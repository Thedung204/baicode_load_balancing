#!/usr/bin/python3

from import_multipath import *
import random
import threading
from collections import defaultdict
from dataclasses import dataclass
import heapq
from ryu.base import app_manager
from ryu.controller import ofp_event
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER, set_ev_cls
from ryu.lib.packet import packet, ethernet, arp, ipv4, tcp, udp, ether_types
from ryu.ofproto import ofproto_v1_3
from ryu.topology import event

# IP protocol numbers thay cho 'inet'
IPPROTO_ICMP = 1
IPPROTO_TCP = 6
IPPROTO_UDP = 17

REFERENCE_BW = 10000000
DEFAULT_BW = 10000000
MAX_PATHS = 2

@dataclass
class Paths:
    ''' Paths container'''
    path: list
    cost: float

class RandomRoutingController(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]

    def __init__(self, *args, **kwargs):
        super(RandomRoutingController, self).__init__(*args, **kwargs)
        self.mac_to_port = {}
        self.neigh = defaultdict(dict)
        self.bw = defaultdict(lambda: defaultdict(lambda: DEFAULT_BW))
        self.prev_bytes = defaultdict(lambda: defaultdict(lambda: 0))
        self.hosts = {}
        self.switches = []
        self.arp_table = {}
        self.path_table = {}
        self.paths_table = {}
        self.path_with_ports_table = {}
        self.datapath_list = {}
        self.path_calculation_keeper = []

    # ---------------- path cost & bw ----------------
    def get_bandwidth(self, path, port, index):
        # trả về băng thông (Mbps) hiện tại cho switch path[index] port `port`
        return self.bw[path[index]][port]

    def find_path_cost(self, path):
        ''' arg path is a list with all nodes in our route '''
        path_cost = []
        i = 0
        while i < len(path) - 1:
            port1 = self.neigh[path[i]][path[i + 1]]
            bandwidth_between_two_nodes = self.get_bandwidth(path, port1, i)
            path_cost.append(bandwidth_between_two_nodes)
            i += 1
        return sum(path_cost)

    def find_paths_and_costs(self, src, dst):
        """
        Tìm tất cả đường đi đơn giản từ src -> dst bằng DFS (với random hóa thứ tự)
        Trả về list của Paths(path, cost)
        """
        if src == dst:
            return [Paths([src], 0)]

        possible_paths = []
        stack = [(src, [src])]

        while stack:
            node, path = stack.pop()
            if node == dst:
                cost_of_path = self.find_path_cost(path)
                possible_paths.append(Paths(list(path), cost_of_path))
                continue
            neighbors = list(set(self.neigh[node]) - set(path))
            # random hóa thứ tự để mỗi lần khám phá sẽ khác nhau (random routing flavor)
            random.shuffle(neighbors)
            for v in neighbors:
                stack.append((v, path + [v]))

        return possible_paths

    def find_n_optimal_paths(self, paths, number_of_optimal_paths=MAX_PATHS):
        '''Chọn n path có cost nhỏ nhất (giữ để so sánh)'''
        if not paths:
            return []
        costs = [p.cost for p in paths]
        n = min(number_of_optimal_paths, len(costs))
        optimal_indexes = list(map(costs.index, heapq.nsmallest(n, costs)))
        optimal_paths = [paths[i] for i in optimal_indexes]
        return optimal_paths

    def add_ports_to_paths(self, paths, first_port, last_port):
        '''
        Add the ports to all switches including hosts
        paths: list-like with at least one Paths object (we use paths[0])
        '''
        paths_n_ports = list()
        bar = dict()
        in_port = first_port
        for s1, s2 in zip(paths[0].path[:-1], paths[0].path[1:]):
            out_port = self.neigh[s1][s2]
            bar[s1] = (in_port, out_port)
            in_port = self.neigh[s2][s1]
        bar[paths[0].path[-1]] = (in_port, last_port)
        paths_n_ports.append(bar)
        return paths_n_ports

    # --------- throughput helpers ----------
    def calculate_path_throughput(self, path_with_ports):
        """
        Tính throughput ước lượng của path: bottleneck link (Mbps)
        path_with_ports: dict (switch -> (in_port, out_port))
        """
        bw_list = []
        path = list(path_with_ports.keys())
        for s1, s2 in zip(path[:-1], path[1:]):
            out_port = path_with_ports[s1][1]
            # self.bw lưu Mbps
            bw = self.bw[s1].get(out_port, DEFAULT_BW / 1000000.0)
            bw_list.append(bw)
        return min(bw_list) if bw_list else 0.0

    def print_bandwidth_stats(self):
        self.logger.info("====== Bandwidth Stats (Mbps) ======")
        for sw in self.switches:
            self.logger.info(f"Switch DPID: {sw}")
            for port, bw in sorted(self.bw[sw].items()):
                prev_bytes = self.prev_bytes[sw][port]
                self.logger.info(f"  Port {port}: Bandwidth = {bw:.3f} Mbps, Tx bytes = {prev_bytes}")
        self.logger.info("===================================")

    # ---------------- install flows ----------------
    def install_paths(self, src, first_port, dst, last_port, ip_src, ip_dst, type, pkt):
        # ensure we discovered path at least once
        if (src, first_port, dst, last_port) not in self.path_calculation_keeper:
            self.path_calculation_keeper.append((src, first_port, dst, last_port))
            # kick topology discovery once for both directions
            self.topology_discover(src, first_port, dst, last_port)
            self.topology_discover(dst, last_port, src, first_port)

        key = (src, first_port, dst, last_port)
        if key not in self.path_table or key not in self.path_with_ports_table:
            self.logger.info(f"[RandomRouting] No path found yet for {key}")
            return None

        # cài flow cho từng switch trên path
        for node in self.path_table[key][0].path:
            dp = self.datapath_list[node]
            ofp_parser = dp.ofproto_parser

            in_port = self.path_with_ports_table[key][0][node][0]
            out_port = self.path_with_ports_table[key][0][node][1]

            actions = [ofp_parser.OFPActionOutput(out_port)]

            if type == 'UDP':
                nw = pkt.get_protocol(ipv4.ipv4)
                l4 = pkt.get_protocol(udp.udp)
                match = ofp_parser.OFPMatch(in_port=in_port, eth_type=ether_types.ETH_TYPE_IP,
                                            ipv4_src=ip_src, ipv4_dst=ip_dst,
                                            ip_proto=IPPROTO_UDP,
                                            udp_src=l4.src_port, udp_dst=l4.dst_port)
                self.add_flow(dp, 33333, match, actions, 10)
                self.logger.info(f"UDP Flow added on switch {node} in:{in_port} out:{out_port}")

            elif type == 'TCP':
                nw = pkt.get_protocol(ipv4.ipv4)
                l4 = pkt.get_protocol(tcp.tcp)
                match = ofp_parser.OFPMatch(in_port=in_port, eth_type=ether_types.ETH_TYPE_IP,
                                            ipv4_src=ip_src, ipv4_dst=ip_dst,
                                            ip_proto=IPPROTO_TCP,
                                            tcp_src=l4.src_port, tcp_dst=l4.dst_port)
                self.add_flow(dp, 44444, match, actions, 10)
                self.logger.info(f"TCP Flow added on switch {node} in:{in_port} out:{out_port}")

            elif type == 'ICMP':
                nw = pkt.get_protocol(ipv4.ipv4)
                match = ofp_parser.OFPMatch(in_port=in_port, eth_type=ether_types.ETH_TYPE_IP,
                                            ipv4_src=ip_src, ipv4_dst=ip_dst,
                                            ip_proto=IPPROTO_ICMP)
                self.add_flow(dp, 22222, match, actions, 10)
                self.logger.info(f"ICMP Flow added on switch {node} in:{in_port} out:{out_port}")

            elif type == 'ARP':
                match_arp = ofp_parser.OFPMatch(in_port=in_port, eth_type=ether_types.ETH_TYPE_ARP,
                                                arp_spa=ip_src, arp_tpa=ip_dst)
                self.add_flow(dp, 1, match_arp, actions, 10)
                self.logger.info(f"ARP Flow added on switch {node} in:{in_port} out:{out_port}")

        # in cost và estimate throughput
        path_obj = self.path_table[key][0]
        path_ports = self.path_with_ports_table[key][0]
        throughput = self.calculate_path_throughput(path_ports)
        self.logger.info(f"[RandomRouting] Installed path {path_obj.path} Cost: {path_obj.cost}")
        self.logger.info(f"[RandomRouting] Path throughput estimate: {throughput:.3f} Mbps")

        # trả về port tại src để gửi packet out
        return self.path_with_ports_table[key][0][src][1]

    # ---------------- ryu helpers ----------------
    def add_flow(self, datapath, priority, match, actions, idle_timeout, buffer_id=None):
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS,
                                             actions)]
        if buffer_id:
            mod = parser.OFPFlowMod(datapath=datapath, buffer_id=buffer_id,
                                    priority=priority, match=match, idle_timeout=idle_timeout,
                                    instructions=inst)
        else:
            mod = parser.OFPFlowMod(datapath=datapath, priority=priority,
                                    match=match, idle_timeout=idle_timeout, instructions=inst)
        datapath.send_msg(mod)

    def run_check(self, ofp_parser, dp):
        # gọi định kỳ mỗi 1s để request port stats
        threading.Timer(1.0, self.run_check, args=(ofp_parser, dp)).start()
        req = ofp_parser.OFPPortStatsRequest(dp)
        dp.send_msg(req)

    # ---------------- topology discovery (random) ----------------
    def topology_discover(self, src, first_port, dst, last_port):
        # chạy lại định kỳ (giống code gốc)
        threading.Timer(1.0, self.topology_discover, args=(src, first_port, dst, last_port)).start()
        # tìm tất cả đường đi (randomized DFS), chọn 1 ngẫu nhiên rồi vẫn lưu cost để so sánh
        possible_paths = self.find_paths_and_costs(src, dst)
        if not possible_paths:
            # không tìm được path
            return
        # chọn 1 random path (thay cho find_n_optimal_paths ở code gốc)
        chosen = [random.choice(possible_paths)]
        path_with_port = self.add_ports_to_paths(chosen, first_port, last_port)
        self.paths_table[(src, first_port, dst, last_port)] = possible_paths
        self.path_table[(src, first_port, dst, last_port)] = chosen
        self.path_with_ports_table[(src, first_port, dst, last_port)] = path_with_port

        self.logger.info(f"[RandomRouting] Possible paths count: {len(possible_paths)}")
        self.logger.info(f"[RandomRouting] Chosen path: {chosen[0].path} Cost: {chosen[0].cost}")
        self.logger.info(f"[RandomRouting] Path with ports: {path_with_port}")

    # ---------------- Ryu event handlers ----------------
    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in_handler(self, ev):
        # giống code gốc: xử lý PacketIn, phân loại ARP/IP/TCP/UDP/ICMP và gọi install_paths
        if ev.msg.msg_len < ev.msg.total_len:
            self.logger.debug("packet truncated: only %s of %s bytes", ev.msg.msg_len, ev.msg.total_len)
        msg = ev.msg
        datapath = msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        in_port = msg.match['in_port']

        pkt = packet.Packet(msg.data)
        eth = pkt.get_protocols(ethernet.ethernet)[0]
        arp_pkt = pkt.get_protocol(arp.arp)
        ip_pkt = pkt.get_protocol(ipv4.ipv4)

        if eth.ethertype == ether_types.ETH_TYPE_LLDP:
            return

        dst = eth.dst
        src = eth.src
        dpid = datapath.id

        if src not in self.hosts:
            self.hosts[src] = (dpid, in_port)

        out_port = ofproto.OFPP_FLOOD

        if eth.ethertype == ether_types.ETH_TYPE_IP:
            nw = pkt.get_protocol(ipv4.ipv4)
            if nw.proto == IPPROTO_UDP:
                l4 = pkt.get_protocol(udp.udp)
            elif nw.proto == IPPROTO_TCP:
                l4 = pkt.get_protocol(tcp.tcp)

        if eth.ethertype == ether_types.ETH_TYPE_IP and nw.proto == IPPROTO_UDP:
            src_ip = nw.src
            dst_ip = nw.dst
            self.arp_table[src_ip] = src
            h1 = self.hosts[src]
            h2 = self.hosts[dst]
            self.logger.info(f" IP Proto UDP from: {src_ip} to: {dst_ip}")
            out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip, 'UDP', pkt)
            if out_port is None:
                out_port = ofproto.OFPP_FLOOD
            self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip, 'UDP', pkt)

        elif eth.ethertype == ether_types.ETH_TYPE_IP and nw.proto == IPPROTO_TCP:
            src_ip = nw.src
            dst_ip = nw.dst
            self.arp_table[src_ip] = src
            h1 = self.hosts[src]
            h2 = self.hosts[dst]
            self.logger.info(f" IP Proto TCP from: {src_ip} to: {dst_ip}")
            out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip, 'TCP', pkt)
            if out_port is None:
                out_port = ofproto.OFPP_FLOOD
            self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip, 'TCP', pkt)

        elif eth.ethertype == ether_types.ETH_TYPE_IP and nw.proto == IPPROTO_ICMP:
            src_ip = nw.src
            dst_ip = nw.dst
            self.arp_table[src_ip] = src
            h1 = self.hosts[src]
            h2 = self.hosts[dst]
            self.logger.info(f" IP Proto ICMP from: {src_ip} to: {dst_ip}")
            out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip, 'ICMP', pkt)
            if out_port is None:
                out_port = ofproto.OFPP_FLOOD
            self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip, 'ICMP', pkt)

        elif eth.ethertype == ether_types.ETH_TYPE_ARP:
            src_ip = arp_pkt.src_ip
            dst_ip = arp_pkt.dst_ip
            if arp_pkt.opcode == arp.ARP_REPLY:
                self.arp_table[src_ip] = src
                h1 = self.hosts[src]
                h2 = self.hosts[dst]
                self.logger.info(f" ARP Reply from: {src_ip} to: {dst_ip} H1: {h1} H2: {h2}")
                out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip, 'ARP', pkt)
                if out_port is None:
                    out_port = ofproto.OFPP_FLOOD
                self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip, 'ARP', pkt)

            elif arp_pkt.opcode == arp.ARP_REQUEST:
                if dst_ip in self.arp_table:
                    self.arp_table[src_ip] = src
                    dst_mac = self.arp_table[dst_ip]
                    h1 = self.hosts[src]
                    h2 = self.hosts[dst_mac]
                    self.logger.info(f" ARP Reply from: {src_ip} to: {dst_ip} H1: {h1} H2: {h2}")
                    out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip, 'ARP', pkt)
                    if out_port is None:
                        out_port = ofproto.OFPP_FLOOD
                    self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip, 'ARP', pkt)

        actions = [parser.OFPActionOutput(out_port)]
        data = None
        if msg.buffer_id == ofproto.OFP_NO_BUFFER:
            data = msg.data
        out = parser.OFPPacketOut(datapath=datapath, buffer_id=msg.buffer_id,
                                  in_port=in_port, actions=actions, data=data)
        datapath.send_msg(out)

    @set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER)
    def _switch_features_handler(self, ev):
        datapath = ev.msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        match = parser.OFPMatch()
        actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER,
                                          ofproto.OFPCML_NO_BUFFER)]
        self.add_flow(datapath, 0, match, actions, 10)

    @set_ev_cls(ofp_event.EventOFPPortStatsReply, MAIN_DISPATCHER)
    def _port_stats_reply_handler(self, ev):
        '''Reply to the OFPPortStatsRequest, update bw and print per-path throughput'''
        switch_dpid = ev.msg.datapath.id
        for p in ev.msg.body:
            # compute Mbps = delta bytes * 8 / 1e6, same as bạn dùng
            self.bw[switch_dpid][p.port_no] = (p.tx_bytes - self.prev_bytes[switch_dpid][p.port_no]) * 8.0 / 1000000.0
            self.prev_bytes[switch_dpid][p.port_no] = p.tx_bytes

        # in bandwidth per switch/port
        self.print_bandwidth_stats()

        # in throughput estimate cho mọi path đã lưu
        for key, path_ports in self.path_with_ports_table.items():
            # path_ports is list with one dict at index 0 (keeps original format)
            throughput = self.calculate_path_throughput(path_ports[0])
            src = key[0]; dst = key[2]
            self.logger.info(f"[PathThroughput] {src} -> {dst} : {throughput:.3f} Mbps")

    @set_ev_cls(event.EventSwitchEnter)
    def switch_enter_handler(self, ev):
        switch_dp = ev.switch.dp
        switch_dpid = switch_dp.id
        ofp_parser = switch_dp.ofproto_parser
        self.logger.info(f"Switch has been plugged in PID: {switch_dpid}")

        if switch_dpid not in self.switches:
            self.datapath_list[switch_dpid] = switch_dp
            self.switches.append(switch_dpid)
            # start periodic stats request for this switch
            self.run_check(ofp_parser, switch_dp)

    @set_ev_cls(event.EventSwitchLeave, MAIN_DISPATCHER)
    def switch_leave_handler(self, ev):
        switch = ev.switch.dp.id
        if switch in self.switches:
            try:
                self.switches.remove(switch)
                del self.datapath_list[switch]
                del self.neigh[switch]
            except KeyError:
                self.logger.info(f"Switch has been already pulged off PID{switch}!")

    @set_ev_cls(event.EventLinkAdd, MAIN_DISPATCHER)
    def link_add_handler(self, ev):
        # cập nhật neigh như code gốc
        self.neigh[ev.link.src.dpid][ev.link.dst.dpid] = ev.link.src.port_no
        self.neigh[ev.link.dst.dpid][ev.link.src.dpid] = ev.link.dst.port_no
        self.logger.info(f"Link added: {ev.link.src.dpid}:{ev.link.src.port_no} <-> {ev.link.dst.dpid}:{ev.link.dst.port_no}")

    @set_ev_cls(event.EventLinkDelete, MAIN_DISPATCHER)
    def link_delete_handler(self, ev):
        try:
            del self.neigh[ev.link.src.dpid][ev.link.dst.dpid]
            del self.neigh[ev.link.dst.dpid][ev.link.src.dpid]
        except KeyError:
            self.logger.info("Link has been already pluged off!")
            pass
