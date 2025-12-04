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

# IP protocol numbers (thay cho inet)
IPPROTO_ICMP = 1
IPPROTO_TCP = 6
IPPROTO_UDP = 17

# --- Cấu hình ---
REFERENCE_BW = 10000000
DEFAULT_BW = 10000000  # giữ nguyên giá trị gốc; khi cần fallback chuyển về Mbps bằng /1000000
MAX_PATHS = 2

@dataclass
class Paths:
    ''' Paths container'''
    path: list
    cost: float

class Controller13(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]

    def __init__(self, *args, **kwargs):
        super(Controller13, self).__init__(*args, **kwargs)
        self.mac_to_port = {}
        self.neigh = defaultdict(dict)
        # self.bw[switch][port] lưu giá trị bandwidth tính theo Mbps (từ stats)
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

    # ---------------- Path cost & bandwidth helpers ----------------
    def get_bandwidth(self, path, port, index):
        """
        Trả về giá trị bandwidth đã đo (Mbps) cho switch path[index] và port.
        Nếu chưa có stats thì trả fallback DEFAULT_BW/1e6 (Mbps).
        """
        sw = path[index]
        return self.bw[sw].get(port, DEFAULT_BW / 1000000.0)

    def find_path_cost(self, path):
        """Tính cost của đường đi: tổng các bandwidth giữa từng cặp nút (giữ giống logic cũ)."""
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
        BFS tìm tất cả đường đi đơn giản (giữ logic gốc BFS nhưng sửa trả Paths đúng kiểu)
        Trả về list[Paths]
        """
        if src == dst:
            return [Paths([src], 0)]
        queue = [(src, [src])]
        possible_paths = list()
        while queue:
            (edge, path) = queue.pop()
            for vertex in set(self.neigh[edge]) - set(path):
                if vertex == dst:
                    path_to_dst = path + [vertex]
                    cost_of_path = self.find_path_cost(path_to_dst)
                    possible_paths.append(Paths(path_to_dst, cost_of_path))
                else:
                    queue.append((vertex, path + [vertex]))
        return possible_paths

    def find_n_optimal_paths(self, paths, number_of_optimal_paths=MAX_PATHS):
        """Chọn n path có cost nhỏ nhất (giữ nguyên logic cũ)."""
        if not paths:
            return []
        costs = [path.cost for path in paths]
        n = min(number_of_optimal_paths, len(costs))
        optimal_paths_indexes = list(map(costs.index, heapq.nsmallest(n, costs)))
        optimal_paths = [paths[op_index] for op_index in optimal_paths_indexes]
        return optimal_paths

    def add_ports_to_paths(self, paths, first_port, last_port):
        """
        Gán cổng (in_port, out_port) cho từng switch dọc theo path.
        paths là list chứa 1 Paths object ở index 0 (giữ cấu trúc cũ).
        Trả về list chứa dict: [{sw1:(in,out), sw2:(in,out), ...}]
        """
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

    # ---------------- Throughput helpers ----------------
    def calculate_path_throughput(self, path_with_ports):
        """
        Tính throughput ước lượng cho 1 path dựa trên bottleneck link.
        path_with_ports: dict mapping {switch: (in_port, out_port)} theo thứ tự path.
        Trả throughput (Mbps).
        """
        if not path_with_ports:
            return 0.0
        bw_list = []
        # Lưu thứ tự switches theo keys hiện tại (được lưu cùng thứ tự khi build)
        path_switches = list(path_with_ports.keys())
        for s1, s2 in zip(path_switches[:-1], path_switches[1:]):
            out_port = path_with_ports[s1][1]
            # fallback về DEFAULT_BW/1e6 nếu chưa có stats cho port đó
            bw = self.bw[s1].get(out_port, DEFAULT_BW / 1000000.0)
            bw_list.append(bw)
        return min(bw_list) if bw_list else 0.0

    def print_bandwidth_stats(self):
        """In băng thông theo switch/port và in throughput ước lượng cho tất cả path đã lưu."""
        self.logger.info("====== Bandwidth Stats ======")
        for sw in sorted(self.switches):
            self.logger.info(f"Switch DPID: {sw}")
            for port, bw in sorted(self.bw[sw].items()):
                prev_bytes = self.prev_bytes[sw].get(port, 0)
                self.logger.info(f"  Port {port}: Bandwidth = {bw:.2f} Mbps, Tx bytes = {prev_bytes}")
        # In throughput cho từng path đã build
        for key, path_ports in self.path_with_ports_table.items():
            # key là (src, first_port, dst, last_port)
            try:
                throughput = self.calculate_path_throughput(path_ports[0])
                self.logger.info(f"[Path Throughput] From switch {key[0]} port {key[1]} -> switch {key[2]} port {key[3]} : {throughput:.2f} Mbps")
            except Exception:
                # tránh lỗi nếu cấu trúc path_ports lạ
                pass
        self.logger.info("============================")

    # ---------------- Install Flows ----------------
    def install_paths(self, src, first_port, dst, last_port, ip_src, ip_dst, type, pkt):
        """
        Cài flow dọc theo đường đã chọn (trong self.path_table và self.path_with_ports_table).
        Sau khi cài xong, in cost và throughput của path.
        """
        if (src, first_port, dst, last_port) not in self.path_calculation_keeper:
            self.path_calculation_keeper.append((src, first_port, dst, last_port))
            self.topology_discover(src, first_port, dst, last_port)
            self.topology_discover(dst, last_port, src, first_port)

        # guard nếu path chưa có (tránh KeyError)
        key = (src, first_port, dst, last_port)
        if key not in self.path_table or key not in self.path_with_ports_table:
            self.logger.info(f"[install_paths] No path found yet for key {key}")
            return None

        for node in self.path_table[key][0].path:
            dp = self.datapath_list[node]
            ofp = dp.ofproto
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
                self.logger.info(f"Installed UDP path in switch: {node} out port: {out_port} in port: {in_port}")
                self.add_flow(dp, 33333, match, actions, 10)

            elif type == 'TCP':
                nw = pkt.get_protocol(ipv4.ipv4)
                l4 = pkt.get_protocol(tcp.tcp)
                match = ofp_parser.OFPMatch(in_port=in_port, eth_type=ether_types.ETH_TYPE_IP,
                                            ipv4_src=ip_src, ipv4_dst=ip_dst,
                                            ip_proto=IPPROTO_TCP,
                                            tcp_src=l4.src_port, tcp_dst=l4.dst_port)
                self.logger.info(f"Installed TCP path in switch: {node} out port: {out_port} in port: {in_port}")
                self.add_flow(dp, 44444, match, actions, 10)

            elif type == 'ICMP':
                nw = pkt.get_protocol(ipv4.ipv4)
                match = ofp_parser.OFPMatch(in_port=in_port, eth_type=ether_types.ETH_TYPE_IP,
                                            ipv4_src=ip_src, ipv4_dst=ip_dst,
                                            ip_proto=IPPROTO_ICMP)
                self.logger.info(f"Installed ICMP path in switch: {node} out port: {out_port} in port: {in_port}")
                self.add_flow(dp, 22222, match, actions, 10)

            elif type == 'ARP':
                match_arp = ofp_parser.OFPMatch(in_port=in_port, eth_type=ether_types.ETH_TYPE_ARP,
                                                arp_spa=ip_src, arp_tpa=ip_dst)
                self.logger.info(f"Installed ARP path in switch: {node} out port: {out_port} in port: {in_port}")
                self.add_flow(dp, 1, match_arp, actions, 10)

        # Tính throughput và in ra
        try:
            path_ports = self.path_with_ports_table[key][0]
            throughput = self.calculate_path_throughput(path_ports)
            cost = self.path_table[key][0].cost
            self.logger.info(f"[RandomRouting/BFS] Path (nodes) = {self.path_table[key][0].path} Cost = {cost}")
            self.logger.info(f"[RandomRouting/BFS] Path throughput estimate = {throughput:.2f} Mbps")
        except Exception as e:
            self.logger.info(f"[install_paths] Could not compute throughput/cost: {e}")

        return self.path_with_ports_table[key][0][src][1]

    def add_flow(self, datapath, priority, match, actions, idle_timeout, buffer_id=None):
        """Gửi OFPFlowMod"""
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser

        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS, actions)]
        if buffer_id:
            mod = parser.OFPFlowMod(datapath=datapath, buffer_id=buffer_id,
                                    priority=priority, match=match, idle_timeout=idle_timeout,
                                    instructions=inst)
        else:
            mod = parser.OFPFlowMod(datapath=datapath, priority=priority,
                                    match=match, idle_timeout=idle_timeout, instructions=inst)
        datapath.send_msg(mod)

    # ---------------- Periodic port stats ----------------
    def run_check(self, ofp_parser, dp):
        """Gửi port stats request định kỳ cho switch dp"""
        threading.Timer(1.0, self.run_check, args=(ofp_parser, dp)).start()
        req = ofp_parser.OFPPortStatsRequest(dp)
        dp.send_msg(req)

    # ---------------- Topology discovery ----------------
    def topology_discover(self, src, first_port, dst, last_port):
        """Cập nhật các path (gọi định kỳ)"""
        threading.Timer(1.0, self.topology_discover, args=(src, first_port, dst, last_port)).start()
        paths = self.find_paths_and_costs(src, dst)
        path = self.find_n_optimal_paths(paths)
        path_with_port = self.add_ports_to_paths(path, first_port, last_port)

        self.logger.info(f"Possible paths: {paths}")
        self.logger.info(f"Optimal Path with port: {path_with_port}")

        self.paths_table[(src, first_port, dst, last_port)] = paths
        self.path_table[(src, first_port, dst, last_port)] = path
        self.path_with_ports_table[(src, first_port, dst, last_port)] = path_with_port

    # ---------------- Ryu event handlers ----------------
    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in_handler(self, ev):
        """Xử lý PacketIn (giữ nguyên logic gốc)"""
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

            self.logger.info(f" IP Proto UDP from: {nw.src} to: {nw.dst}")

            out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip, 'UDP', pkt)
            self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip, 'UDP', pkt)

        elif eth.ethertype == ether_types.ETH_TYPE_IP and nw.proto == IPPROTO_TCP:
            src_ip = nw.src
            dst_ip = nw.dst

            self.arp_table[src_ip] = src
            h1 = self.hosts[src]
            h2 = self.hosts[dst]

            self.logger.info(f" IP Proto TCP from: {nw.src} to: {nw.dst}")

            out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip, 'TCP', pkt)
            self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip, 'TCP', pkt)

        elif eth.ethertype == ether_types.ETH_TYPE_IP and nw.proto == IPPROTO_ICMP:
            src_ip = nw.src
            dst_ip = nw.dst

            self.arp_table[src_ip] = src
            h1 = self.hosts[src]
            h2 = self.hosts[dst]

            self.logger.info(f" IP Proto ICMP from: {nw.src} to: {nw.dst}")

            out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip, 'ICMP', pkt)
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
                self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip, 'ARP', pkt)

            elif arp_pkt.opcode == arp.ARP_REQUEST:
                if dst_ip in self.arp_table:
                    self.arp_table[src_ip] = src
                    dst_mac = self.arp_table[dst_ip]
                    h1 = self.hosts[src]
                    h2 = self.hosts[dst_mac]

                    self.logger.info(f" ARP Reply from: {src_ip} to: {dst_ip} H1: {h1} H2: {h2}")

                    out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip, 'ARP', pkt)
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
        """
        Gửi flow default để forward lên controller (giữ nguyên)
        """
        datapath = ev.msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser

        match = parser.OFPMatch()
        actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER,
                                          ofproto.OFPCML_NO_BUFFER)]
        self.add_flow(datapath, 0, match, actions, 10)

    @set_ev_cls(ofp_event.EventOFPPortStatsReply, MAIN_DISPATCHER)
    def _port_stats_reply_handler(self, ev):
        """Cập nhật self.bw và self.prev_bytes, rồi in stats + throughput cho các path đã lưu."""
        switch_dpid = ev.msg.datapath.id
        for p in ev.msg.body:
            # bw tính bằng Mbps
            self.bw[switch_dpid][p.port_no] = (p.tx_bytes - self.prev_bytes[switch_dpid][p.port_no]) * 8.0 / 1000000.0
            self.prev_bytes[switch_dpid][p.port_no] = p.tx_bytes

        # In băng thông và thông lượng cho tất cả path hiện có
        self.print_bandwidth_stats()

    @set_ev_cls(event.EventSwitchEnter)
    def switch_enter_handler(self, ev):
        """Khi switch kết nối lên controller, lưu datapath và bắt đầu thu stats."""
        switch_dp = ev.switch.dp
        switch_dpid = switch_dp.id
        ofp_parser = switch_dp.ofproto_parser

        self.logger.info(f"Switch has been plugged in PID: {switch_dpid}")

        if switch_dpid not in self.switches:
            self.datapath_list[switch_dpid] = switch_dp
            self.switches.append(switch_dpid)
            # Bắt đầu gửi port stats request định kỳ
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
        """Ghi nhận link (neigh) khi topology thay đổi."""
        self.neigh[ev.link.src.dpid][ev.link.dst.dpid] = ev.link.src.port_no
        self.neigh[ev.link.dst.dpid][ev.link.src.dpid] = ev.link.dst.port_no
        self.logger.info(f"Link between switches has been established, SW1 DPID: {ev.link.src.dpid}:{ev.link.src.port_no} SW2 DPID: {ev.link.dst.dpid}:{ev.link.dst.port_no}")

    @set_ev_cls(event.EventLinkDelete, MAIN_DISPATCHER)
    def link_delete_handler(self, ev):
        try:
            del self.neigh[ev.link.src.dpid][ev.link.dst.dpid]
            del self.neigh[ev.link.dst.dpid][ev.link.src.dpid]
        except KeyError:
            self.logger.info("Link has been already pluged off!")
            pass
