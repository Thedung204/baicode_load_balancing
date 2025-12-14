#!/usr/bin/python3

from ryu.base import app_manager
from ryu.controller import ofp_event
from ryu.controller.handler import MAIN_DISPATCHER, CONFIG_DISPATCHER, set_ev_cls
from ryu.lib.packet import packet, ethernet, arp, ipv4, udp, tcp
from ryu.ofproto import ether, ofproto_v1_3
from ryu.topology import event
import threading
from collections import defaultdict
from dataclasses import dataclass
import networkx as nx
import time

# ---------------- Config ----------------
REFERENCE_BW = 10000000
DEFAULT_BW = 10000000
MAX_PATHS = 2
EPS = 1e-6

@dataclass
class Paths:
    path: list
    cost: float

# ---------------- Controller ----------------
class ControllerDijkstra(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

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

        self.G = nx.DiGraph()

        self.flow_stats = {}
        self.link_latency = defaultdict(lambda: defaultdict(lambda: 0.0))

        # ================= THROUGHPUT STORAGE (ADDED ONLY) =================
        # key: (dpid, out_port) -> (prev_bytes, prev_time, throughput_mbps)
        self.flow_throughput = {}

        threading.Timer(5.0, self._monitor_flow_stats).start()

    # ---------------- Bandwidth / Graph helpers ----------------
    def get_bandwidth(self, u, v):
        port = self.neigh[u].get(v)
        if port is None:
            return 0.0
        return self.bw[u].get(port, DEFAULT_BW)

    def update_graph(self):
        self.G.clear()
        for u in self.neigh:
            for v in self.neigh[u]:
                bw = self.get_bandwidth(u, v)
                cost = 1.0 / (bw + EPS)

                out_port = self.neigh[u][v]
                duration, bytecount = self.flow_stats.get((u, out_port), (0, 1))
                if bytecount == 0:
                    bytecount = 1
                est_switch_ms = 100.0 * (float(duration) / float(bytecount))
                lldp_ms = float(self.link_latency[u].get(v, 0.0))

                self.G.add_edge(
                    u, v,
                    weight=cost,
                    estimated_bandwidth_mbps=bw,
                    estimated_cost=cost,
                    estimated_latency_ms=est_switch_ms + lldp_ms
                )

    def find_best_path(self, src, dst):
        self.update_graph()
        try:
            path = nx.dijkstra_path(self.G, src, dst, weight='weight')
            cost = sum(self.G[u][v]['weight'] for u, v in zip(path[:-1], path[1:]))
            return [Paths(path, cost)]
        except nx.NetworkXNoPath:
            return []

    def add_ports_to_paths(self, paths, first_port, last_port):
        res = []
        if not paths:
            return res
        bar = {}
        in_port = first_port
        for s1, s2 in zip(paths[0].path[:-1], paths[0].path[1:]):
            out_port = self.neigh[s1][s2]
            bar[s1] = (in_port, out_port)
            in_port = self.neigh[s2][s1]
        bar[paths[0].path[-1]] = (in_port, last_port)
        res.append(bar)
        return res

    # ---------------- Flow install ----------------
    def install_paths(self, src, first_port, dst, last_port, ip_src, ip_dst, pkt_type, pkt):
        key = (src, first_port, dst, last_port)
        if key not in self.path_calculation_keeper:
            self.path_calculation_keeper.append(key)
            self.topology_discover(src, first_port, dst, last_port)
            self.topology_discover(dst, last_port, src, first_port)

        for node in self.path_table[key][0].path:
            dp = self.datapath_list[node]
            parser = dp.ofproto_parser
            ofp = dp.ofproto

            in_port, out_port = self.path_with_ports_table[key][0][node]
            actions = [parser.OFPActionOutput(out_port)]

            if pkt_type == 'UDP':
                nw = pkt.get_protocol(ipv4.ipv4)
                l4 = pkt.get_protocol(udp.udp)
                match = parser.OFPMatch(
                    in_port=in_port, eth_type=ether.ETH_TYPE_IP,
                    ipv4_src=ip_src, ipv4_dst=ip_dst,
                    ip_proto=17, udp_src=l4.src_port, udp_dst=l4.dst_port)
            elif pkt_type == 'TCP':
                nw = pkt.get_protocol(ipv4.ipv4)
                l4 = pkt.get_protocol(tcp.tcp)
                match = parser.OFPMatch(
                    in_port=in_port, eth_type=ether.ETH_TYPE_IP,
                    ipv4_src=ip_src, ipv4_dst=ip_dst,
                    ip_proto=6, tcp_src=l4.src_port, tcp_dst=l4.dst_port)
            elif pkt_type == 'ICMP':
                match = parser.OFPMatch(
                    in_port=in_port, eth_type=ether.ETH_TYPE_IP,
                    ipv4_src=ip_src, ipv4_dst=ip_dst, ip_proto=1)
            else:
                match = parser.OFPMatch(
                    in_port=in_port, eth_type=ether.ETH_TYPE_ARP,
                    arp_spa=ip_src, arp_tpa=ip_dst)

            self.add_flow(dp, 32768, match, actions, 10)

        return self.path_with_ports_table[key][0][src][1]

    def add_flow(self, datapath, priority, match, actions, idle_timeout):
        parser = datapath.ofproto_parser
        ofp = datapath.ofproto
        inst = [parser.OFPInstructionActions(ofp.OFPIT_APPLY_ACTIONS, actions)]
        mod = parser.OFPFlowMod(
            datapath=datapath,
            priority=priority,
            match=match,
            idle_timeout=idle_timeout,
            instructions=inst)
        datapath.send_msg(mod)

    # ---------------- Topology ----------------
    def topology_discover(self, src, first_port, dst, last_port):
        threading.Timer(1.0, self.topology_discover,
                        args=(src, first_port, dst, last_port)).start()
        paths = self.find_best_path(src, dst)
        self.path_table[(src, first_port, dst, last_port)] = paths
        self.path_with_ports_table[(src, first_port, dst, last_port)] = \
            self.add_ports_to_paths(paths, first_port, last_port)

    # ---------------- PacketIn ----------------
    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in_handler(self, ev):
        msg = ev.msg
        dp = msg.datapath
        parser = dp.ofproto_parser
        ofp = dp.ofproto
        in_port = msg.match['in_port']

        pkt = packet.Packet(msg.data)
        eth = pkt.get_protocols(ethernet.ethernet)[0]
        if eth.ethertype == ether.ETH_TYPE_LLDP:
            return

        src = eth.src
        dst = eth.dst
        dpid = dp.id

        if src not in self.hosts:
            self.hosts[src] = (dpid, in_port)

        out_port = ofp.OFPP_FLOOD
        ip_pkt = pkt.get_protocol(ipv4.ipv4)

        if ip_pkt:
            proto = ip_pkt.proto
            h1 = self.hosts.get(src)
            h2 = self.hosts.get(dst)
            if h1 and h2:
                if proto == 17:
                    out_port = self.install_paths(*h1, *h2, ip_pkt.src, ip_pkt.dst, 'UDP', pkt)
                elif proto == 6:
                    out_port = self.install_paths(*h1, *h2, ip_pkt.src, ip_pkt.dst, 'TCP', pkt)
                elif proto == 1:
                    out_port = self.install_paths(*h1, *h2, ip_pkt.src, ip_pkt.dst, 'ICMP', pkt)

        actions = [parser.OFPActionOutput(out_port)]
        dp.send_msg(parser.OFPPacketOut(
            datapath=dp,
            buffer_id=msg.buffer_id,
            in_port=in_port,
            actions=actions,
            data=msg.data))

    # ---------------- Switch / Link events ----------------
    @set_ev_cls(event.EventSwitchEnter)
    def switch_enter_handler(self, ev):
        dp = ev.switch.dp
        self.datapath_list[dp.id] = dp
        self.switches.append(dp.id)
        self.run_check(dp.ofproto_parser, dp)

    @set_ev_cls(event.EventLinkAdd)
    def link_add_handler(self, ev):
        self.neigh[ev.link.src.dpid][ev.link.dst.dpid] = ev.link.src.port_no
        self.neigh[ev.link.dst.dpid][ev.link.src.dpid] = ev.link.dst.port_no

    # ---------------- Port stats ----------------
    @set_ev_cls(ofp_event.EventOFPPortStatsReply, MAIN_DISPATCHER)
    def _port_stats_reply_handler(self, ev):
        dpid = ev.msg.datapath.id
        for p in ev.msg.body:
            tx = p.tx_bytes
            prev = self.prev_bytes[dpid][p.port_no]
            self.bw[dpid][p.port_no] = (tx - prev) * 8.0 / 1e6
            self.prev_bytes[dpid][p.port_no] = tx

    def run_check(self, parser, dp):
        threading.Timer(1.0, self.run_check, args=(parser, dp)).start()
        dp.send_msg(parser.OFPPortStatsRequest(dp))

    # ================= FLOW STATS + THROUGHPUT =================
    def request_flow_stats(self, dp):
        dp.send_msg(dp.ofproto_parser.OFPFlowStatsRequest(dp))

    @set_ev_cls(ofp_event.EventOFPFlowStatsReply, MAIN_DISPATCHER)
    def _flow_stats_reply_handler(self, ev):
        dpid = ev.msg.datapath.id
        now = time.time()

        for stat in ev.msg.body:
            out_port = None
            for inst in getattr(stat, 'instructions', []):
                for act in getattr(inst, 'actions', []):
                    if hasattr(act, 'port'):
                        out_port = act.port
                        break
            if out_port is None:
                continue

            duration = int(stat.duration_sec)
            bytes_cnt = int(stat.byte_count) or 1
            self.flow_stats[(dpid, out_port)] = (duration, bytes_cnt)

            key = (dpid, out_port)
            if key in self.flow_throughput:
                prev_b, prev_t, _ = self.flow_throughput[key]
                delta_b = bytes_cnt - prev_b
                delta_t = now - prev_t
                thr = (delta_b * 8.0) / (delta_t * 1e6) if delta_t > 0 else 0.0
            else:
                thr = 0.0

            self.flow_throughput[key] = (bytes_cnt, now, thr)

    def _monitor_flow_stats(self):
        threading.Timer(5.0, self._monitor_flow_stats).start()
        for dp in self.datapath_list.values():
            self.request_flow_stats(dp)

        self.logger.info("===== THROUGHPUT REPORT (Mbps) =====")
        for (dpid, port), (_, _, thr) in self.flow_throughput.items():
            self.logger.info("Switch %s port %s : %.3f Mbps", dpid, port, thr)
