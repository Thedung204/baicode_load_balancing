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

# ---------------- Config ----------------
REFERENCE_BW = 10000000
DEFAULT_BW = 10000000
MAX_PATHS = 2
EPS = 1e-6  # avoid divide-by-zero

@dataclass
class Paths:
    path: list
    cost: float

# ---------------- Controller ----------------
class ControllerDijkstra(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        # topology / host state
        self.mac_to_port = {}
        self.neigh = defaultdict(dict)               # neigh[u][v] = port on u toward v
        self.bw = defaultdict(lambda: defaultdict(lambda: DEFAULT_BW))  # bw[dpid][port] = Mbps (estimated)
        self.prev_bytes = defaultdict(lambda: defaultdict(lambda: 0))   # previous tx_bytes
        self.hosts = {}        # hosts[mac] = (dpid, port)
        self.switches = []     # list of dpids
        self.arp_table = {}    # arp_table[ip] = mac
        # path caches
        self.path_table = {}
        self.paths_table = {}
        self.path_with_ports_table = {}
        self.datapath_list = {}        # dpid -> datapath object
        self.path_calculation_keeper = []
        # graph used by Dijkstra
        self.G = nx.DiGraph()

        # --- minimal addition: storage for flow stats (duration, byte_count) ---
        self.flow_stats = {}   # key: (dpid, out_port) -> (duration_sec, byte_count)

        # ---- THÊM DÒNG NÀY (KHÔNG SỬA GÌ KHÁC) ----
        threading.Timer(5.0, self._monitor_flow_stats).start()


    # ---------------- Bandwidth / Graph helpers ----------------
    def get_bandwidth(self, u, v):
        """Return estimated bandwidth (Mbps) for link u->v using the port stored in neigh[u][v]."""
        port = self.neigh[u].get(v)
        if port is None:
            return 0.0
        return self.bw[u].get(port, DEFAULT_BW)

    def update_graph(self):
        """Rebuild directed graph used by Dijkstra.
        weight = 1 / bandwidth (so higher bandwidth => lower cost).
        Also store weight as 'estimated_cost' and a derived 'estimated_latency_ms' for logging.
        """
        self.G.clear()
        for u in self.neigh:
            for v in self.neigh[u]:
                bw = self.get_bandwidth(u, v)
                # if bandwidth is zero or tiny, cost becomes large
                cost = 1.0 / (bw + EPS)

                # ---- CHỈ SỬA CÔNG THỨC LATENCY Ở ĐÂY ----
                # (Removed fallback; only use latency = 100 * (duration / bytecount))
                out_port = self.neigh[u][v]
                key = (u, out_port)

                duration, bytecount = self.flow_stats[key]
                if bytecount == 0:
                    bytecount = 1
                estimated_latency = 100.0 * (float(duration) / float(bytecount))
                # ------------------------------------------

                self.G.add_edge(u, v, weight=cost, estimated_bandwidth_mbps=bw, estimated_cost=cost,
                                estimated_latency_ms=estimated_latency)
        # Debug: print summary of all edges with estimated bandwidth / cost
        edges_summary = []
        for u, v, d in self.G.edges(data=True):
            edges_summary.append(f"{u}->{v} bw={d.get('estimated_bandwidth_mbps'):.2f}Mbps cost={d.get('estimated_cost'):.6f} lat(ms)={d.get('estimated_latency_ms'):.3f}")
        if edges_summary:
            self.logger.info("Graph edges (u->v bw cost lat(ms)): %s", "; ".join(edges_summary))

    def find_best_path(self, src, dst):
        """Run Dijkstra on current graph and return list with one Paths object (to match old API)."""
        self.update_graph()
        try:
            path = nx.dijkstra_path(self.G, src, dst, weight='weight')
            # compute total cost and per-hop cost list
            per_hop = [self.G[u][v]['weight'] for u, v in zip(path[:-1], path[1:])]
            total_cost = sum(per_hop)
            per_hop_lat_ms = [self.G[u][v].get('estimated_latency_ms', w * 1000.0) for u, v, w in zip(path[:-1], path[1:], per_hop)]
            self.logger.info("Best path from %s to %s: %s", src, dst, path)
            self.logger.info("Per-hop estimated_costs: %s", ["{:.6f}".format(x) for x in per_hop])
            self.logger.info("Per-hop estimated_latency_ms: %s", ["{:.3f}".format(x) for x in per_hop_lat_ms])
            self.logger.info("Total estimated_cost: %.6f  (approx. total_latency_ms: %.3f)", total_cost, total_cost * 1000.0)
            return [Paths(path, total_cost)]
        except nx.NetworkXNoPath:
            self.logger.info("No path found from %s to %s", src, dst)
            return []

    def add_ports_to_paths(self, paths, first_port, last_port):
        """Map switches in path to (in_port, out_port) pairs. Returns list of dicts (like original)."""
        paths_n_ports = []
        if not paths:
            return paths_n_ports
        bar = {}
        in_port = first_port
        for s1, s2 in zip(paths[0].path[:-1], paths[0].path[1:]):
            out_port = self.neigh[s1][s2]
            bar[s1] = (in_port, out_port)
            in_port = self.neigh[s2][s1]
        bar[paths[0].path[-1]] = (in_port, last_port)
        paths_n_ports.append(bar)
        self.logger.info("Path with ports mapping: %s", bar)
        return paths_n_ports

    # ---------------- Flow installation ----------------
    def install_paths(self, src, first_port, dst, last_port, ip_src, ip_dst, pkt_type, pkt):
        key = (src, first_port, dst, last_port)
        if key not in self.path_calculation_keeper:
            self.path_calculation_keeper.append(key)
            self.topology_discover(src, first_port, dst, last_port)
            self.topology_discover(dst, last_port, src, first_port)

        # iterate switches on the selected path and install flows
        for node in self.path_table[key][0].path:
            dp = self.datapath_list[node]
            parser = dp.ofproto_parser
            ofp = dp.ofproto
            in_port = self.path_with_ports_table[key][0][node][0]
            out_port = self.path_with_ports_table[key][0][node][1]
            actions = [parser.OFPActionOutput(out_port)]

            match = None
            if pkt_type == 'UDP':
                nw = pkt.get_protocol(ipv4.ipv4)
                l4 = pkt.get_protocol(udp.udp)
                match = parser.OFPMatch(in_port=in_port, eth_type=ether.ETH_TYPE_IP,
                                        ipv4_src=ip_src, ipv4_dst=ip_dst,
                                        ip_proto=17, udp_src=l4.src_port, udp_dst=l4.dst_port)
            elif pkt_type == 'TCP':
                nw = pkt.get_protocol(ipv4.ipv4)
                l4 = pkt.get_protocol(tcp.tcp)
                match = parser.OFPMatch(in_port=in_port, eth_type=ether.ETH_TYPE_IP,
                                        ipv4_src=ip_src, ipv4_dst=ip_dst,
                                        ip_proto=6, tcp_src=l4.src_port, tcp_dst=l4.dst_port)
            elif pkt_type == 'ICMP':
                match = parser.OFPMatch(in_port=in_port, eth_type=ether.ETH_TYPE_IP,
                                        ipv4_src=ip_src, ipv4_dst=ip_dst,
                                        ip_proto=1)
            elif pkt_type == 'ARP':
                match = parser.OFPMatch(in_port=in_port, eth_type=ether.ETH_TYPE_ARP,
                                        arp_spa=ip_src, arp_tpa=ip_dst)

            if match:
                self.logger.info("Installing %s flow on switch %s: in_port=%s out_port=%s", pkt_type, node, in_port, out_port)
                # also log per-link estimated latency for this switch->next hop (if exists)
                # find next hop to show latency
                path = self.path_table[key][0].path
                idx = path.index(node)
                if idx < len(path) - 1:
                    u = node
                    v = path[idx + 1]
                    if self.G.has_edge(u, v):
                        edge = self.G[u][v]
                        self.logger.info("  -> estimated link bw=%.2f Mbps cost=%.6f lat(ms)=%.3f",
                                         edge.get('estimated_bandwidth_mbps', 0.0),
                                         edge.get('estimated_cost', 0.0),
                                         edge.get('estimated_latency_ms', 0.0))
                self.add_flow(dp, 32768, match, actions, 10)
                self.logger.info("%s Flow added!", pkt_type)

        return self.path_with_ports_table[key][0][src][1]

    def add_flow(self, datapath, priority, match, actions, idle_timeout, buffer_id=None):
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS, actions)]
        mod = parser.OFPFlowMod(datapath=datapath, buffer_id=buffer_id or ofproto.OFP_NO_BUFFER,
                                priority=priority, match=match, idle_timeout=idle_timeout, instructions=inst)
        datapath.send_msg(mod)

    # ---------------- Topology discovery ----------------
    def topology_discover(self, src, first_port, dst, last_port):
        threading.Timer(1.0, self.topology_discover, args=(src, first_port, dst, last_port)).start()
        paths = self.find_best_path(src, dst)
        path_with_port = self.add_ports_to_paths(paths, first_port, last_port)
        self.paths_table[(src, first_port, dst, last_port)] = paths
        self.path_table[(src, first_port, dst, last_port)] = paths
        self.path_with_ports_table[(src, first_port, dst, last_port)] = path_with_port

    # ---------------- PacketIn handler ----------------
    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in_handler(self, ev):
        msg = ev.msg
        datapath = msg.datapath
        parser = datapath.ofproto_parser
        ofp = datapath.ofproto
        in_port = msg.match['in_port']

        pkt = packet.Packet(msg.data)
        eth = pkt.get_protocols(ethernet.ethernet)[0]
        if eth.ethertype == ether.ETH_TYPE_LLDP:
            return

        arp_pkt = pkt.get_protocol(arp.arp)
        ip_pkt = pkt.get_protocol(ipv4.ipv4)

        dst = eth.dst
        src = eth.src
        dpid = datapath.id

        if src not in self.hosts:
            self.hosts[src] = (dpid, in_port)

        out_port = ofp.OFPP_FLOOD

        proto = None
        nw = None
        if ip_pkt:
            nw = ip_pkt
            proto = nw.proto

        # UDP
        if eth.ethertype == ether.ETH_TYPE_IP and proto == 17:
            src_ip = nw.src
            dst_ip = nw.dst
            self.arp_table[src_ip] = src
            h1 = self.hosts.get(src)
            h2 = self.hosts.get(dst)
            self.logger.info(" IP Proto UDP from: %s to: %s", src_ip, dst_ip)
            if h1 and h2:
                out_port = self.install_paths(h1[0], h1[1], h2[0], h2[1], src_ip, dst_ip, 'UDP', pkt)
                self.install_paths(h2[0], h2[1], h1[0], h1[1], dst_ip, src_ip, 'UDP', pkt)

    # ---------------- Switch Features ----------------
    @set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER)
    def _switch_features_handler(self, ev):
        datapath = ev.msg.datapath
        parser = datapath.ofproto_parser
        ofp = datapath.ofproto
        match = parser.OFPMatch()
        actions = [parser.OFPActionOutput(ofp.OFPP_CONTROLLER, ofp.OFPCML_NO_BUFFER)]
        self.add_flow(datapath, 0, match, actions, 10)

    # ---------------- Switch / Link events ----------------
    @set_ev_cls(event.EventSwitchEnter)
    def switch_enter_handler(self, ev):
        switch_dp = ev.switch.dp
        switch_dpid = switch_dp.id
        parser = switch_dp.ofproto_parser
        self.logger.info("Switch plugged in: DPID %s", switch_dpid)
        if switch_dpid not in self.switches:
            self.datapath_list[switch_dpid] = switch_dp
            self.switches.append(switch_dpid)
            self.run_check(parser, switch_dp)

    @set_ev_cls(event.EventSwitchLeave, MAIN_DISPATCHER)
    def switch_leave_handler(self, ev):
        switch = ev.switch.dp.id
        if switch in self.switches:
            try:
                self.switches.remove(switch)
                del self.datapath_list[switch]
                del self.neigh[switch]
            except KeyError:
                self.logger.info("Switch %s already removed", switch)

    @set_ev_cls(event.EventLinkAdd, MAIN_DISPATCHER)
    def link_add_handler(self, ev):
        self.neigh[ev.link.src.dpid][ev.link.dst.dpid] = ev.link.src.port_no
        self.neigh[ev.link.dst.dpid][ev.link.src.dpid] = ev.link.dst.port_no
        bw_fwd = self.get_bandwidth(ev.link.src.dpid, ev.link.src.dpid)
        bw_rev = self.get_bandwidth(ev.link.dst.dpid, ev.link.src.dpid)
        cost_fwd = 1.0 / (bw_fwd + EPS)
        cost_rev = 1.0 / (bw_rev + EPS)
        self.logger.info("Link established: %s:%s <-> %s:%s  (est. bw fwd=%.2fMbps cost=%.6f, rev bw=%.2fMbps cost=%.6f)",
                         ev.link.src.dpid, ev.link.src.port_no, ev.link.dst.dpid, ev.link.dst.port_no,
                         bw_fwd, cost_fwd, bw_rev, cost_rev)

    @set_ev_cls(event.EventLinkDelete, MAIN_DISPATCHER)
    def link_delete_handler(self, ev):
        try:
            del self.neigh[ev.link.src.dpid][ev.link.dst.dpid]
            del self.neigh[ev.link.dst.dpid][ev.link.src.dpid]
            self.logger.info("Link removed: %s:%s <-> %s:%s", ev.link.src.dpid, ev.link.src.port_no, ev.link.dst.dpid, ev.link.dst.port_no)
        except KeyError:
            self.logger.info("Link already removed")

    # ---------------- Port stats (bandwidth estimation) ----------------
    @set_ev_cls(ofp_event.EventOFPPortStatsReply, MAIN_DISPATCHER)
    def _port_stats_reply_handler(self, ev):
        switch_dpid = ev.msg.datapath.id
        for p in ev.msg.body:
            # compute Mbps from delta tx_bytes per second (since request every 1s)
            tx_bytes = p.tx_bytes
            prev = self.prev_bytes[switch_dpid][p.port_no]
            bw_mbps = (tx_bytes - prev) * 8.0 / 1000000.0
            # store and update prev
            self.bw[switch_dpid][p.port_no] = bw_mbps
            self.prev_bytes[switch_dpid][p.port_no] = tx_bytes
            self.logger.debug("PortStats: dpid=%s port=%s bw=%.3fMbps", switch_dpid, p.port_no, bw_mbps)

    def run_check(self, parser, dp):
        threading.Timer(1.0, self.run_check, args=(parser, dp)).start()
        req = parser.OFPPortStatsRequest(dp)
        dp.send_msg(req)

    # ======================================================================
    # ===================== FLOW STATS — CODE THÊM VÀO =====================
    # ======================================================================

    def request_flow_stats(self, datapath):
        """Gửi yêu cầu lấy Flow Stats từ switch."""
        parser = datapath.ofproto_parser
        req = parser.OFPFlowStatsRequest(datapath)
        datapath.send_msg(req)

    @set_ev_cls(ofp_event.EventOFPFlowStatsReply, MAIN_DISPATCHER)
    def _flow_stats_reply_handler(self, ev):
        """Nhận Flow Stats."""
        dpid = ev.msg.datapath.id
        self.logger.info("===== FLOW STATS FROM SWITCH %s =====", dpid)

        for stat in ev.msg.body:
            self.logger.info(
                "match=%s  actions=%s  packets=%d  bytes=%d  duration=%ds",
                stat.match,
                stat.instructions,
                stat.packet_count,
                stat.byte_count,
                stat.duration_sec
            )

            # --- Lưu duration và byte_count để dùng tính latency = 100*(duration/byte_count)
            try:
                # try to extract output port from actions if present
                out_port = None
                if stat.instructions and len(stat.instructions) > 0:
                    inst = stat.instructions[0]
                    if hasattr(inst, 'actions') and inst.actions and len(inst.actions) > 0:
                        act = inst.actions[0]
                        if hasattr(act, 'port'):
                            out_port = act.port
                # if we can't determine out_port, skip storing for that flow
                if out_port is not None:
                    duration = int(stat.duration_sec)
                    bytes_count = int(stat.byte_count)
                    if bytes_count == 0:
                        bytes_count = 1
                    self.flow_stats[(dpid, out_port)] = (duration, bytes_count)
            except Exception:
                # don't raise — just continue (we only added minimal storage)
                pass

    def _monitor_flow_stats(self):
        """Gọi lấy flow stats mỗi 5s."""
        threading.Timer(5.0, self._monitor_flow_stats).start()
        for dp in self.datapath_list.values():
            self.request_flow_stats(dp)
