"""Exact integer graph, feasible flow and matching cut for the shared first3-root relaxation."""
from collections import Counter, deque
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import gcd, lcm, prod
from pathlib import Path
import importlib.util
import json
import sys
import time
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
_spec=importlib.util.spec_from_file_location('shared_root_io',Path(__file__).with_name('adaptive_phase_io.py'))
_io=importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_io)
require=_io.require

CERTIFICATE='certificates/source_norms/source-budgets/shared_first3_root_cut.json'
SOURCES=('certificate_io.py', 'frontier/source-budgets/adaptive_phase_io.py', 'problem-details/67-shared-root-prefix-bounds-for-the-actual-survivor-law.md', 'problem-details/65-independent-survivor-marginal-ceiling-at-the-fixed-cutoff.md', 'frontier/source-budgets/uniform_phase_capacity_input.json', 'certificates/source_norms/source-budgets/shared_first3_root_queries.json', 'frontier/source-budgets/shared_first3_root_queries.py', 'certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json', 'frontier/source-budgets/survivor_cylinder_ceiling.py', 'certificates/source_norms/source-budgets/square_stoploss_curve.json', 'frontier/source-budgets/square_stoploss_curve.py', 'certificates/source_norms/source-budgets/expanded_stop_budget.json', 'frontier/source-budgets/expanded_stop_budget.py')

def calculate(base):
    ctx=_io.Context(base,SOURCES,__file__)
    query=ctx.fresh('certificates/source_norms/source-budgets/shared_first3_root_queries.json','frontier/source-budgets/shared_first3_root_queries.py')
    ceiling=ctx.fresh('certificates/source_norms/source-budgets/survivor_cylinder_ceiling.json','frontier/source-budgets/survivor_cylinder_ceiling.py')
    curve=ctx.fresh('certificates/source_norms/source-budgets/square_stoploss_curve.json','frontier/source-budgets/square_stoploss_curve.py')
    budget=ctx.fresh('certificates/source_norms/source-budgets/expanded_stop_budget.json','frontier/source-budgets/expanded_stop_budget.py')
    data={'query':query,'input':ctx.read('frontier/source-budgets/uniform_phase_capacity_input.json'),'hybrid':ceiling['hybrid'],'threshold':ceiling['thresholds'],'curve':curve}
    START=time.monotonic()
    Q = data['query']
    require(Q['status'] == 'PASS', "Exact shared-root certificate: Q['status'] == 'PASS'")
    D = int(Q['common_denominator'])
    B = {}
    for row in Q['records']:
        f = list(map(F, row['restricted_upper']))
        require(f[0] == 0 and all(((x * D).denominator == 1 for x in f)), 'Exact shared-root certificate: f[0] == 0 and all(((x * D).denominator == 1 for x in f))')
        B[row['modulus']] = [int(x * D) for x in f[1:]]
    mods = [m for m, a in data['input']['labels']]
    vars = sorted((m for m in mods if m % 3 == 0))
    others = [m for m in mods if m % 3]
    N = len(vars)
    require(N == 66 and len(others) == 88, 'Exact shared-root certificate: N == 66 and len(others) == 88')
    unary = [[3 * B[d][r] + 2 * sum((B[lcm(d, e)][r] for e in others)) for r in range(2)] for d in vars]
    pair = [(i, j, 2 * B[lcm(vars[i], vars[j])][0], 2 * B[lcm(vars[i], vars[j])][1]) for i, j in combinations(range(N), 2)]
    old = 3 * sum((max(B[d]) for d in vars)) + 2 * sum((max(B[lcm(d, e)]) for d in vars for e in others)) + sum((max(w0, w1) for i, j, w0, w1 in pair))
    C = sum((u[0] for u in unary)) + sum((w0 for i, j, w0, w1 in pair))
    a = [u[1] - u[0] for u in unary]
    for i, j, w0, w1 in pair:
        require((w0 + w1) % 2 == 0 and (w1 - w0) % 2 == 0, 'Exact shared-root certificate: (w0 + w1) % 2 == 0 and (w1 - w0) % 2 == 0')
        a[i] += (w1 - w0) // 2
        a[j] += (w1 - w0) // 2
    constant = C + sum((max(0, x) for x in a))
    source = N
    sink = N + 1
    graph = [[] for _ in range(N + 2)]
    original = []

    def edge(u, v, c):
        require(c >= 0, 'Exact shared-root certificate: c >= 0')
        if not c:
            return
        iu = len(graph[u])
        iv = len(graph[v])
        graph[u].append([v, iv, c])
        graph[v].append([u, iu, 0])
        original.append((u, v, c, iu))
    for i, coef in enumerate(a):
        edge(source, i, max(-coef, 0))
        edge(i, sink, max(coef, 0))
    for i, j, w0, w1 in pair:
        cap = (w0 + w1) // 2
        edge(i, j, cap)
        edge(j, i, cap)
    flow = 0
    INF = sum((c for u, v, c, k in original)) + 1
    while True:
        level = [-1] * (N + 2)
        level[source] = 0
        q = deque([source])
        while q:
            u = q.popleft()
            for v, rev, c in graph[u]:
                if c and level[v] < 0:
                    level[v] = level[u] + 1
                    q.append(v)
        if level[sink] < 0:
            break
        it = [0] * (N + 2)

        def dfs(u, amount):
            if u == sink:
                return amount
            while it[u] < len(graph[u]):
                item = graph[u][it[u]]
                v, rev, cap = item
                if cap and level[v] == level[u] + 1:
                    sent = dfs(v, min(amount, cap))
                    if sent:
                        item[2] -= sent
                        graph[v][rev][2] += sent
                        return sent
                it[u] += 1
            return 0
        while True:
            sent = dfs(source, INF)
            if not sent:
                break
            flow += sent
        require(time.monotonic() - START < 30, 'Exact shared-root certificate: time.monotonic() - START < 30')
    reachable = {source}
    q = deque([source])
    while q:
        u = q.popleft()
        for v, rev, c in graph[u]:
            if c and v not in reachable:
                reachable.add(v)
                q.append(v)
    cut = sum((c for u, v, c, k in original if u in reachable and v not in reachable))
    require(cut == flow, 'Exact shared-root certificate: cut == flow')
    balance = [0] * (N + 2)
    edges = []
    for u, v, c, k in original:
        f = c - graph[u][k][2]
        require(0 <= f <= c, 'Exact shared-root certificate: 0 <= f <= c')
        balance[u] -= f
        balance[v] += f
        edges.append({'from': u, 'to': v, 'capacity': str(c), 'flow': str(f)})
    require(all((x == 0 for x in balance[:N])) and balance[source] == -flow and (balance[sink] == flow), 'Exact shared-root certificate: all((x == 0 for x in balance[:N])) and balance[source] == -flow and (balance[sink] == flow)')
    x = [0 if i in reachable else 1 for i in range(N)]
    value = sum((u[z] for u, z in zip(unary, x))) + sum((w0 if x[i] == 0 else w1 for i, j, w0, w1 in pair if x[i] == x[j]))
    require(value == constant - flow and value <= old, 'Exact shared-root certificate: value == constant - flow and value <= old')
    kappa = F(old - value, D)
    new = F(data['hybrid']['hybrid_Delta_lower']) + kappa
    h = F(Q['head_survival'])
    eps = 1 - h
    Jh, U = (F(data['threshold']['head_moment_exact']), F(data['threshold']['tail_moment_upper_exact']))
    r = next((r for r in data['curve']['records'] if r['B'] == 16384))
    T, loss, E = map(F, (r['T_lower'], r['C_upper'], r['E7_upper']))
    scores = [eps + loss + extra + (U * (Jh - eps - new) - h) / (T - 1) for extra in (F(0), E)]
    out = {'schema': 'shared-first3-root-mincut-certificate-v1', 'status': 'PASS', 'labels': vars, 'old_selected_upper': str(F(old, D)), 'new_selected_upper': str(F(value, D)), 'additional_credit': str(kappa), 'new_total_credit_lower': str(new), 'baseline_score': str(scores[0]), 'E7_score': str(scores[1]), 'decimals': {'old_selected_upper': float(F(old, D)), 'new_selected_upper': float(F(value, D)), 'additional_credit': float(kappa), 'new_total_credit_lower': float(new), 'baseline_score': float(scores[0]), 'E7_score': float(scores[1])}, 'maximizing_roots': {str(d): r + 1 for d, r in zip(vars, x)}, 'common_denominator': str(D), 'constant_numerator': str(constant), 'flow_value_numerator': str(flow), 'source_vertex': source, 'sink_vertex': sink, 'source_side': sorted(reachable), 'flow_edges': edges, 'scope': 'Exact optimum of the globally shared first3-root binary upper relaxation; higher digits and other query residues remain relaxed. Every original selected label distinct. Previous triangle credit overlaps and is not added.'}
    require(Jh==F(budget['exact_initial_head_second']) and U*Jh==F(r['J_upper']),
            'same complete-height head moment and directed full moment')
    require(T>1 and U>=1 and Jh-eps-new>=h and all(h-loss-extra>0 for extra in (F(0),E)),
            'nonnegative head bound and positive common-law survivor mass')
    require(len(unary)==66 and len(pair)==2145 and N*len(others)==5808,
            'all selected unary, shared-root and mixed pair terms occur once')
    out.update(unary_count=len(unary),shared_pair_count=len(pair),mixed_pair_count=N*len(others),
               graph_arc_count=len(edges),root_query_count=len(Q['records']))
    return ctx.finish(out)


if __name__=="__main__":
    _io.run(CERTIFICATE,calculate,__file__)
