#!/usr/bin/env python3
"""Complete actual-source control of the BL18 global selected-block lowering.

Construct one exact-maximum74 source, an initial balanced flow with selected
block18, then minimize that block in the full original balanced network.
This exercises the lowering alternative only; it does not claim to test a
minimum18/supplier alternative or enumerate actual sources.
"""
from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
import json
import runpy


def require(ok, message):
    if not ok:
        raise ValueError(message)


def fixture():
    source = {(r,c): {(g,h) for g in (0,1) for h in range(7)}
              for r,n in enumerate((4,5,5,5)) for c in range(n)}
    for r in (1,2,3):
        for c in range(5):
            source[r,c].add((r+1,c))
    source[3,0].add((4,5))
    atom = defaultdict(Q)
    for c, entries in enumerate((((0,2),(1,2),(2,1)),
                                  ((2,2),(3,2),(4,1)),
                                  ((4,2),(5,2)),((6,2),(0,2)))):
        for h,m in entries:
            atom[0,c,0,h] += m
    atom[0,0,1,0] = Q(1,2)
    for r in (1,2,3):
        for c in range(5):
            atom[r,c,r+1,c] = 2
    atom[3,0,4,5] = 2
    for c in range(5):
        atom[1,c,0,c] = Q(1,2)
    atom[2,0,0,6] = Q(1,2)
    for r, masses in ((1,(2,1,1,1,1)),
                      (2,(2,2,2,1,1)),
                      (3,(1,Q(3,2),1,1,2))):
        for c,m in enumerate(masses):
            atom[r,c,1,c] = m
    return source, dict(atom)


def original_cut_side(node):
    if node[0] in ('S','R','C','P'):
        return True
    if node[0] == 'L':
        return node[3] in (0,1)
    if node[0] in ('F','G'):
        return node[1] in (0,1)
    return False


def mincost(edges, source, sink, value):
    nodes = sorted({v for u,v,cap,cost in edges} | {u for u,v,cap,cost in edges})
    index = {v:i for i,v in enumerate(nodes)}
    adj = [[] for _ in nodes]
    refs = []
    for u,v,cap,cost in edges:
        a,b = index[u],index[v]
        refs.append((a,len(adj[a]),cap))
        adj[a].append([b,len(adj[b]),cap,cost])
        adj[b].append([a,len(adj[a])-1,0,-cost])
    s,t = index[source],index[sink]
    sent = 0
    while sent < value:
        dist = [None]*len(nodes)
        parent = [None]*len(nodes)
        dist[s] = 0
        for step in range(len(nodes)):
            changed = False
            for u,row in enumerate(adj):
                if dist[u] is None:
                    continue
                for k,(v,rev,cap,cost) in enumerate(row):
                    if cap and (dist[v] is None or dist[v] > dist[u]+cost):
                        dist[v] = dist[u]+cost
                        parent[v] = u,k
                        changed = True
            if not changed:
                break
            require(step < len(nodes)-1, 'no negative residual cycle during SSP')
        require(dist[t] is not None, 'balanced value74 remains attainable')
        amount = value-sent
        v = t
        while v != s:
            u,k = parent[v]
            amount = min(amount, adj[u][k][2])
            v = u
        v = t
        while v != s:
            u,k = parent[v]
            rev = adj[u][k][1]
            adj[u][k][2] -= amount
            adj[v][rev][2] += amount
            v = u
        sent += amount
    # An independent global residual shortest-path potential, with a zero
    # edge from a virtual supersource to every vertex.
    pi = [0]*len(nodes)
    for step in range(len(nodes)):
        changed = False
        for u,row in enumerate(adj):
            for v,rev,cap,cost in row:
                if cap and pi[v] > pi[u]+cost:
                    pi[v] = pi[u]+cost
                    changed = True
        if not changed:
            break
        require(step < len(nodes)-1, 'optimal full-network residual potential exists')
    flow = [cap-adj[u][k][2] for u,k,cap in refs]
    for (u,v,cap,cost),f in zip(edges,flow):
        delta = pi[index[v]]-pi[index[u]]
        require(not f or delta >= cost, 'positive edge reverse sign')
        require(f == cap or delta <= cost, 'unsaturated edge forward sign')
    return flow, {n:pi[i] for i,n in enumerate(nodes)}


def main():
    ap = ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--network-helper', type=Path, required=True)
    ap.add_argument('--source-helper', type=Path, required=True)
    args = ap.parse_args()
    network = runpy.run_path(str(args.network_helper))
    source_check = runpy.run_path(str(args.source_helper))['source_checks']
    source,atoms = fixture()
    points = {(r,c,g,h) for (r,c),labels in source.items() for g,h in labels}
    children,pairs,mono = source_check(points)
    edges,trails = network['paths'](source)
    load = defaultdict(Q)
    for point,m in atoms.items():
        require(point in points, 'initial flow uses actual source')
        for edge in trails[point]:
            load[edge] += m
    require(sum(atoms.values()) == 74, 'initial value74')
    require(sum(m for (r,c,g,h),m in atoms.items() if r == 0 and g == 0) == 18,
            'initial selected block18')
    require(all(0 <= load[e] <= (Q(37,2) if e[0] == ('S',) else cap)
                for e,cap in edges.items()), 'initial balanced capacities')
    cut = [e for e in edges if original_cut_side(e[0]) and not original_cut_side(e[1])]
    require(sum(edges[e] for e in cut) == 74, 'matching ORIGINAL cut74')
    require(all(load[e] == edges[e] for e in cut), 'original forward saturation')
    require(all(load[e] == 0 for e in edges
                if not original_cut_side(e[0]) and original_cut_side(e[1])),
            'original zero backward flow')
    costs = {e:int(e[0][0] == 'C' and e[0][1] == 0 and
                   e[1][0] == 'P' and e[1][3] == 0) for e in edges}
    records = [(u,v,37 if u == ('S',) else 2*cap,costs[u,v])
               for (u,v),cap in edges.items()]
    flow,pi = mincost(records,('S',),('T',),148)
    balance = defaultdict(int)
    for (u,v,cap,cost),f in zip(records,flow):
        require(0 <= f <= cap, 'minimum flow all original capacities')
        balance[u] -= f
        balance[v] += f
    require(balance[('S',)] == -148 and balance[('T',)] == 148 and
            all(b == 0 for n,b in balance.items() if n not in (('S',),('T',))),
            'minimum flow full-network conservation')
    optimized = sum(cost*f for (u,v,cap,cost),f in zip(records,flow))
    require(optimized == 0, 'selected block globally lowers18 to0')
    recovered = {point:Q(flow[list(edges).index((('L',)+point,('F',point[2],point[3])))],2)
                 for point in points}
    require(sum(recovered.values()) == 74, 'actual bridge decomposition')
    require(all(sum(m for (rr,c,g,h),m in recovered.items() if rr == r) == Q(37,2)
                for r in range(4)), 'all root totals preserved')
    out = dict(status='PASS', scope='One complete actual maximum74 source; only the BL18 lowering alternative is exercised.',
               original_maximum=74,balanced_total=74,actual_points=len(points),
               actual_network_edges=len(edges),original_pair_checks=pairs,
               original_cut_capacity=74,initial_selected_block='18',minimum_selected_block='0',
               supplier_alternative_tested=False,integer_potential_vertices=len(pi),
               source=[dict(root=r,child=c,whole_fibre=sorted(labels))
                       for (r,c),labels in sorted(source.items())],
               initial_flow=[dict(point=p,mass=str(m)) for p,m in sorted(atoms.items())],
               minimum_flow=[dict(point=p,mass=str(m)) for p,m in sorted(recovered.items()) if m],
               residual_potential=[dict(node=n,value=p) for n,p in sorted(pi.items())])
    args.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in out.items()
                      if k not in ('source','initial_flow','minimum_flow','residual_potential')}))


if __name__ == '__main__':
    main()
