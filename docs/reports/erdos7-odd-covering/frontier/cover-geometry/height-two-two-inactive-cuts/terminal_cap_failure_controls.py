#!/usr/bin/env python3
"""Actual-source countercontrols to universal terminal-cap feasibility.

A matching feasible atom flow and an explicit equal-capacity cut certify
maximum values74,75,76. Every original legal pair and numerical cylinder
is checked. No source-family enumeration or Lean verification is asserted.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, product
import json
from pathlib import Path
import runpy


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fixture(total):
    source = {(r,c):set() for r,n in enumerate((4,5,5,5)) for c in range(n)}
    for c in range(4):
        source[0,c] = {(g,h) for g in (4,5) for h in (c,c+1)}
    for r in (1,2,3):
        for c in range(5):
            source[r,c].add((r,c))
            if total != 75 or r != 3:
                source[r,c].add((0,c))
    source[3,0].add((3,5))
    if total in (75,76):
        source[3,1].add((3,6))
    flow = defaultdict(int)
    for c in range(3):
        for g,h,m in ((4,c,2),(4,c+1,2),(5,c,1),(5,c+1,2)):
            flow[0,c,g,h] += m
    for r in (1,2,3):
        for c in range(5):
            flow[r,c,r,c] = 2
    flow[3,0,3,5] = 2
    if total in (75,76):
        flow[3,1,3,6] = 2
    common = ((2,2,2,2,0),(2,2,2,2,0),(1,2,2,0,0))
    if total == 75:
        common = ((2,2,2,2,2),(2,2,2,2,2),(0,0,0,0,0))
    for r,values in enumerate(common,1):
        for c,m in enumerate(values):
            if m: flow[r,c,0,c] = m
    return source, dict(flow)


def paths(source):
    """Live original network; dead stubs have no source-to-sink paths."""
    edges = {}
    point_paths = {}
    for (r,c),labels in source.items():
        for g,h in labels:
            nodes = [('S',),('R',r),('C',r,c),('P',r,c,g),
                     ('L',r,c,g,h),('F',g,h),('G',g),('T',)]
            trail = list(zip(nodes,nodes[1:]))
            for edge,capacity in zip(trail,(21,7,6,2,126,7,21)):
                require(edge not in edges or edges[edge] == capacity, 'one original capacity')
                edges[edge] = capacity
            point_paths[r,c,g,h] = trail
    return edges,point_paths


def cut_side(node,total):
    kind = node[0]
    if kind == 'S': return True
    if kind in ('R','C','P'): return node[1] != 0
    if total != 75:
        if kind == 'L': return node[1] != 0 and node[3] == 0
        if kind in ('F','G'): return node[1] == 0
    return False


def check(total, helper):
    source,flow = fixture(total)
    require(len(source) == 19 and all(source.values()), 'all original owners nonempty')
    tree = helper['tree_exists']
    restrictions = {r:list(combinations(range(n),k))
                    for r,(n,k) in enumerate(zip(helper['N'],helper['SELECT']))}
    projections = {r:[set().union(*(source[r,c] for c in cs)) for cs in rr]
                   for r,rr in restrictions.items()}
    checks = 0
    for r,s in combinations(range(4),2):
        for a,b in product(projections[r],projections[s]):
            require(tree(a|b,3,3), 'original whole-fibre legal pair')
            checks += 1
    require(checks == 480, 'all original pair tests')
    require(tree(set().union(*source.values()),5,5), 'original standalone five-tree')
    require(all(not all(tree(p,3,3) for p in pp) for pp in projections.values()),
            'no individually robust root')
    require(all((g,h) in source[r,c] and m > 0 for (r,c,g,h),m in flow.items()),
            'same actual atom source')
    require(sum(flow.values()) == total, 'claimed total')
    edges,trails = paths(source)
    load = defaultdict(int)
    for point,m in flow.items():
        for edge in trails[point]: load[edge] += m
    require(all(0 <= load[e] <= cap for e,cap in edges.items()), 'every original capacity')
    forward = [e for e in edges if cut_side(e[0],total) and not cut_side(e[1],total)]
    backward = [e for e in edges if not cut_side(e[0],total) and cut_side(e[1],total)]
    capacity = sum(edges[e] for e in forward)
    require(capacity == total, 'matching original cut')
    require(all(load[e] == edges[e] for e in forward), 'forward saturation')
    require(all(load[e] == 0 for e in backward), 'zero backward flow')
    require(all(e[0][0] != 'L' for e in forward), 'no actual bridge cut')
    forced_root = (('S',),('R',0))
    require(forced_root in forward and edges[forced_root] == 21, 'root0 forced21 in every maximum')
    if total != 75:
        require((('G',0),('T',)) in forward, 'column0 forced21 in every maximum')
    caps,cylinders = helper['numerical_caps'](flow)
    expected = {74:(74,21,21,7,12,6,4,4,2),
                75:(75,21,20,7,14,4,4,4,2),
                76:(76,21,21,7,14,6,4,4,2)}[total]
    require(caps == expected, 'all original numerical caps')
    numerator = sum(c*m for c,m in zip(helper['COEFF'][1:],caps[1:]))
    envelope = 1+Q(numerator,total)
    require(envelope == {74:Q(543,74),75:Q(183,25),76:Q(563,76)}[total], 'common-law bound')
    require(envelope < 9, 'strict bound')
    failures = []
    for cap in (19,20):
        value = sum((cap if e[0][0] == 'S' else edges[e]) for e in forward)
        require(value < total, 'root cap infeasible at original maximum')
        failures.append({'root_cap':cap,'cut_capacity':value})
    if total != 75:
        for cap in (19,20):
            value = sum((cap if e[1] == ('T',) else edges[e]) for e in forward)
            require(value < total, 'column cap infeasible at original maximum')
            failures.append({'column_cap':cap,'cut_capacity':value})
    return {'maximum':total,'actual_points':sum(map(len,source.values())),
            'original_pair_checks':checks,'network_edges_checked':len(edges),
            'cut_capacity':capacity,'cut_forward_arcs':len(forward),
            'numerical_cylinders':cylinders,'raw_caps':list(map(str,caps)),
            'envelope':str(envelope),'terminal_cap_failure_cuts':failures,
            'source':[{'root':r,'child':c,'whole_fibre':sorted(labels)}
                      for (r,c),labels in sorted(source.items())],
            'flow':[{'point':p,'mass':m} for p,m in sorted(flow.items())]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True,type=Path)
    parser.add_argument('--helper',type=Path,default=Path(__file__).resolve().parent.parent/
                        'height-two-small-anchors'/'small_anchor_actual_controls.py')
    args = parser.parse_args()
    helper = runpy.run_path(str(args.helper))
    cases = [check(total,helper) for total in (74,75,76)]
    result = {'status':'PASS','cases':cases,
              'scope':'Three exact actual-source countercontrols to universal terminal caps; not an odd covering counterexample or Lean proof.'}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS','exact_maxima':[c['maximum'] for c in cases],
                      'envelopes':[c['envelope'] for c in cases],
                      'original_pair_checks':sum(c['original_pair_checks'] for c in cases),
                      'numerical_cylinders':sum(c['numerical_cylinders'] for c in cases)}))


if __name__ == '__main__': main()
