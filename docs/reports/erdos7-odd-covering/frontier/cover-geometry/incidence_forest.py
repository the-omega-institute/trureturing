#!/usr/bin/env python3
"""Literal finite original-family regressions for the incidence proof.

The all-height/rank theorem is proved in Chapter 48, not by these fixtures.
"""
from fractions import Fraction as F
from itertools import product
from math import prod
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import sys
sys.dont_write_bytecode = True


CERTIFICATE = 'certificates/source_norms/cover-geometry/incidence_forest.json'
SOURCES = ('certificate_io.py', 'problem-details/48-incidence-forests-with-arbitrary-original-heights.md', '../../../Library/Arith/balister2018covering.md')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def original(exponents, residues):
    require(set(exponents) == set(residues), 'complete literal CRT label')
    return dict(exponents=exponents, residues=residues,
                modulus=prod(p**e for p,e in exponents.items()))


def analyze(name, heights, labels):
    require(len({label['modulus'] for label in labels}) == len(labels),
            'distinct original numerical moduli')
    primes = sorted(heights)
    spaces = {p:range(p**heights[p]) for p in primes}
    period = prod(len(spaces[p]) for p in primes)
    groups = {}
    pure = {p:[] for p in primes}
    for label in labels:
        ex = label['exponents']
        require(all(1 <= e <= heights[p] for p,e in ex.items()), 'full heights')
        support = tuple(sorted(ex))
        if len(support) == 1:
            pure[support[0]].append(label)
        else:
            groups.setdefault(support,[]).append(label)
    incident = {p:[s for s in groups if p in s] for p in primes}
    visited_p = set()
    visited_s = set()
    children = {p:[] for p in primes}
    roots = []
    parents = {}

    def orient(p):
        require(p not in visited_p, 'acyclic prime introduction')
        visited_p.add(p)
        for support in incident[p]:
            if support in visited_s:
                continue
            visited_s.add(support)
            parents[support] = p
            T = tuple(r for r in support if r != p)
            require(not any(r in visited_p for r in T), 'no incidence cycle')
            children[p].append((support,T))
            for r in T:
                orient(r)

    for p in sorted(primes,key=lambda p:(p!=3,p)):
        if p not in visited_p:
            roots.append(p)
            orient(p)
    require(len(visited_s) == len(groups), 'all support groups assigned once')
    S = {}
    bad = {}
    allowed = {}
    bounds = {}

    def hits(label, point):
        return all(point[p] % p**e == label['residues'][p]
                   for p,e in label['exponents'].items())

    def build(p):
        exceptions = set()
        for support,T in children[p]:
            require(all(r>=5 for r in T), 'no ternary child')
            for r in T:
                build(r)
                require(F(len(S[r]),len(spaces[r])) >= F(r-3,r-1),
                        'actual child domain invariant')
            c = prod(F(1,r-1) for r in T)
            D = prod(r-3 for r in T)
            theta = (D-F(1,4))*c
            group = groups[support]
            weights = [prod(F(1,r**label['exponents'][r]) for r in T) for label in group]
            layers = {}
            for label,w in zip(group,weights):
                a = label['exponents'][p]
                layers[a] = layers.get(a,F(0))+w
            require(all(v<=c for v in layers.values()), 'literal exponent layer capacity')
            B = set()
            for x in spaces[p]:
                active = [i for i,label in enumerate(group)
                          if x % p**label['exponents'][p] == label['residues'][p]]
                L = sum((weights[i] for i in active),F(0))
                tail = sum((weights[i] for i in active if group[i]['exponents'][p]>=D),F(0))
                if L >= theta:
                    B.add(x)
                    require(tail >= 3*c/4, 'pointwise deep-layer excess')
                else:
                    available = []
                    for values in product(*(S[r] for r in T)):
                        point = dict(zip(T,values))
                        point[p] = x
                        if not any(hits(group[i],point) for i in active):
                            available.append(values)
                    require(F(len(available),prod(len(spaces[r]) for r in T)) > c/4,
                            'actual simultaneous extension volume')
                    allowed[support,x] = len(available)
            deep = sum((w*F(1,p**label['exponents'][p])
                        for label,w in zip(group,weights) if label['exponents'][p]>=D),F(0))
            refined = 4*deep/(3*c)
            envelope = F(4,3*(p-1)*p**(D-1))
            require(F(len(B),len(spaces[p])) <= refined <= envelope, 'Haar exception bounds')
            bad[support] = B
            bounds[support] = (c,D,theta,refined,envelope)
            exceptions.update(B)
        S[p] = {x for x in spaces[p]
                if x not in exceptions and not any(hits(label,{p:x}) for label in pure[p])}
        theoretical = 1-F(1,p-1)-F(4*p,3*(p-1)*(p*p-1))
        require(F(len(S[p]),len(spaces[p])) >= theoretical, 'upward prime-domain estimate')
        require(theoretical >= (F(1,4) if p==3 else F(p-3,p-1)), 'closed invariant')

    for root in roots:
        build(root)
    K = 4**(len(roots)+len(groups))*prod(p-1 for p in primes if p not in roots)
    total = F(0)
    survivor_count = 0
    density_max = F(0)
    generated_count = 0
    for values in product(*(spaces[p] for p in primes)):
        point = dict(zip(primes,values))
        safe = not any(hits(label,point) for label in labels)
        survivor_count += safe
        if not safe or not all(point[p] in S[p] for p in primes):
            continue
        probability = prod(F(1,len(S[p])) for p in roots)
        for support in groups:
            probability /= allowed[support,point[parents[support]]]
        total += probability
        generated_count += 1
        density_max = max(density_max,period*probability)
    require(total == 1, 'sequential actual kernel gives one full joint probability')
    require(density_max <= K, 'pointwise full-history density product')
    require(F(survivor_count,period) >= F(1,K), 'original full Haar survival bound')

    source_check = None
    if name == 'deep_edge_with_nonempty_exception':
        support = (3,5)
        # An actual old law avoiding the sole old original 1 mod3.
        sigma = {0:F(1,2),2:F(1,2)}
        require(all(x%3 != 1 for x in sigma), 'old support consists of genuine survivors')
        c,D,_,_,_ = bounds[support]
        actual = sum((m for x,m in sigma.items() if x in bad[support]),F(0))
        rhs = F(0)
        for label in groups[support]:
            a = label['exponents'][3]
            if a >= D:
                m = sum((mass for x,mass in sigma.items()
                         if x % 3**a == label['residues'][3]),F(0))
                rhs += F(1,5**label['exponents'][5])*m
        rhs *= 4/(3*c)
        require(actual == F(1,2) and actual <= rhs, 'unchanged arbitrary-source failure fee')
        source_check = dict(actual_failure=str(actual),original_deep_fee=str(rhs))
    return dict(name=name,period=period,labels=len(labels),supports=len(groups),
                roots=roots,max_support=max(map(len,groups),default=1),
                domain_sizes={str(p):len(S[p]) for p in primes},
                exception_sizes={str(s):len(B) for s,B in bad.items()},
                survivors=survivor_count,survival=str(F(survivor_count,period)),
                generated_points=generated_count,joint_probability=str(total),
                maximum_density=str(density_max),density_bound=K,
                same_old_source=source_check)



def calculate(base):
    edge = [original({3:1},{3:1}),original({5:1},{5:0}),original({5:2},{5:4})]
    edge += [original({3:a,5:b},{3:0,5:1}) for a in (1,2,3) for b in (1,2)]
    high = [original({p:1},{p:0}) for p in (3,5,7,11,13)]
    high += [original({3:a,5:1,7:1,11:1},{3:1,5:1,7:1,11:1}) for a in (1,2)]
    high += [original({11:1,13:1},{11:2,13:3})]
    result = dict(result='PASS',scope='Finite original-family controls for the ordinary general proof.',
                  cases=[analyze('deep_edge_with_nonempty_exception',{3:3,5:2},edge),
                         analyze('rank_four_support_with_child_edge',{3:2,5:1,7:1,11:1,13:1},high)])
    result['schema'] = 'incidence-forest-v1'
    result['source_sha256'] = {p:hashlib.sha256((base/p).read_bytes()).hexdigest() for p in SOURCES}
    result['producer_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('incidence_certificate_io',args.base/'certificate_io.py')
    require(spec is not None and spec.loader is not None, 'readable certificate IO')
    io = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(io)
    result = calculate(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),
                'exact incidence certificate replay')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
