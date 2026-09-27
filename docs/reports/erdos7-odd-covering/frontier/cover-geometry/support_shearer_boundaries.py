#!/usr/bin/env python3
"""Exact degree-six and degree-seven boundaries of complete support-Shearer envelopes."""
import argparse
from fractions import Fraction as F
from fractions import Fraction
from itertools import combinations
from functools import lru_cache
from math import prod
from pathlib import Path
import importlib.util
import hashlib
import json
import sys
sys.dont_write_bytecode = True

CERTIFICATE = 'certificates/source_norms/cover-geometry/support_shearer_boundaries.json'
SOURCES = ('certificate_io.py', 'problem-details/50-prime-support-incidence-at-most-five.md', 'problem-details/52-two-or-four-exact-predecessor-supports.md',
    'problem-details/53-shared-small-prime-budgets-for-six-or-seven-predecessor-supports.md')


def require(c,msg):
    if not c:raise ValueError(msg)


def boundary_checks():
    primes=(3,5,7,11,13,17,19)
    edges=tuple(map(frozenset,[(3,5),(3,7),(3,11),(3,13),(3,17),
        (5,7),(5,11),(5,13),(5,17),(7,11),(7,13),(7,19),
        (11,13),(11,17),(11,19),(3,5,7)]))
    require(len(edges)==len(set(edges))==16 and min(map(len,edges))>=2,'16 distinct nonsingleton supports')
    degree={p:sum(p in E for E in edges) for p in primes}
    require(max(degree.values())==6,'maximum incidence exactly6')
    D=prod(p-2 for p in primes)
    matching_weights=[0]*(1<<len(edges));coeff=[0]*4;matching_counts=[0]*4
    # Independent direct matching enumeration, no vertex or event deletion recursion.
    for k in range(4):
        for inds in combinations(range(len(edges)),k):
            selected=[edges[i] for i in inds]
            union=frozenset().union(*selected)
            if sum(map(len,selected))!=len(union):continue
            denominator=prod(p-2 for p in union)
            require(D%denominator==0,'matching monomial divides common denominator')
            value=(-1)**k*(D//denominator)
            mask=sum(1<<i for i in inds)
            matching_weights[mask]=value;coeff[k]+=value;matching_counts[k]+=1
    # Four disjoint nonsingleton supports need8 primes; only7 exist.
    require(2*4>len(primes),'no larger matching exists')
    require(F(sum(coeff),D)==F(-92,378675),'independent exact negative polynomial')
    polynomial=matching_weights.copy()
    for i in range(len(edges)):
        for mask in range(1<<len(edges)):
            if mask>>i&1:polynomial[mask]+=polynomial[mask^(1<<i)]
    require(polynomial[-1]==sum(coeff),'all-subfamily transform agrees')
    require(all(z>0 for z in polynomial[:-1]),'every proper induced polynomial strictly positive')
    minproper=min(polynomial[:-1]);minmask=polynomial[:-1].index(minproper)
    result=dict(scope='Exact counterexample to universal degree6 support-Shearer positivity, not an actual congruence covering.',
                primes=primes,supports=[sorted(E) for E in edges],numerical_squarefree_moduli=[prod(E) for E in edges],degree=degree,
                common_denominator=D,matching_counts=matching_counts,matching_coefficients=[str(F(z,D)) for z in coeff],
                signed_polynomial=str(F(sum(coeff),D)),proper_subfamilies_checked=(1<<len(edges))-1,
                minimum_proper_polynomial=str(F(minproper,D)),minimum_proper_supports=[sorted(E) for i,E in enumerate(edges) if minmask>>i&1])
    return result


def degree_seven_boundary_checks():
    def check(condition, message):
        if not condition:
            raise RuntimeError(message)


    primes = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31)
    base = [frozenset(e) for e in combinations(primes[:8], 2)]
    old = frozenset((19, 23))
    new = frozenset((19, 23, 29, 31))
    supports = [e for e in base if e != old] + [new]


    def weight(edge):
        result = Fraction(1)
        for p in edge:
            result /= p - 2
        return result


    def polynomial(edges):
        weighted = [(sum(1 << primes.index(p) for p in e), weight(e))
                    for e in edges]

        @lru_cache(None)
        def matching(carrier):
            if not carrier:
                return Fraction(1)
            bit = carrier & -carrier
            return matching(carrier ^ bit) - sum(
                (w * matching(carrier ^ edge) for edge, w in weighted
                 if edge & bit and edge & carrier == edge), Fraction(0))

        return matching((1 << len(primes)) - 1)


    z_base = polynomial(base)
    z_new = polynomial(supports)
    z_residual = polynomial([e for e in base if e.isdisjoint(old)])
    check(z_base == Fraction(-113684, 2650725), 'base K8')
    check(z_new == Fraction(-9849844, 230613075) and z_new < 0, 'new negative')
    check(z_residual == Fraction(52, 825), 'residual K6')
    check(z_new == z_base + (weight(old) - weight(new)) * z_residual,
          'independent one-edge replacement identity')
    union = sum((weight(e) for e in supports), Fraction(0))
    check(union == Fraction(5549956, 4521825) and union > 1, 'union')
    incidence = tuple(sum(p in e for e in supports) for p in primes)
    ending = tuple(sum(max(e) == p for e in supports) for p in primes)
    check(incidence == (7, 7, 7, 7, 7, 7, 7, 7, 1, 1), 'incidence')
    check(ending == (0, 1, 2, 3, 4, 5, 6, 6, 0, 1), 'ending')
    check(min(sum(p in e for e in supports if len(e) == 2)
              for p in primes[:8]) == 6, 'pair minimum degree')
    check(sum(map(len, supports)) - len(supports) - len(primes) + 1 == 21,
          'incidence cycle rank')
    adjacency = {p: set() for p in primes}
    for e in supports:
        for p in e:
            adjacency[p].update(e - {p})


    def connected(carrier):
        seen = {next(iter(carrier))}
        queue = list(seen)
        while queue:
            p = queue.pop()
            for q in (adjacency[p] & carrier) - seen:
                seen.add(q)
                queue.append(q)
        return seen == carrier


    check(connected(set(primes)), 'connected')
    check(all(connected(set(primes) - {p}) for p in primes), 'no articulation')
    return dict(primes=primes,supports=[sorted(e) for e in supports],incidence=incidence,
                numerical_ending_counts=ending,support_count=len(supports),maximum_rank=max(map(len,supports)),
                incidence_cycle_rank=sum(map(len,supports))-len(supports)-len(primes)+1,
                connected=connected(set(primes)),no_articulation=all(connected(set(primes)-{p}) for p in primes),
                original_K8_polynomial=str(z_base),modified_polynomial=str(z_new),
                residual_K6_polynomial=str(z_residual),union_weight=str(union),
                old_support_weight=str(weight(old)),new_support_weight=str(weight(new)))


def calculate(base):
    result = dict(schema='support-shearer-boundaries-v1', boundary=boundary_checks())
    counts = {p:len({frozenset(E)-{p} for E in result['boundary']['supports'] if max(E)==p})
              for p in result['boundary']['primes']}
    require(max(counts.values())<=4,'at most four exact predecessor supports at every largest prime')
    result['predecessor_support_counts_by_prime'] = counts
    result['degree_seven_replacement'] = degree_seven_boundary_checks()
    result['source_sha256'] = {p:hashlib.sha256((base/p).read_bytes()).hexdigest() for p in SOURCES}
    result['producer_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    return json.loads(json.dumps(result))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write',action='store_true')
    mode.add_argument('--check',action='store_true')
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('support_shearer_boundaries_io',args.base/'certificate_io.py')
    require(spec is not None and spec.loader is not None,'readable certificate IO')
    io = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(io)
    result = calculate(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path,json.dumps(result,indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(path),object_pairs_hook=io._unique),
                'exact support-Shearer boundary certificate replay')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
