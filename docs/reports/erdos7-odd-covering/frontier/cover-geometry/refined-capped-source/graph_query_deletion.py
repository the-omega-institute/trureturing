#!/usr/bin/env python3
"""Independent finite arithmetic for graph marks and one live-cell deletion.

Only Python's standard library is used. All assertions are explicit guards and
therefore remain enabled under -O. This is arithmetic evidence, not Lean.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, factorial, prod
import json
from pathlib import Path
import argparse


def require(ok, message):
    if not ok:
        raise ValueError(message)


P = (3, 5, 7, 11, 13, 17, 19, 23)
K = (2, 2, 2, 2, 4, 4, 4, 3)
E = ((0, 3), (3, 4), (4, 5), (5, 6), (6, 7), (1, 5), (2, 6))
Q = prod(P)
MIXED = ((33, 1), (85, 1), (133, 1), (143, 1),
         (221, 1), (323, 1), (437, 1))


def graph_validate(k, edges):
    require(all(n >= 2 for n in k), "every vertex requires a nonspecial root")
    canon = [tuple(sorted(edge)) for edge in edges]
    require(all(len(edge) == 2 and 0 <= edge[0] < edge[1] < len(k)
                for edge in canon), "edges must be simple and in range")
    require(len(set(canon)) == len(canon), "duplicate edge")


def graph_roots(k, edges):
    graph_validate(k, edges)
    return tuple(x for x in product(*(range(1, n + 1) for n in k))
                 if all(x[i] != 1 or x[j] != 1 for i, j in edges))


def Z(weights, edges, vertices=None):
    vertices = tuple(range(len(weights))) if vertices is None else tuple(vertices)
    total = F(0)
    for bits in range(1 << len(vertices)):
        independent = {v for j, v in enumerate(vertices) if bits >> j & 1}
        if all(i not in independent or j not in independent for i, j in edges):
            total += prod((weights[v] for v in vertices if v not in independent), start=F(1))
    return total


def root_histogram(roots, support):
    return Counter(tuple(x[i] for i in support) for x in roots)


def drops(k, edges, support):
    return all(k[v] == 2 and any((i == v and j not in support) or
                                (j == v and i not in support)
                                for i, j in edges) for v in support)


def crt(x):
    return sum(a * (Q // p) * pow(Q // p, -1, p) for a, p in zip(x, P)) % Q


def maxima(roots, enumerate_phases=False):
    answer = []
    phases = 0
    for mask in range(1 << len(K)):
        support = tuple(i for i in range(len(K)) if mask >> i & 1)
        hist = root_histogram(roots, support)
        require(bool(hist), "nonempty source")
        if enumerate_phases:
            values = [hist.get(a, 0) for a in product(*(range(1, K[i] + 1) for i in support))]
            phases += len(values)
            require(max(values) == max(hist.values()), "phase enumeration mismatch")
        answer.append(max(hist.values()))
    return answer, phases


def complete_budget(maxima_counts):
    return sum(F(n, Q) * prod((F(p, p - 1) for i, p in enumerate(P) if mask >> i & 1),
                             start=F(1)) for mask, n in enumerate(maxima_counts))


def a4(p):
    t = F(1, p - 1)
    return 15*t + 50*t**2 + 60*t**3 + 24*t**4


def quartic(maxima_counts):
    # A queried root costs no 1/p factor at depth one. Hence p*A4(p).
    return sum(F(n, Q) * prod((p*a4(p) for i, p in enumerate(P) if mask >> i & 1),
                             start=F(1)) for mask, n in enumerate(maxima_counts))


def check_height_factors():
    checks = 0
    height = 4
    for p in P + (29,):
        geometric = sum(F(1, p**(e-1)) for e in range(1, height+1))
        geometric += F(1, p**height) * F(p, p-1)
        require(geometric == F(p, p-1), "all-height first factor")
        brute = sum(F(1, p**(max(es)-1)) for es in product(range(height+1), repeat=4) if max(es)>0)
        grouped = sum(((e+1)**4-e**4)*F(1, p**(e-1)) for e in range(1,height+1))
        require(brute == grouped, "ordered tuples grouped by maximum")
        # Exact unbounded remainder, expressed through geometric moments.
        g0, g1 = F(1,p-1), F(p,(p-1)**2)
        g2, g3 = F(p*(p+1),(p-1)**3), F(p*(p*p+4*p+1),(p-1)**4)
        h=height
        remainder = F(1,p**(h-1))*((4*h**3+6*h*h+4*h+1)*g0 +
                       (12*h*h+12*h+4)*g1 +(12*h+6)*g2+4*g3)
        require(grouped+remainder == p*a4(p), "complete root-weighted quartic factor")
        checks += 3
    return checks


def generic_controls():
    graph_list = (
        (),
        tuple((0,j) for j in range(1,5)),
        tuple((j,j+1) for j in range(4)),
        ((0,1),(1,2),(2,3),(3,4),(0,4)),
        tuple(combinations(range(5),2)),
    )
    models = supports = 0
    for edges in graph_list:
        for k in product((2,3), repeat=5):
            before = graph_roots(k,edges)
            after = tuple(x for x in before if x != (2,)*5)
            for mask in range(32):
                support = tuple(i for i in range(5) if mask >> i & 1)
                old = max(root_histogram(before,support).values())
                new = max(root_histogram(after,support).values())
                free = tuple(i for i in range(5) if i not in support)
                require(old == Z(tuple(n-1 for n in k),edges,free), "generic maximum formula")
                require(old-new == int(drops(k,edges,support)), "generic deletion neighborhood criterion")
                supports += 1
            models += 1
    invalid = 0
    for k, edges in (((1,2),()), ((2,2),((0,0),)), ((2,2),((0,1),(1,0)))):
        try:
            graph_validate(k,edges)
        except ValueError:
            invalid += 1
        else:
            raise ValueError("invalid graph accepted")
    return dict(models=models,support_checks=supports,invalid_controls_rejected=invalid)


def minimal_hyperedges(n, edges):
    raw = {frozenset(edge) for edge in edges}
    require(all(edge and all(0 <= i < n for i in edge) for edge in raw),
            "hyperedges must be nonempty and in range")
    return tuple(sorted((edge for edge in raw if not any(other < edge for other in raw)),
                        key=lambda edge: (len(edge),tuple(sorted(edge)))))


def hyper_roots(k, edges):
    require(all(v >= 2 for v in k),"hypergraph root alphabets require nonspecial roots")
    return tuple(x for x in product(*(range(1,v+1) for v in k))
                 if not any(all(x[i] == 1 for i in edge) for edge in edges))


def hyper_Z(weights, edges, vertices):
    vertices=tuple(vertices)
    result=F(0)
    for mask in range(1<<len(vertices)):
        special={i for j,i in enumerate(vertices) if mask>>j&1}
        if not any(edge <= special for edge in edges):
            result += prod((weights[i] for i in vertices if i not in special),start=F(1))
    return result


def hyper_drop(k,edges,support):
    return all(k[v] == 2 and any(edge.intersection(support) == {v} for edge in edges)
               for v in support)


def hypergraph_controls():
    n=3
    possible=tuple(frozenset(i for i in range(n) if mask>>i&1) for mask in range(1,1<<n))
    models=supports=redundant_models=zero_successors=0
    for family in range(1<<len(possible)):
        raw=tuple(edge for j,edge in enumerate(possible) if family>>j&1)
        minimal=minimal_hyperedges(n,raw)
        for k in product((2,3),repeat=n):
            roots=hyper_roots(k,raw)
            require(roots == hyper_roots(k,minimal),"minimalizing preserves exact root source")
            after=tuple(x for x in roots if x != (2,)*n)
            zero_successors += int(not after)
            for mask in range(1<<n):
                support={i for i in range(n) if mask>>i&1}
                old=max(root_histogram(roots,sorted(support)).values(),default=0)
                new=max(root_histogram(after,sorted(support)).values(),default=0)
                free=tuple(i for i in range(n) if i not in support)
                require(old==hyper_Z(tuple(v-1 for v in k),minimal,free),"hypergraph induced partition maximum")
                require(old-new==int(hyper_drop(k,minimal,support)),"hypergraph clutter deletion criterion")
                supports+=1
            models+=1
            redundant_models+=int(len(minimal)<len(raw))
    # A redundant superset can fabricate an exposing edge if not removed.
    raw=(frozenset((0,)),frozenset((0,1)))
    k=(2,2); support={1}
    before=hyper_roots(k,raw)
    after=tuple(x for x in before if x != (2,2))
    actual=max(root_histogram(before,tuple(support)).values())-max(root_histogram(after,tuple(support)).values())
    require(actual==0 and hyper_drop(k,raw,support) and
            not hyper_drop(k,minimal_hyperedges(2,raw),support),"raw-edge criterion negative control")
    try:
        minimal_hyperedges(2,(frozenset(),))
    except ValueError:
        empty_rejected=True
    else:
        raise ValueError("empty edge was admitted")
    actual_edges=tuple(frozenset(edge) for edge in E)
    require(hyper_Z(tuple(F(v-1)+F(p,p-1) for v,p in zip(K,P)),actual_edges,range(8))
              ==Z(tuple(F(v-1)+F(p,p-1) for v,p in zip(K,P)),E),"graph is exact hypergraph special case")
    return dict(raw_hypergraph_families=1<<len(possible),models=models,
                support_checks=supports,redundant_models=redundant_models,
                zero_successor_models=zero_successors,empty_edge_rejected=empty_rejected,
                nonminimal_edge_false_positive_detected=True)


def main():
    graph_validate(K,E)
    require(all(k <= p-1 for k,p in zip(K,P)), "actual root alphabets in nonzero residues")
    block = tuple(product(*(range(1,k+1) for k in K)))
    residues = {x:crt(x) for x in block}
    require(len(set(residues.values())) == len(block), "CRT injectivity")
    for x,r in residues.items():
        require(tuple(r % p for p in P)==x,"CRT reconstruction")
    originals = tuple((p,0) for p in P)+MIXED
    numerical = tuple(x for x in block if all(residues[x]%d != a for d,a in originals))
    require(numerical == graph_roots(K,E),"literal originals equal graph source")
    changed = tuple((d,67 if d==143 else a) for d,a in originals)
    incoherent = tuple(x for x in block if all(residues[x]%d != a for d,a in changed))
    deleted = tuple(x for x in numerical if residues[x]%Q != 2)
    require(len(numerical)==1482 and len(deleted)==1481 and len(incoherent)==1464,"actual source cardinalities")
    require(tuple(x for x in numerical if x not in deleted)==((2,)*8,),"actual deleted live cell")
    labels = originals+((Q,2),)
    require(len({d for d,a in labels})==16,"distinct original numerical labels")
    pairs=0
    for (d,a),(e,b) in combinations(sorted(labels),2):
        if e%d==0:
            require(b%d != a,"actual proper-divisor originals intersect")
            pairs += 1
    old,phase_count = maxima(numerical,True)
    new,new_phase_count = maxima(deleted,True)
    inc,inc_phase_count = maxima(incoherent,True)
    require(phase_count==new_phase_count==inc_phase_count==40500,"root phase checks")
    eligible=[]
    for mask in range(256):
        support=tuple(i for i in range(8) if mask>>i&1)
        free=tuple(i for i in range(8) if i not in support)
        require(old[mask]==Z(tuple(k-1 for k in K),E,free),"actual maximum versus induced partition")
        require(old[mask]-new[mask]==int(drops(K,E,support)),"actual deletion credit criterion")
        if old[mask]-new[mask]: eligible.append(mask)
    mass,mass_new=F(len(numerical),Q),F(len(deleted),Q)
    budget,budget_new,budget_inc=map(complete_budget,(old,new,inc))
    shifted=tuple(F(k-1)+F(p,p-1) for k,p in zip(K,P))
    require(budget == Z(shifted,E)/Q,"partition shifted-factor identity")
    credit=(budget-budget_new)*Q
    require(credit==F(351,20),"actual weighted deletion credit")
    require(budget/mass==F(1513740786341,54086123520),"old mean")
    require(budget_new/mass_new==F(1513100292773,54049628160),"new mean")
    require(budget_inc/F(len(incoherent),Q)==F(1503075311141,53429207040),"phase-sensitive control")
    require(budget/mass < budget_new/mass_new < 28 < budget/mass_new,"credit preserves but does not improve margin")
    sigma=28*mass_new-budget_new
    require(sigma==F(289295707,4070927302041600),"slack")
    mass29=sigma/28
    fourth=quartic(new)
    fourth29=fourth*(1+a4(29))
    require(fourth29==F(102509552036551597634646100370192341,
                          8740445251530270887053885440000),"raw fourth envelope")
    B,ell,r,delta=40000,9,25,F(2,5)
    require(B>=286 and ell>=4 and 3**ell<=B and 4*ell>=r,"analytic-tail prerequisites")
    coefficients=(F(1),F(25),F(250,3),F(100),F(40))
    require(all(coefficients[j]<=comb(r,j) for j in range(5)),"tail growth polynomial domination")
    constant=F(27,256)/delta**3/(1-delta)
    require(constant/3==F(5625,6144),"quartic tail coefficient")
    cell=F(2*ell*ell+1,2*ell*ell-1)
    tail=constant/3*cell**r*F(B,(B-1)**4)*sum(F(factorial(r),factorial(r-j)*(3*ell)**j) for j in range(r+1))
    margin=mass29-fourth29*tail
    require(margin>F(1,10**9),"strict complete-tail margin")
    height_checks=check_height_factors()
    generic=generic_controls()
    hypergeneric=hypergraph_controls()
    return {
        "status":"independent_exact_checks_passed_not_Lean",
        "primes":P,"root_sizes":K,"root_period":Q,"originals":labels,
        "initial_roots":len(block),"coherent_roots":len(numerical),
        "deleted_roots":len(deleted),"incoherent_roots":len(incoherent),
        "proper_divisor_pairs":pairs,"query_supports":256,
        "query_phases_per_source":phase_count,"maxima_before":old,"maxima_after":new,
        "eligible_masks":eligible,"complete_budget_before":budget,
        "complete_budget_after":budget_new,"mean_before":budget/mass,
        "mean_after":budget_new/mass_new,"mass_only_mean":budget/mass_new,
        "incoherent_mean":budget_inc/F(len(incoherent),Q),
        "deletion_credit_in_root_units":credit,"slack":sigma,"mass29_lower":mass29,
        "raw_quartic_envelope_before29":fourth,"raw_quartic_envelope_after29":fourth29,
        "tail_parameters":{"B":B,"ell":ell,"r":r,"delta":delta},
        "tail_factor":tail,"margin":margin,"margin_decimal":float(margin),
        "analytic_input":"Report734 HM14 Rosser--Schoenfeld Theorem8; not independently reproved",
        "all_height_numeric_controls":height_checks,"generic_graph_controls":generic,
        "generic_hypergraph_controls":hypergeneric,
        "support_restriction":"P union {29} union primes strictly above40000; other old originals must miss retained mark",
        "fourth_envelope_not_claimed_attained":True,
    }


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument('--write-result',type=Path)
    args=parser.parse_args()
    result=json.loads(json.dumps(main(),default=str))
    if args.write_result:
        args.write_result.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    else:
        require(result==json.loads(Path(__file__).with_suffix('.json').read_text()),
                'Fresh graph result equals retained exact data')
    print(json.dumps({k:result[k] for k in ('coherent_roots','deleted_roots','deletion_credit_in_root_units','mean_after','margin_decimal')},indent=2))
