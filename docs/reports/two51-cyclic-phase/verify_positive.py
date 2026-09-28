#!/usr/bin/env python3
"""Exact probability and retained-reference checks for Context Geometry section87.

Python >=3.10; standard library only. Companion verify.py must be beside this
file. Run from any cwd, optionally with --output PATH. These finite checks do
not enumerate all controllers or replace the universal arguments in section87.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as Q
import importlib.util
from itertools import combinations, product
import json
from math import prod
from pathlib import Path

if not __debug__:
    raise RuntimeError("Exact verification requires assertions; remove -O/PYTHONOPTIMIZE.")
_spec = importlib.util.spec_from_file_location(
    "two51_cyclic_helpers", Path(__file__).with_name("verify.py"))
if _spec is None or _spec.loader is None:
    raise ImportError("Cannot load companion exact linear algebra helpers.")
_helpers = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_helpers)
columns, eye, local_basis, mul, rank, RowBasis = (
    getattr(_helpers, n) for n in ("columns", "eye", "local_basis", "mul", "rank", "RowBasis"))


def inverse(a):
    n = len(a)
    rows = [list(map(Q, r)) + e for r, e in zip(a, eye(n))]
    for j in range(n):
        pivot = next(i for i in range(j, n) if rows[i][j])
        rows[j], rows[pivot] = rows[pivot], rows[j]
        z = rows[j][j]
        rows[j] = [x/z for x in rows[j]]
        for i in range(n):
            if i != j and rows[i][j]:
                z = rows[i][j]
                rows[i] = [x-z*y for x, y in zip(rows[i], rows[j])]
    assert [r[:n] for r in rows] == eye(n)
    return [r[n:] for r in rows]


def marginal_model(dims):
    points = list(product(*(range(n) for n in dims)))
    bases = [local_basis(n) for n in dims]
    indices = [s for s in points if sum(x != 0 for x in s) >= 2]
    k = columns([[prod(bases[j][s[j]][x[j]] for j in range(len(dims)))
                  for x in points] for s in indices])
    m = [[int(x[j] == a) for x in points] for j, n in enumerate(dims) for a in range(n)]
    n = len(points)
    # Orthogonal projector onto the full interaction space.
    p = [[Q(int(x == y)) - Q(sum(dims[j] for j in range(len(dims)) if x[j] == y[j])
                              - len(dims) + 1, n) for y in points] for x in points]
    assert rank(m) == 1 + sum(d-1 for d in dims)
    assert rank(k) == n - rank(m)
    assert mul(m, k) == [[0]*len(indices) for _ in m]
    assert mul(p, p) == p and mul(p, k) == k
    classes = {tuple(r) for r in p}
    distances = []
    for i, j in combinations(range(n), 2):
        distance = sum((a-b)**2 for a, b in zip(p[i], p[j]))
        formula = 2*(1-Q(sum(dims[c] for c in range(len(dims))
                              if points[i][c] != points[j][c]), n))
        assert distance == formula
        distances.append(distance)
    return points, k, m, {"factor_sizes": dims, "configurations": n,
                          "affine_dimension": rank(k), "coordinate_classes": len(classes),
                          "minimum_squared_separation": str(min(distances))}


def positive_encoding():
    points, k, m, summary = marginal_model((5, 3, 2, 2))
    rb, selected = RowBasis(), []
    for i, row in enumerate(k):
        if rb.insert(row):
            selected.append(i)
    assert len(selected) == 51
    e = [[Q(1+int(x == i), 104) for x in range(60)] for i in selected]
    e.append([1-sum(row[x] for row in e) for x in range(60)])
    assert len(e) == 52 and min(map(min, e)) > 0
    assert all(sum(r[x] for r in e) == 1 for x in range(60))
    b = [[Q(1, 60)] + row for row in k]
    eb = mul(e, b)
    assert rank(eb) == 52
    decoder = mul(b, inverse(eb))
    assert mul(decoder, eb) == b
    assert all(sum(r[y] for r in decoder) == 1 for y in range(52))
    negative = [(x, y, z) for x, row in enumerate(decoder) for y, z in enumerate(row) if z < 0]
    assert negative
    p0 = [[Q(1,60)] for _ in points]
    marginal = mul(m, p0)
    cases = 0
    for j in range(51):
        for sign in (-1, 1):
            p = [[Q(1,60)+sign*Q(row[j],120)] for row in k]
            assert min(r[0] for r in p) > 0 and mul(m,p) == marginal
            assert mul(decoder,mul(e,p)) == p
            cases += 1
    # A stochastic inverse on this whole family is ruled out by the prose
    # theorem; this computation only exhibits the signed inverse of our encoder.
    summary.update({"encoder_outputs": 52, "encoder_minimum_entry": str(min(map(min,e))),
                    "augmented_image_rank": rank(eb), "selected_coordinates": selected,
                    "signed_decoder_minimum_entry": str(min(map(min,decoder))),
                    "positive_perturbations_checked": cases})
    return summary


def product_boundary():
    families = [marginal_model(ds)[3] for ds in ((2,2),(2,3),(2,2,2),(3,3))]
    e = [[1,0,0,1],[0,1,1,0]]
    d = [[Q(1,2),0],[0,Q(1,2)],[0,Q(1,2)],[Q(1,2),0]]
    _, k, _, _ = marginal_model((2,2))
    b = [[Q(1,4)]+r for r in k]
    assert mul(mul(d,e),b) == b
    assert mul(d,e) != eye(4)
    return {"families": families, "two_by_two_reversible_outputs": 2}


def controller_reference():
    # The symmetric full table from section60.3, as specified in section84.1.
    def step(q, digit):
        kind, b = q
        if kind == 'S':
            return 'WG2', digit
        if kind in ('WF','WG1','WG2'):
            return {'WF':'F','WG1':'G','WG2':'WG1'}[kind], b
        if kind == 'H':
            return q
        offset = (digit-b) % 5
        if kind == 'G':
            return [('WF',b),('WG2',(b+2)%5),('H',5*((b+1)%5)+3),
                    ('H',5*((b+1)%5)+4),('WG2',(b+2)%5)][offset]
        return [('WF',(b-2)%5),('H',5*b+2),('H',5*((b+2)%5)),
                ('H',5*((b+2)%5)+1),('H',5*b)][offset]
    def rotate(q):
        kind, b = q
        return q if kind == 'S' else (kind,(b+(5 if kind == 'H' else 1)) % (25 if kind == 'H' else 5))
    traces, labels = [], defaultdict(set)
    for x in range(25):
        q, pos, reads, waits, trace = ('S',0), x, 0, 0, []
        for _ in range(30):
            trace.append(q)
            if q[0] != 'S':
                labels[q].add(x//5)
            if q[0] == 'H':
                assert q[1] == x
                break
            if q[0].startswith('W'):
                pos = (pos+1)%25
                waits += 1
                q = step(q,0)
            else:
                reads += 1
                q = step(q,pos//5)
        else:
            raise AssertionError('controller did not halt')
        assert trace[1] == ('WG2',x//5)
        traces.append((trace,reads,waits))
    pairs = {(q,r) for q, rs in labels.items() for r in rs}
    assert len(labels) == 50 and len(pairs) == 90
    # Complete unreachable digit slots equivariantly while retaining r.
    def lifted(q,r,digit):
        target = step(q,digit)
        return (target,r) if (target,r) in pairs else (('H',5*r),r)
    for q,r in pairs:
        assert (rotate(q),(r+1)%5) in pairs
        for digit in range(5):
            target, rr = lifted(q,r,digit)
            assert rr == r and (target,rr) in pairs
            assert lifted(rotate(q),(r+1)%5,(digit+1)%5) == (rotate(target),(rr+1)%5)
    for x,(trace,reads,waits) in enumerate(traces):
        q, pos, r, seen = ('S',0), x, None, []
        for _ in range(30):
            seen.append(q)
            if q[0] == 'H': break
            if q[0] == 'S':
                r=pos//5
                q=('WG2',r)
            elif q[0].startswith('W'):
                pos=(pos+1)%25
                q,r=lifted(q,r,0)
            else:
                q,r=lifted(q,r,pos//5)
        assert seen == trace
    assert labels[('WG2',0)] == {0,1,3}
    by_kind = Counter(q[0] for q,r in pairs)
    assert dict(by_kind) == {'F':10,'G':15,'WF':10,'WG1':15,'WG2':15,'H':25}
    # Conditional physical protocol: prepare the dial at x=(j+5*a)%25,
    # retain a externally, then execute the unchanged original controller.
    code, reachable, costs = set(), set(), []
    for a,j in product(range(5),range(12)):
        x=(j+5*a)%25
        trace,reads,waits=traces[x]
        halt=trace[-1][1]
        assert (halt-5*a)%25 == j
        code.add((halt,a))
        reachable.update((q,a) for q in trace)
        costs.append((reads,waits))
        shifted=traces[(x+5)%25][0]
        assert shifted == [rotate(q) for q in trace]
        assert ((halt+5)%25, (a+1)%5) == ((j+5*((a+1)%5))%25,(a+1)%5)
    assert len(code)==60
    return {"physical_inputs": 25, "original_states": 51, "first_read_acquires_high_digit": True,
            "prepared_source_protocol": {"source_configurations":60,
                "external_reference_labels":5, "used_halt_reference_pairs":len(code),
                "reachable_control_reference_pairs":len(reachable),
                "max_reads_after_preparation":max(r for r,w in costs),
                "max_unit_waits_after_preparation":max(w for r,w in costs),
                "scope":"Requires a source-dependent dial loader and an external record of a; their acquisition/preparation costs are not included."},
            "initial_reference_refinement_states": 91,
            "noninitial_refinement_by_kind": dict(by_kind),
            "max_reads": max(t[1] for t in traces), "max_unit_waits": max(t[2] for t in traces),
            "ambiguous_state": ['WG2',0], "possible_initial_references": [0,1,3],
            "full_noninitial_covariance_checks": len(pairs)*5,
            "scope": "91 is exact for the refinement retaining both original q and initial high digit; not a minimum over all controllers."}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result={"arithmetic":"exact integers and fractions", "probability":positive_encoding(),
            "generalizations":product_boundary(), "reference":controller_reference(),
            "scope":"No full two-archive operational equivalence, universal controller optimum, or complete Lean claim."}
    data=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output: args.output.write_text(data,encoding='utf-8')
    else: print(data,end='')


if __name__=='__main__':
    main()
