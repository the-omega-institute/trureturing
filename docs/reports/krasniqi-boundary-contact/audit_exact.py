"""Exact, dependency-free audit of the Krasniqi polynomial certificate.

The q coefficients are obtained by multiplying truncated exponential series,
not by the source recurrence. All operations use fractions and sparse powers.
Certificate inputs are read-only. The exact result is printed as JSON.
"""
from fractions import Fraction as Q
from math import comb, factorial
from itertools import product
from functools import lru_cache
from pathlib import Path
import json

import argparse

if not __debug__:
    raise SystemExit("verification requires assertions: run Python without -O")
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--certificate-dir", type=Path,
                    default=Path(__file__).resolve().parent,
                    help="directory containing P6-certificate.json and tail-certificate.json")
ROOT = parser.parse_args().certificate_dir


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON key: " + key)
        result[key] = value
    return result


def load_certificate(name):
    cert = json.loads((ROOT / (name + "-certificate.json")).read_text(encoding="utf-8"),
                      object_pairs_hook=unique_object,
                      parse_constant=lambda value: (_ for _ in ()).throw(
                          ValueError("non-finite JSON constant: " + value)))
    if not isinstance(cert, dict) or set(cert) != {"report", "leaves"}:
        raise ValueError("certificate must have exactly report and leaves")
    leaves = cert["leaves"]
    if not isinstance(leaves, list) or not leaves:
        raise ValueError("certificate leaves must be a nonempty list")
    for leaf in leaves:
        if not isinstance(leaf, list) or len(leaf) < 2 or not isinstance(leaf[0], str):
            raise ValueError("malformed leaf")
        path, mode = leaf[:2]
        if len(path) % 2 or len(path) > 128 or any(
                ax not in "012" or side not in "LR"
                for ax, side in zip(path[::2], path[1::2])):
            raise ValueError("malformed bisection path")
        if mode == "positive":
            if len(leaf) != 2:
                raise ValueError("positive leaf must have exactly two fields")
        elif mode == "exclude":
            if len(leaf) != 3 or type(leaf[2]) is not int or leaf[2] not in (1, 2, 3):
                raise ValueError("invalid exclusion label")
        else:
            raise ValueError("unknown leaf mode")
    if name == "tail" and leaves != [["", "positive"]]:
        raise ValueError("tail must certify the entire parameter rectangle")
    report = cert["report"]
    expected = dict(name=name, nodes=2*len(leaves)-1,
                    positive_leaves=sum(x[1] == "positive" for x in leaves),
                    excluded_leaves=sum(x[1] == "exclude" for x in leaves),
                    maxdepth=max(len(x[0])//2 for x in leaves), fail=None)
    if report != expected:
        raise ValueError("certificate metadata disagrees with its leaves")
    return cert


certificates = {name: load_certificate(name) for name in ("P6", "tail")}
ZERO = (0, 0, 0)

def scalar(x):
    return {ZERO: Q(x)} if x else {}

def add(*ps):
    ans = {}
    for p in ps:
        for e, v in p.items():
            ans[e] = ans.get(e, Q(0)) + v
    return {e: v for e, v in ans.items() if v}

def scale(p, c):
    return {e: v*c for e, v in p.items() if v*c}

def mul(p, q):
    ans = {}
    for e, v in p.items():
        for f, w in q.items():
            g = tuple(x+y for x, y in zip(e, f))
            ans[g] = ans.get(g, Q(0)) + v*w
    return {e: v for e, v in ans.items() if v}

def power(p, n):
    ans = scalar(1)
    for _ in range(n):
        ans = mul(ans, p)
    return ans

def deriv(p, ax):
    ans = {}
    for e, v in p.items():
        if e[ax]:
            f = list(e); f[ax] -= 1
            ans[tuple(f)] = v*e[ax]
    return ans

def specialize(p, ax, x):
    ans = {}
    for e, v in p.items():
        f = list(e); f[ax] = 0
        ans[tuple(f)] = ans.get(tuple(f), Q(0)) + v*x**e[ax]
    return {e: v for e, v in ans.items() if v}

a = {(1, 0, 0): Q(1)}
c = {(0, 1, 0): Q(1)}
t = {(0, 0, 1): Q(1)}
# Product_j exp((a/(j+1)+c/j) z^j), truncated at z^9.
q = [scalar(1)] + [{} for _ in range(9)]
for j in range(1, 10):
    ell = add(scale(a, Q(1, j+1)), scale(c, Q(1, j)))
    nq = [{} for _ in range(10)]
    for n in range(10):
        for m in range(n//j+1):
            nq[n] = add(nq[n], scale(mul(q[n-j*m], power(ell, m)), Q(1, factorial(m))))
    q = nq
# Check literal recurrence independently after construction.
for n in range(1, 10):
    rhs = {}
    for j in range(1, n+1):
        rhs = add(rhs, mul(add(scale(a, Q(j, j+1)), c), q[n-j]))
    assert q[n] == scale(rhs, Q(1, n))
assert q[1] == add(scale(a, Q(1, 2)), c)
assert q[2] == add(scale(a, Q(1, 3)), scale(c, Q(1, 2)), scale(power(q[1], 2), Q(1, 2)))
d = [add(*(scale(q[j+1], Q((-1)**j*comb(n, j))) for j in range(n+1))) for n in range(9)]
km2 = add(a, c, scalar(-2))
km1 = add(a, c, scalar(-1))
sumr_times_a = add(scale(a, 2), scale(c, 2), scalar(-3))
J = [add(mul(power(a, 2), d[i+2]), scale(mul(mul(a, sumr_times_a), d[i+1]), -1), mul(mul(km2, km1), d[i])) for i in range(7)]
P = add(*(scale(mul(J[i], power(t, i)), Q(1, factorial(i))) for i in range(7)))
T = specialize(deriv(P, 2), 2, Q(16))
d0 = Q(1295836866004, 10**12)
B = add(a, scale(c, 4))
A = add(scale(a, d0), scale(c, 4))
M = add(scale(mul(A, add(scale(a, 5), scale(c, 26))), 2), scale(power(B, 2), -8), scale(mul(power(A, 2), B), -1), scalar(Q(1, 10**9)))
U = add(scalar(4), scale(c, -4), scale(power(add(a, scale(c, 2), scalar(-2)), 2), -1))

def degree(p):
    return tuple(max(e[j] for e in p) for j in range(3))

@lru_cache(None)
def affine_bern_matrix(n, lo, hi):
    # Entry (i,j) is the Bernstein coefficient of (lo+(hi-lo)u)^j.
    return tuple(tuple(sum(Q(comb(i, h), comb(n, h))*comb(j, h)*lo**(j-h)*(hi-lo)**h
                           for h in range(min(i, j)+1)) for j in range(n+1)) for i in range(n+1))

def check_affine_identity(n, lo, hi):
    # Re-expand each Bernstein column, proving the affine monomial identity
    # coefficient-by-coefficient; this also checks the conversion at endpoints.
    mat = affine_bern_matrix(n, lo, hi)
    for j in range(n+1):
        for k in range(n+1):
            got = sum(mat[i][j]*comb(n, i)*comb(n-i, k-i)*(-1)**(k-i)
                      for i in range(k+1))
            expected = Q(comb(j, k))*lo**(j-k)*(hi-lo)**k if k <= j else Q(0)
            assert got == expected, (n, lo, hi, j, k, got, expected)

def bern(p, box):
    ns = degree(p)
    # Linear transformations in each coordinate, with a dense final tensor.
    tensor = dict(p)
    for ax in range(3):
        mat = affine_bern_matrix(ns[ax], *box[ax])
        nxt = {}
        others = [j for j in range(3) if j != ax]
        for rest in product(*(range(ns[j]+1) for j in others)):
            e = [0, 0, 0]
            for j, v in zip(others, rest): e[j] = v
            row = []
            for j in range(ns[ax]+1):
                e[ax] = j; row.append(tensor.get(tuple(e), Q(0)))
            for i in range(ns[ax]+1):
                e[ax] = i
                nxt[tuple(e)] = sum(mat[i][j]*row[j] for j in range(ns[ax]+1))
        tensor = nxt
    return tensor

def decode(path):
    assert len(path) % 2 == 0
    box = [(Q(1), Q(7, 3)), (Q(0), Q(1)), (Q(0), Q(16))]
    for ax, side in zip(path[::2], path[1::2]):
        assert ax in '012' and side in 'LR'
        k = int(ax); lo, hi = box[k]; mid = (lo+hi)/2
        box[k] = (lo, mid) if side == 'L' else (mid, hi)
    return tuple(box)

def coverage(paths):
    # Prefix-free full binary tree; closed children cover the closed parent,
    # including the split face. Verify every leaf is reached exactly once.
    assert len(paths) == len(set(paths))
    reached = set()
    def visit(prefix, below):
        if prefix in paths:
            assert below == [prefix]
            reached.add(prefix); return
        assert below
        axes = {p[len(prefix)] for p in below}
        assert len(axes) == 1
        axis = next(iter(axes)); assert axis in '012'
        for side in 'LR':
            child = prefix+axis+side
            visit(child, [p for p in below if p.startswith(child)])
    visit('', list(paths)); assert reached == set(paths)

rho = Q(6583, 11943936)
tail_margin = Q(45599851, 571536000)
reports = []
for certificate in certificates.values():
    coverage([leaf[0] for leaf in certificate['leaves']])
for name, poly, target in [('P6', P, rho), ('tail', T, tail_margin)]:
    cert = certificates[name]
    leaves = cert['leaves']; coverage([x[0] for x in leaves])
    positive = excluded = 0; minimum = None; exclusions = {}; exclusion_upper_bounds = {}
    for leaf in leaves:
        path, mode = leaf[:2]; box = decode(path)
        if mode == 'positive':
            bs = bern(poly, box); lo = min(bs.values())
            assert lo >= target > 0, (name, path, lo)
            minimum = lo if minimum is None else min(minimum, lo)
            positive += 1
        else:
            assert mode == 'exclude' and leaf[2] in [1, 2, 3]
            pred = [None, M, U, km2][leaf[2]]
            hi = max(bern(pred, box).values())
            assert hi < 0, (name, path, hi)
            excluded += 1
            exclusions[str(leaf[2])] = exclusions.get(str(leaf[2]), 0)+1
            label = str(leaf[2])
            exclusion_upper_bounds[label] = max(hi, exclusion_upper_bounds.get(label, hi))
    assert minimum == target
    reports.append(dict(name=name, leaves=len(leaves), positive=positive, excluded=excluded,
                        exclusion_types=exclusions,
                        exclusion_upper_bounds={key: str(value) for key, value in exclusion_upper_bounds.items()},
                        minimum=str(minimum),
                        maxdepth=max(len(x[0])//2 for x in leaves),
                        prefix_free_complete_closed_partition=True))

L = 2*sum(Q(1, 2)**(2*n+1)/Q(2*n+1) for n in range(24))
rem = 2*Q(1, 2)**49/Q(49)/(1-Q(1, 4))
assert d0-Q(1, 10**12) < 3*L-2 < 3*(L+rem)-2 < d0+Q(1, 10**12)
assert Q(1) < 3*L-2 and 3*(L+rem)-2 < Q(13, 10)
lip = 2*Q(7, 3)*(5*Q(7, 3)+26)+2*Q(7, 3)*(Q(13, 10)*Q(7, 3)+4)*(Q(7, 3)+4)
assert lip < 500
assert 500*Q(1, 10**12) < Q(1, 10**9)
# Every coordinate interval used by each checked polynomial is audited.
checked_matrices = set()
for name, poly in [('P6', P), ('tail', T)]:
    cert = certificates[name]
    for leaf in cert['leaves']:
        pred = poly if leaf[1] == 'positive' else [None, M, U, km2][leaf[2]]
        ns = degree(pred)
        for ax, (lo, hi) in enumerate(decode(leaf[0])):
            key = (ns[ax], lo, hi)
            if key not in checked_matrices:
                check_affine_identity(*key); checked_matrices.add(key)

data = dict(polynomial_degrees=list(degree(P)), polynomial_terms=len(P),
            q_generation='product of truncated exponential series through degree 9',
            recurrence_and_q1_q2_verified=True,
            log3_lower=str(L), log3_upper=str(L+rem), d0=str(d0),
            derivative_M_bound=str(lip),
            affine_Bernstein_identities_verified=len(checked_matrices),
            certificates=reports)
print(json.dumps(data))
