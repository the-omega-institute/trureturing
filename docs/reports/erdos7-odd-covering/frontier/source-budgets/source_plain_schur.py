#!/usr/bin/env python3
"""Exact certificates for the plain actual F_N square at every N >= 12.

Report339d proves the source-box and tail reductions. This module checks
their finite rational obligations, the source API, and the centered value.
It extends only a nonnegative comparison sum, never the actual source law.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True

L = F(11, 10)
S = F(101, 100)
TABLE = ((20, 27, 30), (33, 50, 47), (14, 20, 22), (21, 34, 33))
LEADING = ((F(881515, 708588), F(797159, 708588)),
           (F(375382, 177147), F(354293, 177147)))
INF = 'infinity'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def c(a, b, e):
    return F(TABLE[2*int(b > 0)+int(e > 0)][min(a, 3)-1])


def weight(a, b, e):
    return c(a, b, e)*L**a*S**(b+e)


def d(a, b, e):
    return F(1, 3**a*5**b*7**e)


def params(N):
    require(type(N) is int and N >= 12, 'Plain uniform source requires N>=12')
    return ((1-F(1, 3**(N-2)))/18, (1-F(1, 5**N))/4, (5+F(1, 7**N))/6)


def source_box():
    t, q, u = params(12)
    return tuple(product((t, F(1, 18)), (q, F(1, 4)), (F(5, 6), u)))


@lru_cache(None)
def coeff(a, bpos, epos, t, q, u, kind):
    """Centered or root0 upper moment divided by 3^-a 5^-b 7^-e."""
    require(a in (1, 2, 3) and kind in ('p', 'u'), 'Known moment class')
    if a == 1:
        eta = (F(1, 9)-t, F(1, 9), F(1, 9), F(1, 9), F(1, 9))
        ns = ((1-q)*eta[0], (1-q)/9, (1-3*q)/9, (1-2*q)/9, (1-2*q)/9-t*q)
        gs = (u-F(1, 7), u-F(2, 7), u, u, u)
        rows = (2, 3, 4) if kind == 'p' else (0, 1)
        return 3*sum((eta[j] if bpos else ns[j])*(1 if epos else gs[j]) for j in rows)
    if kind == 'p':
        return (1 if bpos else 1-2*q)*(1 if epos else u)
    # Maximum depth2 uses row3; deeper depths use path18. These are caps.
    return (1 if bpos else 1-q)*(1 if epos else u-(F(2, 7) if a == 2 else F(1, 7)))


def moment(a, b, e, t, q, u, kind):
    return d(a, b, e)*coeff(min(a, 3), b > 0, e > 0, t, q, u, kind)


def kernel(i, j, t, q, u):
    a, b, e = (max(x, y) for x, y in zip(i, j))
    return moment(a, b, e, t, q, u, 'p')+moment(a, b, e, t, q, u, 'u')


def finite_geom(r, low, high):
    if high < low:
        return F(0)
    return F(high-low+1) if r == 1 else (r**low-r**(high+1))/(1-r)


@lru_cache(None)
def axis(p, r, k, cls):
    """Sum p^(k-max(k,j))*r^(j-k) over a singleton or secondary tail."""
    if k == INF:
        return F(0) if cls == 'zero' or type(cls) is int else r/(r-1)+r/(p-r)
    if cls == 'zero':
        return r**(-k)
    if type(cls) is int:
        return F(1, p**max(0, cls-k))*r**(cls-k)
    require(cls in ('deep', 'pos'), 'Known secondary tail class')
    low = 3 if cls == 'deep' else 1
    if k < low:
        return F(p**k)*r**(-k)*(r/F(p))**low/(1-r/F(p))
    return r**(-k)*finite_geom(r, low, k)+r/(p-r)


@lru_cache(None)
def G(a, b, e, t, q, u):
    """Twelve-term infinite comparison row, with exact coordinate limits."""
    answer = F(0)
    for A, B, E in product((1, 2, 'deep'), ('zero', 'pos'), ('zero', 'pos')):
        ac = 3 if A == 'deep' else A
        target = max(3 if a == INF else min(a, 3), ac)
        bpos = b == INF or b > 0 or B == 'pos'
        epos = e == INF or e > 0 or E == 'pos'
        cap = sum(coeff(target, bpos, epos, t, q, u, kind) for kind in ('p', 'u'))
        answer += c(ac, int(B == 'pos'), int(E == 'pos'))*cap*axis(3, L, a, A)*axis(5, S, b, B)*axis(7, S, e, E)
    return answer


def hp(p, N, k):
    return F(k+1)+sum(F(1, p**j) for j in range(1, N-k+1))


def Hratio(N, a, b, e):
    """Exact H_i/d_i, including all a0 labels and their unit cross terms."""
    t, q, _ = params(N)
    if a >= 2:
        gamma = (F(5, 7) if a == 2 else F(6, 7)) if e == 0 else F(1)
        value = ((1-q)*hp(3, N, a)-gamma if b == 0
                 else hp(5, N, b)*(hp(3, N, a)-gamma))
        return value*(1 if e == 0 else hp(7, N, e))
    R1 = (3-4*q)/9-t*q if b == 0 else F(1, 3)
    R0 = F(11, 63)-6*t/7 if e == 0 else F(2, 9)-t
    T = sum(F(1, 3**j) for j in range(2, N+1))
    return 3*(2*R1-R0+T*((1-q) if b == 0 else 1))*(1 if b == 0 else hp(5, N, b))*(1 if e == 0 else hp(7, N, e))


@lru_cache(None)
def v(p, k):
    return F(k+1)+sum(F(1, p**j) for j in range(1, max(0, 12-k)+1))


def hlo(a, b, e):
    if a >= 2:
        gamma = (F(5, 7) if a == 2 else F(6, 7)) if e == 0 else F(1)
        return (F(3, 4)*v(3, a)-gamma if b == 0 else v(5, b)*(v(3, a)-gamma))*(1 if e == 0 else v(7, e))
    return LEADING[int(b > 0)][int(e > 0)]*(1 if b == 0 else v(5, b))*(1 if e == 0 else v(7, e))


def verify_grid(source_type):
    N = 12
    t, q, u = params(N)
    source = source_type(N, False)
    checks = 0
    for a, b, e in product(range(1, N+1), range(N+1), range(N+1)):
        for kind in ('p', 'u'):
            residue = 4 % 3**a if kind == 'p' else (0 if a == 1 else 3 if a == 2 else 18)
            actual = source.mass(a, residue, b, e)*source.haar_normalization
            require(moment(a, b, e, t, q, u, kind) == actual,
                    f'Actual source mass mismatch {(a, b, e, kind)}')
            checks += 1
    labels = tuple(product(range(N+1), repeat=3))
    samples = tuple((a, b, e) for a in (1, 2, 3, 7, 12)
                    for b, e in ((0, 0), (0, 12), (12, 0), (12, 12)))
    for a, b, e in samples:
        directH = sum(moment(max(a, A), max(b, B), max(e, E), t, q, u, 'p')
                      for A, B, E in labels)
        directH -= sum(moment(a, max(b, B), max(e, E), t, q, u, 'u')
                       for B, E in product(range(N+1), repeat=2))
        require(directH == d(a, b, e)*Hratio(N, a, b, e), f'H formula mismatch {(a, b, e)}')
        row = sum(kernel((a, b, e), j, t, q, u)*weight(*j) for j in labels if j[0] > 0)
        require(row/(d(a, b, e)*L**a*S**(b+e)) <= G(a, b, e, t, q, u),
                f'Infinite G fails to majorize {(a, b, e)}')
    best, best_at, count = F(-1), None, 0
    for tv, qv, uv in source_box():
        for a, b, e in product(range(1, 13), range(13), range(13)):
            h = hlo(a, b, e)
            require(h > 0, f'Nonpositive h {(a, b, e)}')
            ratio = G(a, b, e, tv, qv, uv)/(2*c(a, b, e)*h)
            if ratio > best:
                best, best_at = ratio, (a, b, e, tv, qv, uv)
            require(ratio <= F(49, 50), f'Grid failure {(a, b, e, tv, qv, uv, ratio)}')
            count += 1
    return dict(actual_source_entries=checks, direct_rows=len(samples), grid_checks=count,
                best_ratio=best, best_at=best_at, lambda_value=L, sigma_value=S,
                class_weights=TABLE, schur_ratio_upper=F(49, 50))


def verify_tail():
    t, q, _ = params(12)
    cap_count = 0
    for tv, qv, uv in source_box():
        for bp, ep in product((False, True), repeat=2):
            row0 = (F(1, 9)-tv)*(1 if bp else 1-qv)*(1 if ep else uv-F(1, 7))
            row3 = F(1, 9)*(1 if bp else 1-qv)*(1 if ep else uv-F(2, 7))
            require(row3 >= row0, 'Depth2 row3 cap')
            deep0 = (1 if bp else 1-qv)*(1 if ep else uv-F(1, 7))
            deep3 = (1 if bp else 1-qv)*(1 if ep else uv-F(2, 7))
            require(deep0 >= deep3, 'Deep path18 cap')
            cap_count += 2
    lows = []
    T = sum(F(1, 3**j) for j in range(2, 13))
    for bp, ep in product((False, True), repeat=2):
        values = []
        for tv, qv in product((t, F(1, 18)), (q, F(1, 4))):
            R1 = F(1, 3) if bp else (3-4*qv)/9-tv*qv
            R0 = F(2, 9)-tv if ep else F(11, 63)-6*tv/7
            values.append(3*(2*R1-R0+T*(1 if bp else 1-qv)))
        require(min(values) == LEADING[int(bp)][int(ep)], 'Depth1 exact corner minimum')
        lows.append(dict(positive_five=bp, positive_seven=ep, minimum=min(values)))
    tails = []
    for tv, qv, uv in source_box():
        for b, e in product((0, 1, INF), repeat=2):
            gamma = F(6, 7) if e == 0 else F(1)
            multiplier = F(3, 4) if b == 0 else F(1)
            shift = 1-gamma/multiplier
            gap = (13+shift)*G(12, b, e, tv, qv, uv)-(12+shift)*G(13, b, e, tv, qv, uv)
            require(gap > 0, f'a tail {(b, e, tv, qv, uv, shift, gap)}')
            tails.append(gap)
        for a, e in product((1, 2, 3, INF), (0, 1, INF)):
            gap = 14*G(a, 12, e, tv, qv, uv)-13*G(a, 13, e, tv, qv, uv)
            require(gap > 0, f'b tail {(a, e, tv, qv, uv, gap)}')
            tails.append(gap)
        for a, b in product((1, 2, 3, INF), (0, 1, INF)):
            gap = 14*G(a, b, 12, tv, qv, uv)-13*G(a, b, 13, tv, qv, uv)
            require(gap > 0, f'e tail {(a, b, tv, qv, uv, gap)}')
            tails.append(gap)
    require(len(tails) == 264, 'Tail endpoint count')
    return dict(root0_cap_checks=cap_count, depth1_corner_minima=lows,
                tail_checks=len(tails), min_tail_margin=min(tails),
                a_tail_shift='1-gamma/d; d=3/4 for b=0 and d=1 otherwise')


def value(t, q, u, J3, J5, J7):
    eta = (F(1, 9)-t, F(1, 9), F(1, 9), F(1, 9), F(1, 9))
    ns = ((1-q)*eta[0], (1-q)/9, (1-3*q)/9, (1-2*q)/9, (1-2*q)/9-t*q)
    gs = (u-F(1, 7), u-F(2, 7), u, u, u)
    B, E = J5-1, J7-1
    rows = [(n+B*et)*(g+E) for n, et, g in zip(ns, eta, gs)]
    Z = sum(n*g for n, g in zip(ns, gs))
    numerator = sum(rows)+3*sum(rows[i] for i in (2, 3, 4))+(J3-2)*(1-2*q+B)*(u+E)
    return numerator/Z


def centered_value(N):
    return value(*params(N), *(sum(F(2*k+1, p**k) for k in range(N+1)) for p in (3, 5, 7)))


def verify_value(source_type):
    rows = []
    for N in (12, 24):
        exact = centered_value(N)
        require(exact == source_type(N, False).centered_square(), f'Centered value mismatch N{N}')
        rows.append(dict(height=N, value=exact))
    limit = value(F(1, 18), F(1, 4), F(5, 6), *(F(p*(p+1), (p-1)**2) for p in (3, 5, 7)))
    require(limit == F(1829, 72), 'Exact centered limiting value')
    return dict(finite_values=rows, limit=limit)


def verify_all(source_type):
    return dict(scope='Plain actual F_N, every N>=12; the ordinary proof supplies source-box and exponent-tail reductions. Compressed layouts and their site/pair LP have a unique centered optimum; no arbitrary-source, weighted all-height, later-prime, or unrestricted covering conclusion.',
                grid=verify_grid(source_type), tail=verify_tail(), value=verify_value(source_type))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', required=True)
    parser.parse_args()
    path = Path(__file__).resolve().with_name('source_full_square.py')
    spec = importlib.util.spec_from_file_location('plain_schur_source', path)
    require(spec is not None and spec.loader is not None, 'Readable source API')
    source = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(source)
    print(json.dumps(verify_all(source.CompressedSource), default=str, indent=2))


if __name__ == '__main__':
    main()
