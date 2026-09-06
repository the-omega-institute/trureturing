#!/usr/bin/env python3
"""Exact rational circular-cap enclosures for a (6,6,6,2) MUB constellation.

Reuses the actual signed-Cayley centers, exhaustive clique enumerator and
sublevel-cover engine. No stored PASS, old graph masks, numerical angle,
floating-point optimizer or root-uniqueness claim is used in acceptance.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction as F
from math import isqrt
from pathlib import Path
import hashlib
import itertools
import json
import subprocess
import check_real_x_two_relation as prior

Z = tuple[F, F]
N = 60
RADIUS = F(1, 16)
TAU = F(1, 256)
ETA = TAU * TAU
SUBLEVEL = F(1, 128)
SIGMA = F(3, 4096)
SAME = F(3, 4)


def require(ok: bool, text: str) -> None:
    if not ok:
        raise ValueError(text)


def add(a: Z, b: Z) -> Z:
    return a[0] + b[0], a[1] + b[1]


def neg(a: Z) -> Z:
    return -a[0], -a[1]


def conj(a: Z) -> Z:
    return a[0], -a[1]


def mul(a: Z, b: Z) -> Z:
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]


def dot(a: Z, b: Z) -> F:
    return a[0]*b[0]+a[1]*b[1]


def cross(a: Z, b: Z) -> F:
    return a[0]*b[1]-a[1]*b[0]


def cayley(t: F, sign: int) -> Z:
    require(sign in (-1, 1), 'invalid Cayley sign')
    return sign*(1-t*t)/(1+t*t), sign*2*t/(1+t*t)


def sqrt_upper(x: F) -> F:
    require(x >= 0, 'negative square root')
    r = isqrt((x.numerator << 128)//x.denominator)
    upper = F(r+1, 1 << 64)
    require(upper*upper >= x, 'integer square-root certificate failed')
    return upper


def arc_upper(lo: Z, hi: Z, g: Z) -> F:
    """Verify an endpoint dual, or fall back to the certified Cauchy bound.

For |z|=|e|=1 and a.z>=h, g=lambda*e-mu*a gives
  (lambda-mu*h)-g.z = lambda/2*|z-e|^2 + mu*(a.z-h).
Both multipliers must be nonnegative. Here a=lo+hi, h=1+lo.hi.
"""
    require(dot(lo, lo) == dot(hi, hi) == 1, 'nonunit arc endpoint')
    require(cross(lo, hi) > 0 and dot(lo, hi) > 0, 'not an oriented short arc')
    a = add(lo, hi)
    h = 1+dot(lo, hi)
    bounds = [sqrt_upper(dot(g, g))]
    for e in (lo, hi):
        den = cross(e, a)
        require(den != 0, 'degenerate endpoint dual')
        mu = -cross(e, g)/den
        lam = dot(e, g)+mu*h
        if mu >= 0 and lam >= 0:
            require((lam*e[0]-mu*a[0], lam*e[1]-mu*a[1]) == g,
                    'endpoint dual vector identity failed')
            bounds.append(lam-mu*h)
    return min(bounds)


def projection(lo: Z, hi: Z, g: Z) -> tuple[F, F]:
    return -arc_upper(lo, hi, neg(g)), arc_upper(lo, hi, g)


def relative_arc(t: F, tsign: int, s: F, ssign: int,
                 radius: F) -> tuple[Z, Z]:
    """Certify that all relative phases lie on the chosen minor arc.

q/lo is Cayley(k1)*Cayley(k2) with k1,k2>=0 and k1*k2<1.
The same check for hi/q proves both wedge inequalities without angles.
"""
    require(radius > 0, 'nonpositive radius')
    tl, th, sl, sh = t-radius, t+radius, s-radius, s+radius
    pairs = [(min(1+th*tl, 1+th*th), min(1+sl*sl, 1+sl*sh)),
             (min(1+tl*tl, 1+tl*th), min(1+sh*sl, 1+sh*sh))]
    for a, b in pairs:
        require(a > 0 and b > 0 and (th-tl)*(sh-sl) < a*b,
                'Cayley arc membership guard failed')
    lo = mul(conj(cayley(th, tsign)), cayley(sl, ssign))
    hi = mul(conj(cayley(tl, tsign)), cayley(sh, ssign))
    require(cross(lo, hi) > 0 and dot(lo, hi) > 0, 'minor-arc guard failed')
    return lo, hi


def square_range(interval: tuple[F, F]) -> tuple[F, F]:
    lo, hi = interval
    require(lo <= hi, 'inverted interval')
    return (F(0) if lo <= 0 <= hi else min(lo*lo, hi*hi), max(lo*lo, hi*hi))


def overlap_bounds(x, y, radius: F = RADIUS) -> tuple[F, F]:
    arcs = []
    center = (F(1), F(0))
    for (t, tsign), (s, ssign) in zip(x, y):
        arcs.append(relative_arc(t, tsign, s, ssign, radius))
        center = add(center, mul(conj(cayley(t, tsign)), cayley(s, ssign)))
    directions = [(F(1), F(0))]
    if center != (0, 0):
        directions.append(center)
    lower, upper = F(0), F(1)
    for g in directions:
        ig = (-g[1], g[0])
        real = [g[0], g[0]]
        imag = [ig[0], ig[0]]
        for lo, hi in arcs:
            r, s = projection(lo, hi, g), projection(lo, hi, ig)
            real = [real[j]+r[j] for j in (0, 1)]
            imag = [imag[j]+s[j] for j in (0, 1)]
        r, s = square_range(tuple(real)), square_range(tuple(imag))
        denominator = 36*dot(g, g)
        require(denominator > 0, 'zero observation direction')
        lower = max(lower, (r[0]+s[0])/denominator)
        upper = min(upper, (r[1]+s[1])/denominator)
    require(lower <= upper, 'inconsistent overlap bounds')
    scale = 1 << 60
    return (F(lower.numerator*scale//lower.denominator, scale),
            F(-((-upper.numerator*scale)//upper.denominator), scale))


def read_centers(path: Path):
    lines = path.read_text().splitlines()
    require(len(lines) == N+1 and lines[0] == str(N), 'incomplete centers')
    out = {}
    for line in lines[1:]:
        nums = list(map(int, line.split()))
        require(len(nums) == 7, 'invalid center row')
        i, mask, *values = nums
        require(0 <= i < N and i not in out and 0 <= mask < 32, 'invalid center label')
        out[i] = [(F(t, 1 << 40), 1-2*((mask >> j) & 1)) for j, t in enumerate(values)]
    require(set(out) == set(range(N)), 'missing center')
    return [out[i] for i in range(N)]


def relations(centers):
    A, B, bounds = [0]*N, [0]*N, []
    same_lower = F(1)
    for i, j in itertools.combinations_with_replacement(range(N), 2):
        lo, hi = overlap_bounds(centers[i], centers[j])
        bounds.append([i, j, str(lo), str(hi)])
        if i == j:
            same_lower = min(same_lower, lo)
            require(lo > SAME, 'same-tube lower bound failed')
        elif lo < ETA:
            A[i] |= 1 << j
            A[j] |= 1 << i
        if lo <= F(1, 6)+TAU and hi >= F(1, 6)-TAU:
            B[i] |= 1 << j
            B[j] |= 1 << i
    return A, B, bounds, same_lower


def audit_partners(A, B):
    cliques = prior.enumerate_six_cliques(A)
    sets = set()
    nonempty = 0
    for clique in cliques:
        common = (1 << N)-1
        for v in clique:
            common &= B[v]
        require(common.bit_count() <= 1, 'a first clique has multiple partner tubes')
        sets.add(common)
        nonempty += bool(common)
    return cliques, sets, nonempty


def audit_cover(reports):
    require(len(reports) == 32 and {r.get('chart') for r in reports} == set(range(32)),
            'missing or duplicate chart')
    for r in reports:
        require(r.get('status') == 'SUBLEVEL_COVERED' and r.get('pending') == 0 and
                r.get('unresolved') == 0, 'incomplete cover')
        require((r.get('epsilon_bits'), r.get('guard_radius_bits'), r.get('dyadic_bits')) ==
                (7, 4, 40), 'wrong cover parameters')
        require(r.get('tube_uniqueness_checked') is False and
                r.get('max_guard_contraction_dyadic') is None, 'wrong tube semantics')
    return {'charts': 32, 'nodes': sum(r['nodes'] for r in reports),
            'pending': 0, 'unresolved': 0, 'root_uniqueness_used': False}


def run(centers_path: Path, output: Path, full: bool, jobs: int) -> dict:
    require(1 <= jobs <= 32, 'invalid worker count')
    output.mkdir(parents=True, exist_ok=True)
    (output/'verification.json').unlink(missing_ok=True)
    (output/'failure.json').unlink(missing_ok=True)
    centers = read_centers(centers_path)
    A, B, bounds, same_lower = relations(centers)
    cliques, sets, nonempty = audit_partners(A, B)
    budget = TAU+SIGMA*(5+SIGMA)
    require(TAU <= F(1, 4) and budget < SUBLEVEL and ETA < SAME, 'invalid scalar budget')
    report = {'status': 'FINITE_ARC_CERTIFICATE_VERIFIED', 'tube_radius': str(RADIUS),
        'sublevel': str(SUBLEVEL), 'tau': str(TAU), 'internal_squared_overlap_tolerance': str(ETA),
        'same_tube_squared_overlap_lower': str(same_lower), 'column_l1_radius': str(SIGMA),
        'entrywise_radius': str(SIGMA/6), 'transferred_residual_upper': str(budget),
        'orthogonal_edges': sum(v.bit_count() for v in A)//2,
        'unbiased_edges': sum(v.bit_count() for v in B)//2,
        'first_six_cliques': len(cliques), 'distinct_partner_sets': len(sets),
        'partner_union': list(prior.vertices(sum(sets))), 'first_cliques_with_partner': nonempty,
        'maximum_partner_cardinality': max(map(int.bit_count, sets), default=0),
        'conditional_partial_constellation_merit_gap': str(ETA),
        'candidate_sizes': [6, 2], 'global_cover_replayed': False, 'lean_kernel_verified': False}
    (output/'overlap_bounds.json').write_text(json.dumps(bounds)+'\n')
    (output/'finite_certificate.json').write_text(json.dumps({'orthogonal_masks': A,
        'unbiased_masks': B, 'first_cliques': cliques, 'partner_sets': sorted(sets)})+'\n')
    directory = Path(__file__).resolve().parent
    if full:
        source = directory/'check_real_x_residual_barrier.cpp'
        binary = (output/'sublevel').resolve()
        subprocess.run(['g++','-O3','-std=c++17','-Wall','-Wextra',str(source),'-o',str(binary)],check=True)
        def one(k):
            target = (output/f'chart_{k:02d}.json').resolve()
            target.unlink(missing_ok=True)
            subprocess.run([str(binary), str(centers_path.resolve()), str(k), '1500000',
                '7', '4', str(target), '--raw-tube-cover'],check=True,stdout=subprocess.DEVNULL)
            return json.loads(target.read_text())
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            reports = list(pool.map(one, range(32)))
        report['coverage'] = audit_cover(reports)
        report['global_cover_replayed'] = True
        report['status'] = 'COMPUTATIONAL_PARTIAL_CONSTELLATION_EXCLUSION'
    dependencies = [Path(__file__), centers_path, directory/'check_real_x_two_relation.py',
        directory/'check_real_x_residual_barrier.cpp',directory/'check_real_x_global_cover.cpp']
    report['sha256'] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in dependencies}
    (output/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('centers',type=Path)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--full-cover',action='store_true')
    p.add_argument('--jobs',type=int,default=4)
    a = p.parse_args()
    try:
        print(json.dumps(run(a.centers,a.output,a.full_cover,a.jobs),indent=2))
    except Exception as exc:
        a.output.mkdir(parents=True,exist_ok=True)
        (a.output/'verification.json').unlink(missing_ok=True)
        (a.output/'failure.json').write_text(json.dumps({'status':'FAIL','error':str(exc)})+'\n')
        raise
