#!/usr/bin/env python3
"""Exact PG1 fourth-query redistribution checks; ordinary finite evidence only.

The all-height, all-layout inequality is established in the accompanying
ordinary proof. This consumer checks exact constants, full geometric series,
the pinned actual old source, literal new originals at heights 1 and 2,
unchanged source mass/caps, and a declared finite sample of full queries.
It does not enumerate the full query dictionary or compute its supremum.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from math import comb
from pathlib import Path


def need(ok, why):
    if not ok:
        raise ValueError(why)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def crt(a, d, b, power):
    return (a + d * (((b-a)*pow(d, -1, power)) % power)) % (d*power)


def prefix(e, final):
    return 15*(17**(e-1)-1)//16 + final*17**(e-1)


def geometric_power_sum(k, z):
    # Eulerian-number numerator: sum_(j>=1) j^k z^j.
    if k == 0:
        return z/(1-z)
    row = [1]
    for n in range(2, k+1):
        row = [(i+1)*(row[i] if i < len(row) else 0)
               +(n-i)*(row[i-1] if i else 0) for i in range(n)]
    return sum((a*z**(i+1) for i, a in enumerate(row)), F(0))/(1-z)**(k+1)


def polynomial_geometric(coefficients, z):
    return sum((a*geometric_power_sum(k, z)
                for k, a in enumerate(coefficients)), F(0))


def constants(mu0, mu2):
    z, t = F(1, 17), F(1, 2**20)
    tuple_cases = 0
    for k in range(1, 5):
        for j in range(7):
            actual = sum(min(v) == 0 and max(v) == j
                         for v in product(range(j+1), repeat=k))
            expected = 1 if j == 0 else (j+1)**k-2*j**k+(j-1)**k
            need(actual == expected, 'independent min/max exponent tuple count')
            tuple_cases += 1
    # N_k(j) for j>=1. This uses the tuple count just checked, not the
    # constants proposed in the proof.
    polys = ((0,), (2,), (0, 6), (2, 0, 12))
    R = tuple(1+polynomial_geometric(a, z) for a in polys)
    need(R == (F(1), F(9, 8), F(179, 128), F(1035, 512)), 'complete min/max series')
    M = 12**4*(1+17*polynomial_geometric((1, 4, 6, 4), z))
    C = 17*12**3*sum(comb(4, k)*R[k-1] for k in range(1, 5))
    need(M == F(13611483, 32) and C == F(4315977, 8), 'full root and recipient fourth moments')
    # Independent factor moment computation from the geometric PMF, using
    # the binomial expansion of (1+j)^4 and its unit j=0 term.
    PMF_moment = (1-z)*(1+sum(comb(4, k)*geometric_power_sum(k, z)
                              for k in range(5)))
    need(M == 12**4*(1+17*(PMF_moment-1)), 'independent geometric PMF fourth moment')
    epsilon = 3*mu0*t
    gaps = {'spoke': 15*mu2*F(14, 187), 'pure': F(15, 17),
            'spine': F(15, 289), 'split': 12*mu0/17}
    reserves = {name: g-mu0*t*M-epsilon for name, g in gaps.items()}
    need(all(g > 0 for g in reserves.values()), 'all exceptional complete-query cases have strict reserve')
    need(12-t*C == F(96347319, 8388608) > 0, 'deep-label cap gap pays the entire recipient gain')
    need(epsilon == F(49866777, 1048576007340032), 'uniform positive unnormalized gain')
    need(t < F(41, 952) and t/4 < F(1, 17), 'uniform actual root capacity and donor bounds')
    return dict(transfer=t, epsilon=epsilon, R=R, root_M4=M, recipient_C4=C,
                gap_lower_bounds=gaps, gap_reserves=reserves,
                deep_gap_reserve=12-t*C, tuple_count_cases=tuple_cases)


def make_geometry(H, points, old, divisors, mu, t):
    power = 17**H
    s, lam = F(1- F(1, power), 16), 1-F(1-F(1, power), 16)
    roots = (12, 13, 14, 15, 16) if H == 1 else (12, 13, 14, 16)
    originals = list(old)
    for e in range(1, H+1):
        pe = 17**e
        originals.append((pe, prefix(e, 0)))
        for j, d in enumerate(divisors[1:], 1):
            originals.append((d*pe, crt(2 % d, d, prefix(e, j), pe)))
    need(len(originals) == len({d for d, a in originals}) == 11+12*H,
         'every original full numerical modulus remains distinct')
    need(all(d > 1 and d % 2 and 0 <= a < d for d, a in originals), 'literal odd nonunit originals')
    rows = {}
    total, killed, candidate_total, candidate_killed, old_bad, candidate_bad = [F(0)]*6
    altered = point_checks = 0
    for x in points:
        n = sum(x % d == 2 % d for d in divisors[1:])
        bad_haar = n*s
        beta = max(F(0), bad_haar/lam-F(7, 15))/F(8, 15)
        c = 1/max(lam-bad_haar, lam*F(8, 15))
        bad_density = beta/bad_haar if bad_haar else F(0)
        categories = []
        row_total = row_candidate = row_bad = row_candidate_bad = F(0)
        for y in range(power):
            full = crt(x, 315, y, power)
            actual_bad = any(full % d == a for d, a in originals)
            pure_bad = any(y % (17**e) == prefix(e, 0) for e in range(1, H+1))
            mixed_bad = any(x % d == 2 % d and y % (17**e) == prefix(e, j)
                            for e in range(1, H+1)
                            for j, d in enumerate(divisors[1:], 1))
            need(actual_bad == (pure_bad or mixed_bad) and not (pure_bad and mixed_bad),
                 'literal CRT original union agrees with disjoint-prefix geometry')
            density = F(0) if pure_bad else bad_density if mixed_bad else c
            prob = density/power
            change = F(0)
            if x == 314:
                if y % 17 == 2:
                    change = t/(17**(H-1))
                elif y % 17 in roots:
                    change = -t/(len(roots)*17**(H-1))
            candidate = prob+change
            need(0 <= candidate <= F(15, 8)/(lam*power), 'modified global Haar cap and nonnegativity')
            if change:
                need(not actual_bad, 'all actual moved mass lies in the survivor set')
                altered += 1
            need(not actual_bad or candidate == prob, 'every original bad atom is unchanged')
            row_total += prob
            row_candidate += candidate
            row_bad += prob if actual_bad else 0
            row_candidate_bad += candidate if actual_bad else 0
            total += mu[x]*prob
            candidate_total += mu[x]*candidate
            old_bad += mu[x]*(prob if actual_bad else 0)
            candidate_bad += mu[x]*(candidate if actual_bad else 0)
            killed += mu[x]*(prob if not actual_bad else 0)
            candidate_killed += mu[x]*(candidate if not actual_bad else 0)
            categories.append(0 if pure_bad else 1 if mixed_bad else 2)
            point_checks += 1
        need(row_total == row_candidate == 1 and row_bad == row_candidate_bad == beta,
             'normalized rows and unchanged actual charge')
        rows[x] = dict(c=c, beta=beta, bad_density=bad_density, categories=categories)
    need(total == candidate_total == 1 and killed == candidate_killed
         and old_bad == candidate_bad == 1-killed, 'same physical and killed mass under the one law')
    need(killed >= F(len(roots), 17) and altered > 0, 'positive actual survivors and changed law')
    return dict(height=H, power=power, rows=rows, roots=roots, originals=originals,
                mass=killed, altered=altered, point_checks=point_checks)


def make_queries(H, divisors):
    queries = []
    for z in (0, 1, 2, 11, 12, 15, 16):
        for variant in range(3):
            q = {}
            for e in range(H+1):
                for d in divisors:
                    a = (314 if variant != 2 else 2) % d
                    b = 0 if e == 0 else z % (17**e)
                    if e == 1 and variant == 1 and d == 3:
                        b = (z+1) % 17
                    if e >= 2 and variant == 0 and d in (1, 3, 5, 15, 315):
                        b = (2+17*(d % 17)) % (17**e)
                    q[(d, e)] = (a, b)
            queries.append((f'root{z}-variant{variant}', q))
    for seed in range(5):
        q = {(d, e): ((19*seed+7*d+31*e) % d,
                      (37*seed+11*d+e*e) % (17**e))
             for e in range(H+1) for d in divisors}
        queries.append((f'deterministic{seed}', q))
    return queries


def evaluate_query(query, geometry, points, divisors, mu, t, aligned=False):
    H, power, rows, roots = (geometry[k] for k in ('height', 'power', 'rows', 'roots'))
    physical = killed = U = US = perturbation = F(0)
    for x in points:
        active = [(e, (12 if aligned and e else b))
                  for (d, e), (a, b) in query.items() if x % d == a]
        A = [sum(e == j for e, b in active) for j in range(H+1)]
        need(A[0] >= 1 and all(1 <= a <= 12 for a in A), 'mandatory unit old slot at every depth')
        running = A[0]
        extension = F(0)
        for e in range(1, H+1):
            extension += F((running+A[e])**4-running**4, 17**e)
            running += A[e]
        c, beta, bd, categories = (rows[x][k] for k in ('c', 'beta', 'bad_density', 'categories'))
        U += mu[x]*(A[0]**4+c*extension)
        US += mu[x]*((1-beta)*A[0]**4+c*extension)
        moments = [0, 0, 0]
        root_moments = [0]*17
        for y, category in enumerate(categories):
            load = sum(y % (17**e) == b for e, b in active)
            fourth = load**4
            moments[category] += fourth
            root_moments[y % 17] += fourth
        physical += mu[x]*(bd*moments[1]+c*moments[2])/power
        killed += mu[x]*c*moments[2]/power
        if x == 314:
            perturbation = mu[x]*t*(F(root_moments[2], 17**(H-1))
                              -F(sum(root_moments[r] for r in roots), len(roots)*17**(H-1)))
    return physical, killed, U, US, perturbation


def run(report_root):
    io_path = report_root/'certificate_io.py'
    spec = importlib.util.spec_from_file_location('e7_quartic_certificate_io', io_path)
    io = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(io)
    source_path = report_root/'certificates/mod3_conditioned_geometry_certificate.json'
    raw = io.read_artifact_bytes(source_path)
    need(sha256(raw).hexdigest() == '9a0e265a456ab133389202abd5ef91ac6826957f74c24b1e8bd055a97cea0a0a',
         'pinned complete PG1 logical source')
    cases = [r for r in json.loads(raw)['cases'] if r['name'] == 'PG1']
    need(len(cases) == 1, 'one actual PG1 case')
    source = cases[0]
    points, weights, denominator = (source[k] for k in ('points', 'weight_numerators', 'weight_denominator'))
    old = [tuple(x) for x in source['family']]
    divisors = [d for d in range(1, 316) if 315 % d == 0]
    need(sorted(d for d, a in old) == divisors[1:], 'complete old numerical labels')
    need(points == [x for x in range(315) if all(x % d != a for d, a in old)]
         and len(points) == len(weights) == 75, 'literal old survivors')
    need(denominator == 1000000007 and sum(weights) == denominator and min(weights) > 0,
         'one full-support PG1 probability')
    mu = dict(zip(points, (F(w, denominator) for w in weights)))
    need(mu[2] == F(13119398, denominator) and mu[314] == F(16622259, denominator), 'selected old masses')
    c = constants(mu[314], mu[2])
    fixtures = []
    for H in (1, 2):
        g = make_geometry(H, points, old, divisors, mu, c['transfer'])
        query_results = []
        for name, query in make_queries(H, divisors):
            V, W, U, US, delta = evaluate_query(query, g, points, divisors, mu, c['transfer'])
            Va, Wa, Ua, USa, unused = evaluate_query(query, g, points, divisors, mu, c['transfer'], aligned=True)
            need(Va == U == Ua and Wa == US == USa, 'one simultaneous clean layout attains both cap values')
            need(V <= U and W <= US, 'baseline query is bounded by its same-layout cap')
            need(V+delta <= U-c['epsilon'] and W+delta <= US-c['epsilon'],
                 'literal arbitrary-phase sample has the claimed physical and killed uniform gap')
            query_results.append(dict(name=name, physical=V, killed=W, same_law_delta=delta,
                                      physical_gap=U-V-delta, killed_gap=US-W-delta))
        fixtures.append(dict(height=H, full_period=315*g['power'], original_classes=g['originals'],
                             complete_query_label_count=12*(H+1), literal_point_checks=g['point_checks'],
                             changed_survivor_points=g['altered'], old_and_new_survivor_mass=g['mass'],
                             normalized_fourth_gap=c['epsilon']/g['mass'], query_checks=query_results))
    return encode(dict(schema='e7-pg1-quartic-gain-check-v1',
                       mathematical_scope='Fixed pinned PG1 and center2 17-adic comb; all-height/full-query theorem is an ordinary proof, not finite enumeration or Lean.',
                       source_logical_sha256=sha256(raw).hexdigest(), constants=c,
                       literal_geometry_fixtures=fixtures, finite_complete_query_samples=sum(len(x['query_checks']) for x in fixtures),
                       lean_verification=False, general_family_gain=False, source779_identification=False))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report-root', type=Path,
                        default=Path(__file__).resolve().parents[3])
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = run(args.report_root)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    else:
        need(result == json.loads(Path(__file__).with_suffix('.json').read_text()),
             'Retained quartic result agrees with fresh exact reconstruction')
    print('PASS: exact quartic constants, min/max tuple sums, actual source/caps, and finite complete-query samples.')
