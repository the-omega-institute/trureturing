#!/usr/bin/env python3
"""Exact controls for the branch-asymmetric, fourth-height conditional lift.

Requires Python 3.9+ and its standard library. Writes the requested JSON result.
Canonical placement: branch_asymmetric_height_four.py, next to its two pinned
JSON dependencies. From another directory, pass --source-dir. All mathematical
comparisons use Fraction; float values are display-only. The ordinary proof
supplies arbitrary-family, all-height and same-source moment quantifiers.
No optimizer, Lean run, or unrestricted covering conclusion is supplied here.
"""
from argparse import ArgumentParser
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import gcd, lcm, prod
from pathlib import Path
import json

SOURCE_DIGESTS = {
    'height_three_clipping_envelope.json':
        '276d7e266a86ed8e5a1c9da2982b219725c2738bc4ad19da1243bf8575543685',
    'four_level_query_hinge_lift.json':
        'b224c79716585f16b52aeda277810a1a001a4f2d92d3e092cfc1cc41345dbcfd',
}
Q = (5, 7, 11, 13, 17, 19)
P = (3,) + Q


def positive(x):
    return max(F(0), x)


def crt(a, m, b, n):
    if gcd(m, n) != 1:
        raise ValueError('CRT inputs must be coprime')
    return (a + m * (((b - a) * pow(m, -1, n)) % n)) % (m * n)


def exact(x):
    return {'exact': str(x), 'decimal': float(x)}


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    checks = []
    controls = {}

    def need(name, condition):
        if not condition:
            raise ValueError('FAILED: ' + name)
        checks.append(name)

    sources = {}
    provenance = []
    for name, expected in SOURCE_DIGESTS.items():
        raw = (args.source_dir / name).read_bytes()
        actual = sha256(raw).hexdigest()
        need('pinned source digest ' + name, actual == expected)
        sources[name] = json.loads(raw)
        provenance.append({'path': name, 'sha256': actual})
    env = sources['height_three_clipping_envelope.json']
    fh = sources['four_level_query_hinge_lift.json']
    B = F(env['B'])
    target = F(env['target'])
    K3 = max(F(c['K_integer'][3]) for c in env['corners'])
    K7 = max(F(c['K_integer'][7]) for c in env['corners'])
    alpha = min(F(c['alpha']['exact']) for c in fh['corners'])
    need('both existing producers supply the same B', B == F(fh['B']['exact']))
    need('both existing producers supply the same K3', K3 == F(fh['K']['exact']))
    need('all four source-mass corners agree between producers',
         {F(c['alpha']) for c in env['corners']} ==
         {F(c['alpha']['exact']) for c in fh['corners']})
    need('four complete pure-mass corners are retained',
         {(F(c['x']), F(c['y'])) for c in env['corners']} ==
         set(product((F(1, 2), F(1)), (F(2, 3), F(1)))))
    need('K7 is the maximum of the four exact source corners',
         K7 == F(6258510165289233442029877862409645975916115839,
                 7807154349055719001167517219171937585855811250))
    need('positive source constants and exact continuation target',
         B > 0 and K3 > 0 and K7 > 0 and alpha > 0 and target == F(566, 49))

    w = F(1, 2)
    tA, tB = F(1), F(7)
    kA, kB = 1 - tA / 12, 1 - tB / 18
    lamA, lamB = w / (12 - tA), (1 - w) / (18 - tB)
    need('strictly positive branch clips', kA == F(11, 12) and kB == F(11, 18))
    need('equal branch loss coefficients', lamA == lamB == F(1, 22))
    need('equal complete deep-query coefficients',
         F(3, 4) * w / kA == F(1, 2) * (1 - w) / kB == F(9, 22))
    need('shallow root plus deep coefficient is ten elevenths',
         max(w, 1 - w) + F(9, 22) == F(10, 11))
    N = B + F(10, 11) * (1 + B)
    loss0 = K3 / 66 + K7 / 22
    rho_star = 33 * (1 - N / target - loss0)
    Gamma_star = 22 * (1 - N / target) - K7
    reciprocal_star = alpha * rho_star / 9
    source_density = 9 / alpha
    raw_density_A = source_density * w * F(9, 2) / kA
    raw_density_B = source_density * (1 - w) * 3 / kB
    raw_density = F(243, 11) / alpha
    need('raw density agrees on disjoint roots without summing twice',
         raw_density_A == raw_density_B == raw_density)
    need('positive rho gate strictly inside positive-mass range',
         0 < rho_star < 33 * (1 - loss0))

    def mass_lower(rho):
        return 1 - F(rho) / 33 - loss0

    def query_upper(rho):
        return N / mass_lower(rho)

    def continuation_haar(rho):
        return alpha * (566 * mass_lower(rho) - 49 * N) / 13608

    need('rho boundary gives target equality, not a strict gate',
         mass_lower(rho_star) == N / target and query_upper(rho_star) == target)
    need('rho zero strict full-query gate', mass_lower(0) > 0 and query_upper(0) < target)
    need('rho gate is the rearranged first-moment loss bound',
         rho_star == 33 * (1 - F(49, 566) * N - K3 / 66 - K7 / 22))
    need('Gamma gate and first-moment rho gate coincide',
         F(2, 3) * rho_star + K3 / 3 == Gamma_star)

    # Exact geometric completions: finite cuts plus their full infinite tails.
    for h in (4, 5, 6, 12, 30):
        a = lambda e: F(54, 3 ** e)
        need('residual load weights and full tail at height ' + str(h),
             sum((a(e) for e in range(4, h + 1)), F(0)) + F(1, 3 ** (h - 3)) == 1)
        need('later load weights and full tail at height ' + str(h),
             sum((3 * a(e) for e in range(5, h + 1)), F(0)) + F(1, 3 ** (h - 4)) == 1)
        need('actual branch cylinder caps at height ' + str(h),
             a(h) / 12 == F(9, 2 * 3 ** h) and a(h) / 18 == F(3, 3 ** h))
        deep_head = sum((F(27, 11 * 3 ** e) for e in range(2, h + 1)), F(0))
        deep_tail = F(27, 22 * 3 ** h)
        need('complete query-height sum at height ' + str(h), deep_head + deep_tail == F(9, 22))
    need('height four coefficient and later coefficient', F(54, 81) == F(2, 3))
    need('hinge split loss coefficients', F(2, 3) / 22 == F(1, 33) and F(1, 3) / 22 == F(1, 66))

    # Saturated losses are retained. The worst allowed survival c is
    # max(0,1-Y/n), and the exact maximum loss there is the capped hinge.
    saturated_controls = 0
    for n, t, weight, kap in ((12, tA, w, kA), (18, tB, 1 - w, kB)):
        for Y in (F(0), t / 2, t, t + 1, (t + n) / 2, F(n), F(n + 1), F(2 * n)):
            cmin = max(F(0), 1 - Y / n)
            capped = min(weight, weight * positive(Y - t) / (n - t))
            worst_loss = weight * (1 - cmin / max(cmin, kap))
            need('saturated branch maximum n=' + str(n) + ' Y=' + str(Y), worst_loss == capped)
            for c in (cmin, (1 + cmin) / 2, F(1)):
                loss = weight * (1 - c / max(c, kap))
                if not (0 <= loss <= capped <= weight):
                    raise ValueError('saturated pointwise loss control failed')
                saturated_controls += 1
    controls['saturated_feasible_survivals'] = saturated_controls

    split_controls = 0
    for L, Z, s in product(map(F, (0, 1, 2, 3, 6, 12)),
                           map(F, (0, 1, 3, 4, 8, 18)),
                           (F(0), F(1, 2), F(1), F(3, 2))):
        YA = F(2, 3) * L + Z / 3
        lhs = positive(YA - 1)
        rhs = F(2, 3) * positive(L - s) + positive(Z - (3 - 2 * s)) / 3
        if not lhs <= rhs:
            raise ValueError('branch-A hinge decomposition failed')
        split_controls += 1
    need('hinge split includes all threshold and saturation controls', split_controls == 144)
    controls['hinge_decomposition_points'] = split_controls

    # Actual fibre controls use globally compatible Q-phase2 for every
    # listed cofactor, with distinct full moduli. They do NOT claim that a
    # Dirac point is a PA source, or infer any moment bound from sampling.
    # Their role is to reject hidden disjointness assumptions in 1-c<=Y/n.
    def case_from_phases(phases):
        return [(4, 5 ** (i + 1), r) for i, r in enumerate(phases)]

    fibre_cases = {
        'empty': [],
        'equal_A_cylinders': [(4, 5, 0), (4, 7, 0)],
        'nested_A_cylinders': [(4, 5, 0), (5, 7, 0), (6, 11, 0)],
        'disjoint_A_cylinders': [(4, 5, 0), (4, 7, 6), (4, 11, 9)],
        'nested_B_cylinders': [(4, 5, 2), (5, 7, 2), (6, 11, 2)],
        'inactive_pure_forbidden_phases': [(4, 5, 1), (4, 7, 3)],
        'mixed_overlaps': [(4, 5, 0), (4, 7, 0), (4, 11, 2),
                           (5, 35, 0), (5, 55, 83), (6, 77, 6)],
        'dead_A': case_from_phases(r for r in range(81) if r % 9 in (0, 6)),
        'dead_B': case_from_phases(r for r in range(81) if r % 3 == 2),
        'dead_both': case_from_phases(r for r in range(81) if r % 9 in (0, 6) or r % 3 == 2),
    }
    fibre_results = {}
    for name, originals in fibre_cases.items():
        need('distinct actual fibre labels ' + name,
             len({3 ** e * d for e, d, r in originals}) == len(originals))
        LA, LB = {}, {}
        for e, d, r in originals:
            if r % 9 in (0, 6):
                LA[e] = LA.get(e, 0) + 1
            elif r % 3 == 2:
                LB[e] = LB.get(e, 0) + 1
        YA = sum((F(54, 3 ** e) * count for e, count in LA.items()), F(0))
        YB = sum((F(54, 3 ** e) * count for e, count in LB.items()), F(0))
        L4 = F(LA.get(4, 0))
        ZA = sum((F(162, 3 ** e) * count for e, count in LA.items() if e >= 5), F(0))
        branchA = [r for r in range(729) if r % 9 in (0, 6)]
        branchB = [r for r in range(729) if r % 3 == 2]
        good = lambda r: all(r % (3 ** e) != a for e, d, a in originals)
        cA = F(sum(map(good, branchA)), len(branchA))
        cB = F(sum(map(good, branchB)), len(branchB))
        loss = w * (1 - cA / max(cA, kA)) + (1 - w) * (1 - cB / max(cB, kB))
        capped = min(w, lamA * positive(YA - tA)) + min(1 - w, lamB * positive(YB - tB))
        need('overlap-safe branch union and allocation ' + name,
             1 - cA <= YA / 12 and 1 - cB <= YB / 18 and YA == F(2, 3) * L4 + ZA / 3)
        need('actual saturated fibre loss ' + name, 0 <= loss <= capped <= 1)
        fibre_results[name] = {'cA': str(cA), 'cB': str(cB), 'YA': str(YA), 'YB': str(YB),
                               'actual_loss': str(loss), 'capped_loss_upper': str(capped)}
    need('overlap control is strictly smaller than additive deletion',
         F(fibre_results['equal_A_cylinders']['cA']) == F(17, 18) and
         1 - F(fibre_results['equal_A_cylinders']['cA']) < F(fibre_results['equal_A_cylinders']['YA']) / 12)
    need('dead fibres retain capped loss and avoid zero denominators',
         fibre_results['dead_A']['cA'] == '0' and fibre_results['dead_B']['cB'] == '0' and
         fibre_results['dead_both']['actual_loss'] == '1')
    controls['actual_fibre_cases'] = len(fibre_cases)

    # Literal five-original structural witness. The five numerical phases
    # are fixed once; no residue is re-selected along a query branch.
    d = 385
    family = [(3, 1), (9, 3), (d, 0), (3 * d, crt(2, 3, 1, d)),
              (81 * d, crt(0, 81, 2, d))]
    period = lcm(*(m for m, a in family))
    need('literal family has five distinct odd nonunit labels',
         len({m for m, a in family}) == 5 and all(m > 1 and m % 2 for m, a in family))
    need('literal period and two actual CRT residues',
         period == 31185 and family[3][1] % 3 == 2 and family[3][1] % d == 1 and
         family[4][1] % 81 == 0 and family[4][1] % d == 2)
    private_specs = ((1, 3), (3, 3), (2, 0), (2, 1), (0, 2))
    private = {}
    for (m, a), (tr, qr) in zip(family, private_specs):
        n = crt(tr, 81, qr, d)
        need('private CRT point for original ' + str(m),
             n % m == a and all(n % mm != aa for mm, aa in family if mm != m))
        private[str(m)] = n
    survivor = [n for n in range(period) if all(n % m != a for m, a in family)]
    need('literal actual survivor is nonempty', len(survivor) > 0)
    projections = []
    for m, a in family:
        e, cofactor = 0, m
        while cofactor % 3 == 0:
            cofactor //= 3
            e += 1
        if cofactor > 1:
            projections.append((e, cofactor, a % cofactor, a % (3 ** e)))
    need('through height three has precisely two projected phases',
         {r for e, dd, r, tr in projections if e <= 3} == {0, 1})
    need('through height four violates the earlier two-phase hypothesis',
         {r for e, dd, r, tr in projections if e <= 4} == {0, 1, 2})
    need('sole height-four residual is the actual branch A phase',
         [(dd, r, tr) for e, dd, r, tr in projections if e == 4] == [(385, 2, 0)])
    rho_cap = source_density / d
    need('literal reciprocal condition implies strict rho gate', F(1, d) < reciprocal_star and rho_cap < rho_star)
    need('literal conservative full-query certificate passes', mass_lower(rho_cap) > 0 and query_upper(rho_cap) < target)

    # Same selected PA law sanity for this witness, using Report569's
    # k_11=min(5/3,1/g_11)1_G. At old residues0,1 mod35 only one11-root
    # is removed, so g=10/11 and kappa=11/10; elsewhere g=kappa=1.
    # Every later row is unchanged Haar. This gives a mass-one PA source.
    nu385 = {}
    for x in range(d):
        triggered = x % 35 in (0, 1)
        row_density = min(F(5, 3), F(11, 10)) if triggered else F(1)
        nu385[x] = F(0) if x in (0, 1) else row_density / d
    need('literal selected PA source is a single probability avoiding phases zero and one',
         sum(nu385.values()) == 1 and nu385[0] == nu385[1] == 0)
    need('literal selected PA law preserves its old35 Haar marginal',
         all(sum(v for x, v in nu385.items() if x % 35 == r) == F(1, 35) for r in range(35)))
    rho_actual = nu385[2]
    need('literal branch statistic under that same actual source', rho_actual == F(1, 385) < rho_cap)
    need('literal residual fibre is live without clipping loss', F(17, 18) > kA and F(2, 3) < tA)

    # Continuation density accounts for both outside pure coordinates and
    # the SAME final normalization, with the unit old cofactor included.
    outside_density = F(22, 21) * F(28, 27)
    need('outside pure conditioning density', outside_density == F(616, 567))
    for name, rho in (('zero', F(0)), ('literal_density_cap', rho_cap), ('literal_actual_PA', rho_actual)):
        s0 = mass_lower(rho)
        final_density = raw_density / s0
        full_density = final_density * outside_density
        remaining = (566 - 49 * query_upper(rho)) / 567
        need('same-law continuation density and normalization ' + name,
             s0 > 0 and remaining > 0 and remaining / full_density == continuation_haar(rho))
    fixed_den = 45495414676673208339450453294815817703090068480000000
    need('zero-rho exact Haar certificate', continuation_haar(0) ==
         F(5077349916577157708522677346911843565565363056927, fixed_den))
    need('literal conservative exact Haar certificate', continuation_haar(rho_cap) ==
         F(3736878374366916983392122334571070715442355056927, fixed_den))
    need('simple strict continuation bounds', continuation_haar(0) > F(1, 9000) and
         continuation_haar(rho_cap) > F(1, 12500))

    # A21-original rho=0 witness. CRT private points certify irredundancy
    # without enumerating its130945815-point common period. The specified
    # selection has six active residual cofactors on a positive-PA-mass
    # cylinder; no statement about every possible spare-phase selection is
    # inferred from this displayed selection.
    def full_point(ternary, roots):
        value, modulus = ternary, 81
        for prime in Q:
            value = crt(value, modulus, roots[prime], prime)
            modulus *= prime
        return value

    zero_originals = [
        {'label': 'pure3', 'modulus': 3, 'phase': 1},
        {'label': 'pure9', 'modulus': 9, 'phase': 3},
    ]
    zero_private_specs = [(1, {q: 3 for q in Q}), (3, {q: 3 for q in Q})]
    for i, q in enumerate(Q):
        for e, qr, tr in ((0, 0, 0), (1, 1, 2), (4, 2, 2 + 3 * i)):
            m = 3 ** e * q
            a = qr if e == 0 else crt(tr, 3 ** e, qr, q)
            zero_originals.append({'label': 'q' + str(q) + '_e' + str(e),
                                   'modulus': m, 'phase': a, 'Q_cofactor': q,
                                   'exponent3': e, 'Q_phase': qr,
                                   'ternary_phase': tr if e else None})
            roots = {p: 3 for p in Q}
            roots[q] = qr
            zero_private_specs.append((tr, roots))
    zero_originals.append({'label': 'Q_only_385', 'modulus': 385, 'phase': 4})
    zero_private_specs.append((0, {q: 4 if q in (5, 7, 11) else 3 for q in Q}))
    zero_period = 81 * prod(Q)
    need('zero-load witness has21 distinct odd numerical labels',
         len(zero_originals) == len({o['modulus'] for o in zero_originals}) == 21 and
         all(o['modulus'] > 1 and o['modulus'] % 2 for o in zero_originals))
    need('zero-load CRT period resolves every original without enumeration',
         zero_period == 130945815 and all(zero_period % o['modulus'] == 0 for o in zero_originals))
    zero_private = []
    for idx, (tr, roots) in enumerate(zero_private_specs):
        value = full_point(tr, roots)
        hits = [i for i, o in enumerate(zero_originals) if value % o['modulus'] == o['phase']]
        need('zero-load private point ' + zero_originals[idx]['label'], hits == [idx])
        zero_private.append({'label': zero_originals[idx]['label'], 'point': value,
                             'ternary_mod81': tr, 'Q_roots': {str(q): roots[q] for q in Q}})
    zero_survivor = full_point(0, {q: 3 for q in Q})
    need('zero-load actual survivor witness',
         all(zero_survivor % o['modulus'] != o['phase'] for o in zero_originals))
    for q in Q:
        rows = [o for o in zero_originals if o.get('Q_cofactor') == q]
        need('zero-load through3 two phases and through4 third phase q=' + str(q),
             {o['Q_phase'] for o in rows if o['exponent3'] <= 3} == {0, 1} and
             {o['Q_phase'] for o in rows} == {0, 1, 2})
        need('zero-load fourth layer lies in branch B q=' + str(q),
             next(o['ternary_phase'] for o in rows if o['exponent3'] == 4) % 3 == 2)
    zero_selected = [(q, a) for q in Q for a in (0, 1)] + [(385, 4)]
    need('all-two Q cylinder survives displayed selected phases',
         all(2 % d != a for d, a in zero_selected))
    active = [o['Q_cofactor'] for o in zero_originals if o.get('exponent3') == 4 and
              2 % o['Q_cofactor'] == o['Q_phase']]
    need('displayed live cylinder activates six residual cofactors', active == list(Q))
    need('zero-load narrow fourth layer is identically empty',
         all(o['ternary_phase'] % 3 == 2 for o in zero_originals if o.get('exponent3') == 4))
    need('zero-load actual source starts in admitted pure-mass rectangle',
         F(1, 2) <= F(3, 5) <= 1 and F(2, 3) <= F(5, 7) <= 1)
    for q, rowdensity, cap in ((11, F(11, 8), F(5, 3)), (13, F(13, 11), F(3, 2)),
                               (17, F(17, 15), F(2)), (19, F(19, 17), F(9, 5))):
        need('zero-load normalized actual row below PA cap q=' + str(q), rowdensity < cap)
    # Directly construct the normalized5/7/11 prefix, including the extra
    # forbidden11-root4 on exactly the old(4,4) row. Later coordinates have
    # independent normalized Haar after deleting roots0,1.
    zero_nu385 = {}
    for x in range(385):
        if x % 5 in (0, 1) or x % 7 in (0, 1) or x % 11 in (0, 1) or x == 4:
            zero_nu385[x] = F(0)
        else:
            row_count = 8 if x % 35 == 4 else 9
            zero_nu385[x] = F(1, 15 * row_count)
    need('zero-load actual normalized prefix includes the extra385 deletion',
         sum(zero_nu385.values()) == 1 and zero_nu385[4] == 0)
    need('zero-load actual prefix preserves its allowed5/7 marginal',
         all(sum(v for x, v in zero_nu385.items() if x % 35 == a) ==
             (F(0) if a % 5 in (0, 1) or a % 7 in (0, 1) else F(1, 15))
             for a in range(35)))
    all_two_mass = zero_nu385[2] * prod((F(1, q - 2) for q in (13, 17, 19)), start=F(1))
    need('zero-load all-two cylinder has positive same-PA-source mass',
         all_two_mass == F(1, 378675) > 0)
    zero_example = {
        'original_count': len(zero_originals), 'period': zero_period,
        'originals': zero_originals, 'private_points': zero_private,
        'survivor_witness': zero_survivor, 'selected_phases': zero_selected,
        'live_Q_cylinder': {'phase': 2, 'modulus': prod(Q), 'active_cofactors': active,
                            'actual_PA_mass': exact(all_two_mass)},
        'rho_A': '0', 'query_upper': exact(query_upper(0)),
        'nine_prime_Haar_lower': exact(continuation_haar(0)),
        'structural_scope': 'The through-exponent4 two-phase premise fails. The displayed selected PA source also violates the pointwise M<=2 premise on a positive-mass cylinder. This does not assert failure of every alternative spare-phase selection or every older instance-specific certificate.',
    }

    out = {
        'scope': 'Conditional branch-asymmetric lift: exactly the pure3 originals1mod3,3mod9; at most two selected Q phases through exponent3; actual branch-A exponent4 statistic rho below the stated threshold. Arbitrary other residual overlaps and finite later heights. One PA source, complete query tails, one final normalization. Ordinary proof, not Lean or unrestricted Erdos7.',
        'provenance': provenance,
        'producer_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
        'proof_sources': [
            'Report569 SD3: actual capped PA kernels and one common source',
            'Report574 FH3-FH8 and section6: same-source full-suffix stop-loss bounds',
            'Report574 section4: PA density9/alpha_min and23/29 continuation',
            'Report579 RC2-RC6: branch caps, actual joint law and complete query sum',
        ],
        'constants': {k: exact(v) for k, v in {
            'B': B, 'K3': K3, 'K7': K7, 'alpha_min': alpha, 'target': target,
            'w': w, 'tA': tA, 'tB': tB, 'kappa_A': kA, 'kappa_B': kB,
            'raw_query_upper_N': N, 'rho_threshold': rho_star, 'Gamma_threshold': Gamma_star,
            'branch_A_reciprocal_threshold': reciprocal_star, 'source_density_upper': source_density,
            'raw_joint_density_upper': raw_density, 'zero_rho_mass_lower': mass_lower(0),
            'zero_rho_query_upper': query_upper(0), 'zero_rho_target_margin': target - query_upper(0),
            'zero_rho_nine_prime_Haar_lower': continuation_haar(0),
        }.items()},
        'symbolic_certificate': {
            'mass_lower': 's0(rho)=1-rho/33-K3/66-K7/22',
            'query_upper': 'R_P(mu)<=N/s0(rho), N=B+(10/11)(1+B)',
            'strict_gate': 'rho<rho_threshold; equality only reaches566/49',
            'general_Gamma_condition': 'For some s in[0,3/2], Gamma_A(s)=(2/3)E_nu(L_A4-s)_++K_(3-2s)/3<Gamma_threshold gives mass>=1-(Gamma_A(s)+K7)/22 and R<=N/[1-(Gamma_A(s)+K7)/22]',
            'residual_allocation': 'YA=(2/3)L_A4+(1/3)ZA; ZA and YB are convex mixtures of partial single-phase layouts under the same nu',
            'capped_pointwise_loss': 'sum_j min(w_j,w_j*(Y_j-t_j)_+/(n_j-t_j)), nA=12,nB=18',
            'continuation_Haar_lower': 'alpha_min*(566*s0(rho)-49*N)/13608',
            'scope_boundary': 'Failure of the rho premise does not imply failure of an actual query law or noncoverage.',
        },
        'actual_example': {
            'family': [{'modulus': m, 'phase': a} for m, a in family],
            'period': period, 'survivor_count': len(survivor), 'survivor_witness': survivor[0],
            'private_points': private, 'selected_phases': {'385': [0, 1]},
            'projected_originals': [{'exponent3': e, 'Q_cofactor': dd, 'Q_phase': r, 'ternary_phase': tr}
                                   for e, dd, r, tr in projections],
            'rho_density_upper': exact(rho_cap), 'rho_actual_selected_PA': exact(rho_actual),
            'conservative_query_upper': exact(query_upper(rho_cap)),
            'conservative_nine_prime_Haar_lower': exact(continuation_haar(rho_cap)),
            'actual_rho_inserted_query_upper': exact(query_upper(rho_actual)),
            'structural_scope': 'Separates the through-exponent4 two-projection hypothesis. It is also covered by Report572 with overlap count M=1; no first-proof or unrestricted claim.',
        },
        'zero_load_structural_example': zero_example,
        'controls': controls,
        'actual_fibre_controls': fibre_results,
        'check_count': len(checks), 'checks': checks,
    }
    args.output.write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({'checks': len(checks), 'controls': controls,
                      'rho_threshold': str(rho_star), 'zero_rho_query_upper': float(query_upper(0)),
                      'literal_conservative_query_upper': float(query_upper(rho_cap)),
                      'zero_rho_Haar_lower': float(continuation_haar(0)),
                      'literal_conservative_Haar_lower': float(continuation_haar(rho_cap))}))


if __name__ == '__main__':
    main()
