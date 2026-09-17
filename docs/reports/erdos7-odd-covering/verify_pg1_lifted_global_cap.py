#!/usr/bin/env python3
"""Exact arithmetic for the full-inventory lifted PG1 cubic transfer.

The ordinary all-height/all-test argument is FI in marked_head_profile.md.
Finite replays below verify formulas and family identities, not the universal
quantifiers. All original divisor labels are retained. Standard library only;
checks remain active under python -I -O. No Lean verification is asserted.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import comb, factorial, gcd
from pathlib import Path
import argparse
import json

HERE = Path(__file__).resolve().parent
SOURCE = 'mod3_conditioned_geometry_certificate.json'
SOURCE_SHA256 = '9a0e265a456ab133389202abd5ef91ac6826957f74c24b1e8bd055a97cea0a0a'
CERTIFICATE = 'pg1_lifted_global_cap_certificate.json'
P, LOW, CENTER, SLICE, TARGET = 17, 315, 2, 314, 2
DELTA, CAP, TRANSFER = F(7, 15), F(15, 8), F(1, 2**24)
OLD_PRIMES = (3, 5, 7, 11, 13)
PG1_FAMILY = [(3, 0), (9, 4), (5, 0), (15, 11), (45, 37),
              (7, 0), (21, 8), (35, 9), (63, 59), (105, 74), (315, 89)]


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def multiply(values):
    result = F(1)
    for value in values:
        result *= value
    return result


def geom_moment(p, k):
    """E G^k from factorial moments, P(G=n)=(p-1)/p^(n+1)."""
    stirling = [[0]*(k+1) for _ in range(k+1)]
    stirling[0][0] = 1
    for i in range(1, k+1):
        for j in range(1, i+1):
            stirling[i][j] = stirling[i-1][j-1]+j*stirling[i-1][j]
    return sum((F(stirling[k][j]*factorial(j), (p-1)**j)
                for j in range(k+1)), F(0))


def fixed_low_moment(p, h, k):
    return sum((comb(k, j)*(h+1)**(k-j)*geom_moment(p, j)
                for j in range(k+1)), F(0))


def root_pure_moment(p, k):
    """Uniform nonzero first root, then independent uniform suffix."""
    return 1+F(p, p-1)*(fixed_low_moment(p, 0, k)-1)


def fixed_finite_moment(p, h, n, k):
    return F((h+1)**k)+sum((F((h+1+j)**k-(h+j)**k, p**j)
                           for j in range(1, n+1)), F(0))


def nonzero_finite_moment(p, a, k):
    return F(1)+sum((F((j+1)**k-j**k, (p-1)*p**(j-1))
                     for j in range(1, a+1)), F(0))


def moment_data():
    factors, fixtures = [], []
    for p, h, law in [(3, 2, 'fixed-low'), (5, 1, 'fixed-low'),
                      (7, 1, 'fixed-low'), (11, 0, 'nonzero-root'),
                      (13, 0, 'nonzero-root'), (17, 1, 'fixed-low')]:
        row = dict(prime=p, fixed_depth=h, law=law)
        for k in (2, 3):
            closed = fixed_low_moment(p, h, k)
            b = h+1
            formula = (b*b+F(2*b, p-1)+F(p+1, (p-1)**2) if k == 2 else
                       b**3+F(3*b*b, p-1)+F(3*b*(p+1), (p-1)**2)
                       +F(p*p+4*p+1, (p-1)**3))
            require(closed == formula, 'factorial-moment and rational closed forms agree')
            upper = root_pure_moment(p, k) if law == 'nonzero-root' else closed
            row['K'+str(k)] = upper
            for n in (0, 1, 2, 7, 64):
                if law == 'nonzero-root':
                    finite = nonzero_finite_moment(p, n, k)
                    tail = F(p, p-1)*F(1, p**n)*(fixed_low_moment(p, n, k)-(n+1)**k)
                    cap = lambda e: F(1) if e == 0 else F(1, (p-1)*p**(e-1))
                    depth = n
                else:
                    finite = fixed_finite_moment(p, h, n, k)
                    tail = F(1, p**n)*(fixed_low_moment(p, h+n, k)-(h+n+1)**k)
                    cap = lambda e: F(1) if e <= h else F(1, p**(e-h))
                    depth = h+n
                require(finite+tail == upper and tail > 0,
                        'exact finite sum plus positive untruncated tail')
                if n <= 2:
                    ordered = sum((cap(max(es)) for es in product(range(depth+1), repeat=k)), F(0))
                    require(ordered == finite, 'all ordered original-label tuples retained')
                fixtures.append(dict(prime=p, order=k, added_or_nonzero_depth=n,
                                     finite=finite, exact_tail=tail))
        factors.append(row)
    K2 = multiply(row['K2'] for row in factors)
    K3 = multiply(row['K3'] for row in factors)
    require(K2 == F(638455140323, 248832000), 'full six-coordinate second moment')
    require(K3 == F(104829447952912991, 402653184000), 'full six-coordinate third moment')
    return dict(factors=factors, K2=K2, K3=K3, finite_sum_fixtures=fixtures,
                universal_formula='Ordered original-label k-tuples use the coordinate cap at their maximum exponent. The full box factors by CRT. Every finite sum equals its displayed infinite rational bound minus its strictly positive exact tail.',
                fixed_coordinate='F_k(p,h)=E[(h+1+G_p)^k]; P(G_p>=j)=p^(-j)',
                nonzero_coordinate='P_k(p)=1+p/(p-1)*(F_k(p,0)-1); absent primes contribute 1')


def original_divisors(exponents):
    return sorted(int(multiply(p**e for p, e in zip(OLD_PRIMES, es)))
                  for es in product(*(range(a+1) for a in exponents)))


def crt(a, m, b, n):
    z = a+m*(((b-a)*pow(m, -1, n)) % n)
    require(0 <= z < m*n and z % m == a % m and z % n == b % n, 'CRT identity')
    return z


def prefix(e, final):
    return 15*(P**(e-1)-1)//16+final*P**(e-1)


def old_residue(d):
    original = dict(PG1_FAMILY)
    if d in original:
        return original[d], d
    if d % 11 == 0:
        return 0, 11
    if d % 13 == 0:
        return 0, 13
    d0 = gcd(d, LOW)
    require(d0 in original, 'every remaining old divisor projects to a PG1 divisor')
    return original[d0], d0


def family_fixtures(points):
    low_divisors = original_divisors((2, 1, 1, 0, 0))
    rows = []
    for exponents, H in [((2, 1, 1, 0, 0), 1), ((3, 2, 2, 1, 1), 2),
                         ((7, 4, 3, 2, 2), 3), ((66, 1, 1, 1, 1), 2)]:
        divisors = original_divisors(exponents)
        M = int(multiply(p**a for p, a in zip(OLD_PRIMES, exponents)))
        require(len(divisors) == int(multiply(a+1 for a in exponents))
                and len(set(divisors)) == len(divisors) and divisors[-1] == M,
                'all old original divisor labels exactly once')
        family = [(d, old_residue(d)[0]) for d in divisors[1:]]
        for d, residue in family:
            a, base = old_residue(d)
            require(residue == a and d % base == 0 and 0 <= a < d,
                    'added old classes are subsets of their excluded base class')
            if base in (11, 13):
                require(a == 0, 'added prime first-root exclusion')
            else:
                require(all(x % base != a for x in points), 'PG1 support avoids projected class')
        for e in range(1, H+1):
            for d in divisors:
                if d == 1:
                    a = prefix(e, 0)
                elif d in low_divisors:
                    j = low_divisors.index(d)
                    a = crt(CENTER % d, d, prefix(e, j), P**e)
                else:
                    a = 0
                    require(a % P == 0, 'every added current class lies in pure root zero')
                family.append((d*P**e, a))
        expected = {d*P**e for d in divisors for e in range(H+1)}-{1}
        require(len(family) == len(expected) and {d for d, _ in family} == expected,
                'all original full-family labels present exactly once')
        require(all(d % 2 == 1 and 0 <= a < d for d, a in family), 'valid odd residue classes')
        rows.append(dict(old_exponents=exponents, current_height=H, old_period=M,
                         complete_test_labels=len(expected)+1, forbidden_labels=len(family),
                         independent_original_test_residues=True))
    return rows


def rare_cylinder_data():
    fixtures = []
    for N in (0, 1, 2, 4, 6, 16, 64):
        exact = F(208)-F(16*(N+4), 3**N)
        tail_sum = 16*(9+sum((F(2*j+5, 3**j) for j in range(1, N+1)), F(0)))
        pair_caps = 16*sum((F(1, 3**max(0, max(a, b)-2))
                            for a in range(N+3) for b in range(N+3)), F(0))
        require(exact == tail_sum == pair_caps <= 208, 'exact complete-test second-moment maximum')
        conditional = 4*(N+3)
        if N <= 6:
            divisors = original_divisors((N+2, 1, 1, 0, 0))
            loads = [sum(x % d == SLICE % d for d in divisors)
                     for x in (SLICE+LOW*j for j in range(3**N))]
            require(F(sum(a*a for a in loads), 3**N) == exact,
                    'literal full-original-label load second moment')
            cylinder = [j for j in range(3**N) if (LOW*j) % 3**(N+2) == 0]
            require(cylinder == [0] and loads[0] == conditional,
                    'deepest original cylinder has mass 3^-N and unbounded conditional load')
        fixtures.append(dict(N=N, original_test_labels=4*(N+3), Gamma=exact,
                             cylinder_mass=F(1, 3**N), conditional_load=conditional))
    require(16**2 > 208, 'N=1 already exceeds sqrt of uniform Gamma bound')
    lifts = [314, 629, 944]
    extra = [(27, 17), (135, 89), (189, 188)]
    require(all(any(x % d == a for d, a in extra) for x in lifts),
            'arbitrary higher old residues can delete the whole transfer slice')
    return dict(old_period='315*3^N', complete_test='one label per divisor, all centered at 314',
                exact_Gamma='208-16*(N+4)/3^N', conditional_ratio='4*(N+3)',
                conclusion='A uniform second moment does not imply E[A*1_C] <= sqrt(Gamma)*P(C).',
                actual_current_statistic='17^(-e)*1_(314 mod 3^(N+2)), from original label 3^(N+2)*17^e',
                fixtures=fixtures,
                zero_slice_example=dict(old_period=945, lifted_points=lifts, extra_forbidden=extra))


def height_data(points, mu, counts, epsilon):
    result = []
    for H in (1, 2, 3, 16, 100):
        s = (1-F(1, P**H))/16
        lam = 1-s
        donors = [12, 13, 14, 15, 16] if H == 1 else [12, 13, 14, 16]
        rows = {}
        for x in points:
            bad = counts[x]*s
            beta = max(F(0), bad/lam-DELTA)/(1-DELTA)
            c = 1/max(lam-bad, lam*(1-DELTA))
            b = beta/bad if bad else F(0)
            require(c*(lam-bad)+beta == 1 and 0 <= b <= 1/lam <= c <= CAP/lam,
                    'actual BB row normalization, charge and density caps')
            rows[x] = (beta, c, b)
        beta0, c0, _ = rows[SLICE]
        _, c2, b2 = rows[CENTER]
        require(beta0 == 0 and c0 == 1/(1-2*s) <= F(8, 7), 'uniform uncharged transfer slice')
        require((CAP/lam-c0)/P >= F(41, 952) > TRANSFER
                and c0/P >= F(1, P) > TRANSFER/len(donors), 'recipient slack and donor positivity')
        require(c2-b2 == F(7, 88)/s and (c2-b2)/P >= F(14, 187),
                'exact all-spokes witness difference and uniform gap')
        rho = 1-sum((mu[x]*rows[x][0] for x in points), F(0))
        require(rho >= F(len(donors), P) > 0, 'common clean roots ensure actual survivors')
        result.append(dict(height=H, s=s, pure_survival=lam, donor_roots=donors,
                           selected_density=c0, actual_survivor_mass=rho,
                           conditioned_Gamma_decrease=epsilon/rho))
    return result


def rare_family_stability(mu, epsilon):
    factors = dict(old3=fixed_low_moment(3, 2, 4),
                   old5=fixed_low_moment(5, 1, 4),
                   old7=fixed_low_moment(7, 1, 4),
                   old11=root_pure_moment(11, 4),
                   old13=root_pure_moment(13, 4),
                   current17_Haar=fixed_low_moment(17, 0, 4))
    require(list(factors.values()) == [F(232), F(1297, 32), F(818, 27),
                                      F(20429, 6250), F(28711, 10368), F(17595, 8192)],
            'all six fourth-moment factors, with uniform current Haar')
    K4 = multiply(factors.values())
    require(K4 == F(3528039728534972593, 637009920000), 'complete-test Haar fourth moment')
    fixtures = []
    for p, h, nonzero in [(3, 2, False), (5, 1, False), (7, 1, False),
                          (11, 0, True), (13, 0, True), (17, 0, False)]:
        upper = root_pure_moment(p, 4) if nonzero else fixed_low_moment(p, h, 4)
        if nonzero:
            require(upper == 1+F(1, p-1)*(fixed_low_moment(p, 1, 4)-1),
                    'independent Bernoulli times 1+G equals nonzero-root law')
        for n in (0, 1, 4, 64):
            finite = (nonzero_finite_moment(p, n, 4) if nonzero else
                      fixed_finite_moment(p, h, n, 4))
            tail = (F(p, p-1)*F(1, p**n)*(fixed_low_moment(p, n, 4)-(n+1)**4)
                    if nonzero else
                    F(1, p**n)*(fixed_low_moment(p, h+n, 4)-(h+n+1)**4))
            require(finite+tail == upper and tail > 0, 'fourth-moment finite sum and exact tail fixtures')
            fixtures.append(dict(prime=p, added_or_nonzero_depth=n, finite=finite, exact_tail=tail))
    first = 0
    while 3**first*epsilon**2 <= 64*K4:
        first += 1
    require(first == 58 and 3**57*epsilon**2 < 64*K4 < 3**58*epsilon**2,
            'first sufficient integer height for the squared stability inequality')
    N, Q = 64, 3**66
    q = F(1, 3**N)
    margin = 3**N*epsilon**2-64*K4
    require(margin > 0 and CAP/F(15, 16) == 2,
            'two comparisons with density difference at most2 retain epsilon/2')
    low_mass = sum((mass for x, mass in mu.items() if x % 9 == SLICE % 9), F(0))
    actual_F_mass = low_mass*q
    require(0 < actual_F_mass <= q < 1, 'exact old rare-event mass from the PG1 mod9 projection')
    cofactors = [Q, 5*Q, 7*Q, 35*Q, 11*Q]
    minimum_M = Q*5*7*11*13
    projection = {d: SLICE % d for d in (9, 5, 7, 11, 13)}
    require(projection == {9: 8, 5: 4, 7: 6, 11: 6, 13: 2}
            and all(SLICE % d != a for d, a in PG1_FAMILY), 'positive old support witness')
    classes = []
    for d, root in zip(cofactors, range(12, 17)):
        residue = crt(SLICE % d, d, root, P)
        require(minimum_M % d == 0 and d % Q == 0 and LOW % d != 0
                and residue % Q == SLICE and residue % P == root,
                'actual distinct original mixed labels, with changed masks contained in F')
        classes.append(dict(old_cofactor=d, original_modulus=d*P,
                            old_residue=SLICE, current_root=root, CRT_residue=residue))
    require(len(set(d*P for d in cofactors)) == 5, 'five distinct original mixed moduli')
    support_witness_mass = mu[SLICE]*q/F(120)
    require(support_witness_mass > 0 and mu[CENTER] > 0, 'positive-mass witnesses for every dirty root')
    rho_lower = F(4, P)*(1-q)
    require(rho_lower > 0, 'new family retains positive actual survivors')
    return dict(
        scope='Keep all pure17 classes, all old labels and old law fixed. Only five mixed classes change; masks coincide off F. No arbitrary-residue conclusion.',
        fourth_moment_factors=factors, K4_Haar=K4,
        fourth_moment_formula='E[((3+G3)*(2+G5)*(2+G7)*(1+B11*(1+G11))*(1+B13*(1+G13))*(1+G17))^4]',
        geometric_law='P(G_p=n)=(p-1)/p^(n+1); B_p independent with P(B_p=1)=1/(p-1)',
        fourth_moment_finite_fixtures=fixtures,
        physical_and_killed_density_cap=F(2), single_comparison='eta=2*sqrt(q*K4_Haar)',
        two_comparisons='loss<=2*eta; 64*K4_Haar<3^N*epsilon^2 gives loss<epsilon/2',
        minimum_sufficient_N=first, selected_N=N, rare_mass_upper=q,
        low_mod9_mass=low_mass, exact_rare_event_mass=actual_F_mass,
        squared_stability_margin=margin, Q=Q, moved_original_classes=classes,
        old_witness=SLICE, old_witness_projections=projection,
        minimum_height_old_point_mass=support_witness_mass,
        dirty_root_witnesses='Root0: pure forbidden; roots1..11: positive-mass old low2; roots12..16: the five old314 cylinders.',
        no_globally_clean_current_root=True, minimum_survivor_mass=rho_lower,
        physical_V_decrease_at_least=epsilon/2,
        conditioned_Gamma_decrease='epsilon/(2*rho_tilde); same actual survivor mass within the new-family pair')


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate certificate key: '+key)
        result[key] = value
    return result


def evaluate(directory):
    raw = (directory/SOURCE).read_bytes()
    require(sha256(raw).hexdigest() == SOURCE_SHA256, 'canonical PG1 source SHA-256')
    source = json.loads(raw, object_pairs_hook=unique_object)
    require(source['schema'] == 'erdos7-mod3-conditioned-geometry-v1', 'source schema')
    cases = [case for case in source['cases'] if case['name'] == 'PG1']
    require(len(cases) == 1, 'unique PG1 source')
    case = cases[0]
    points, weights, den = case['points'], case['weight_numerators'], case['weight_denominator']
    require([tuple(pair) for pair in case['family']] == PG1_FAMILY, 'canonical old forbidden family')
    require(points == [x for x in range(LOW) if all(x % d != a for d, a in PG1_FAMILY)]
            and len(points) == len(weights) == 75 and den == 1000000007
            and all(type(w) is int and w > 0 for w in weights) and sum(weights) == den,
            'canonical positive PG1 law on its exact support')
    mu = dict(zip(points, (F(w, den) for w in weights)))
    require(mu[SLICE] == F(16622259, den) and mu[CENTER] == F(13119398, den), 'fixed low masses')
    low_divisors = original_divisors((2, 1, 1, 0, 0))
    active = {x: [j for j, d in enumerate(low_divisors[1:], 1) if x % d == CENTER % d]
              for x in points}
    require(active[SLICE] == [1] and active[CENTER] == list(range(1, 12)), 'slice and gap witnesses')
    moments = moment_data()
    K2, K3 = moments['K2'], moments['K3']
    epsilon = F(3, 10)*mu[SLICE]*TRANSFER
    excess = P*TRANSFER*K3
    increase = mu[SLICE]*TRANSFER*K2
    gaps = dict(spoke=3*mu[CENTER]*F(14, 187), root_zero=F(3, P), spine=F(3, P*P))
    require(excess < F(3, 10) and F(3, 5)-excess > F(3, 10), 'cubic absorption beats donor loss')
    require(all(gap-increase > epsilon for gap in gaps.values()), 'all non-donor-root gaps absorb recipient gain')
    require(epsilon == F(49866777, 167772161174405120) > 0, 'uniform strict physical gain')
    threshold = 1/(P*TRANSFER)
    for A in (F(0), F(1), threshold/3, threshold, threshold+1):
        for Z in (F(0), F(1), threshold/2, threshold, 2*threshold):
            X = A+Z
            left = TRANSFER*(2*A*Z+Z*Z)-F(2, P)*Z
            middle = TRANSFER*X*X if X > threshold else F(0)
            require(left <= middle <= P*TRANSFER**2*X**3, 'pointwise absorption branch fixtures')
    return encode(dict(
        schema='erdos7-pg1-lifted-global-cap-v1',
        scope='Every finite old height a3>=2,a5,a7>=1,a11,a13>=0 and current H>=1, for the explicitly redundant stable family and uniform product lift. Every original divisor test remains independently selectable. No arbitrary-residue family claim.',
        verification_scope='Exact source binding, rational moment constants and finite formula fixtures. The all-height and complete-test implication is an ordinary proof, not Lean verification or exhaustive test enumeration.',
        source_sha256={SOURCE: SOURCE_SHA256}, old_family=PG1_FAMILY, old_support_points=75,
        old_weight_denominator=den, transferred_low_slice=SLICE,
        transferred_slice_mass=mu[SLICE], all_spokes_witness_mass=mu[CENTER],
        stable_family='Keep old d|315; other old classes use residue0 if11 or13 dividesd, otherwise the PG1 residue at gcd(d,315). Current added old cofactors use residue0 modulo d*17^e, redundant inside pure0mod17. Retain every label.',
        stable_old_law='PG1 low law times independent uniform added357 digits and uniform nonzero first11/13 roots with uniform higher suffixes.',
        moments=moments, family_fixtures=family_fixtures(points),
        second_moment_linear_bridge_counterexample=rare_cylinder_data(),
        transfer=dict(delta=DELTA, global_cap=CAP, t=TRANSFER, target_root=TARGET,
                      target_capacity_slack_lower=F(41, 952), donor_root_mass_lower=F(1, P),
                      natural_target_density_ceiling=F(8, 7), minimum_survivor_mass=F(4, P)),
        cubic_absorption=dict(pointwise='t*(2*A*Z+Z^2)-2*Z/17 <= t*(A+Z)^2*1_(A+Z>1/(17t)) <= 17*t^2*(A+Z)^3',
                              pure17_donor_loss_per_mu_t_lower=F(3, 5),
                              p_t_K3=excess, margin_below_three_tenths=F(3, 10)-excess,
                              recipient_increase_upper=increase, non_donor_root_gaps=gaps,
                              gap_margins={k: g-increase-epsilon for k, g in gaps.items()}),
        uniform_comparisons=dict(physical_V_decrease_at_least=epsilon,
                                 conditional_Gamma_decrease_at_least=epsilon,
                                 sharper_conditional_decrease='epsilon/rho_H; same positive actual survivor mass'),
        rare_family_stability=rare_family_stability(mu, epsilon),
        exact_height_fixtures=height_data(points, mu, {x: len(active[x]) for x in points}, epsilon)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path, default=HERE/CERTIFICATE)
    parser.add_argument('--source-directory', type=Path, default=HERE)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = evaluate(args.source_directory)
    if args.write:
        args.certificate.write_text(json.dumps(result, indent=2)+'\n')
    else:
        stored = json.loads(args.certificate.read_text(), object_pairs_hook=unique_object)
        require(json.dumps(stored, sort_keys=True) == json.dumps(result, sort_keys=True),
                'entire certificate equals exact recomputation')
    print(json.dumps(dict(K2=result['moments']['K2'], K3=result['moments']['K3'],
                          uniform_physical_gain=result['uniform_comparisons']['physical_V_decrease_at_least'],
                          rare_family_physical_gain=result['rare_family_stability']['physical_V_decrease_at_least'],
                          certificate_action='written' if args.write else 'verified')))


if __name__ == '__main__':
    main()
