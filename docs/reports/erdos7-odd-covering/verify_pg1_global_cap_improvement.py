#!/usr/bin/env python3
"""Exact PG1 law-changing global-cap perturbation, valid at every finite height.

The all-height/full-test result uses GC1--GC6 in marked_head_profile.md. The
verifier checks its rational constants, binds the actual PG1 source, and
replays the candidate and original CRT families literally at heights1,2.
Other heights use exact disjoint-prefix arithmetic, without expanding17**H.
Neither the complete-test maximum nor the unrestricted problem is solved.
Standard library only; all mathematical checks survive Python -O.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import argparse
import json

HERE = Path(__file__).resolve().parent
SOURCE = 'certificates/mod3_conditioned_geometry_certificate.json'
CERTIFICATE = 'certificates/pg1_global_cap_improvement_certificate.json'
M, P, CENTER, X0, TARGET = 315, 17, 2, 314, 2
DELTA, GLOBAL_CAP, TRANSFER = F(7, 15), F(15, 8), F(1, 8192)


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


def crt(a, m, b, n):
    z = a + m * (((b-a)*pow(m, -1, n)) % n)
    require(z % m == a % m and z % n == b % n and 0 <= z < m*n, 'literal CRT')
    return z


def prefix(e, final):
    return (P-2)*(P**(e-1)-1)//(P-1)+final*P**(e-1)


def data_at_height(H, points, divisors, old, mu, counts):
    require(H >= 1, 'positive finite height')
    s = (1-F(1, P**H))/(P-1)
    lam = 1-s
    clean = [12, 13, 14, 15, 16] if H == 1 else [12, 13, 14, 16]
    pure, mixed = [], []
    for e in range(1, H+1):
        pure.append((P**e, prefix(e, 0)))
        for j, d in enumerate(divisors[1:], 1):
            mixed.append((d*P**e, crt(CENTER % d, d, prefix(e, j), P**e)))
    family = old+pure+mixed
    expected = {d*P**e for d in divisors for e in range(H+1)}
    require(len(family) == 11+12*H and len(set(d for d, a in family)) == len(family)
            and {d for d, a in family} == expected-{1}, 'every original forbidden modulus')
    require(len(expected) == 12*(H+1), 'every original complete-test modulus')
    require(all(d > 1 and d % 2 and 0 <= a < d for d, a in family), 'actual odd classes')
    rows = {}
    for x in points:
        bad_haar = counts[x]*s
        alpha = bad_haar/lam
        beta = max(F(0), alpha-DELTA)/(1-DELTA)
        c = 1/max(lam-bad_haar, lam*(1-DELTA))
        bad_density = beta/bad_haar if bad_haar else F(0)
        require(0 <= bad_density <= 1/lam <= c <= GLOBAL_CAP/lam,
                'BB pure-base bad domination and global Haar cap')
        require(c*(lam-bad_haar)+beta == 1, 'exact normalized row')
        rows[x] = dict(alpha=alpha, beta=beta, c=c, bad_haar=bad_haar,
                       bad_density=bad_density)
    row0, row2 = rows[X0], rows[CENTER]
    require(counts[X0] == 1 and row0['beta'] == 0
            and row0['c'] == 1/(1-2*s) <= F(8, 7), 'selected row stays uncharged')
    require(GLOBAL_CAP/lam >= F(15, 8)
            and (GLOBAL_CAP/lam-row0['c'])/P >= F(41, 952) > TRANSFER,
            'uniform whole-target-root capacity slack')
    require(row0['c']/P >= F(1, P) > TRANSFER/len(clean), 'positive donor root mass')
    require((row2['c']-row2['bad_density'])/P >= F(14, 187),
            'uniform dirty-spoke root gap at witness old2')
    rho = 1-sum(mu[x]*rows[x]['beta'] for x in points)
    require(rho >= F(len(clean), P) > 0, 'clean roots ensure actual survivors')
    return s, lam, clean, pure, mixed, family, rows, rho


def literal(H, points, divisors, old, mu, counts, epsilon):
    s, lam, clean, pure, mixed, family, rows, rho = data_at_height(
        H, points, divisors, old, mu, counts)
    q = P**H
    totals = [F(0), F(0)]
    bad_totals = [F(0), F(0)]
    good_totals = [F(0), F(0)]
    changed_points = positive_survivors = 0
    target_mass_change = F(0)
    for x in points:
        row_total = [F(0), F(0)]
        row_bad = [F(0), F(0)]
        pure_count = bad_count = 0
        for y in range(q):
            z = crt(x, M, y, q)
            require(all(z % d != a for d, a in old), 'old source support in literal CRT')
            pure_bad = any(z % d == a for d, a in pure)
            bad = any(z % d == a for d, a in mixed)
            require(not (pure_bad and bad), 'disjoint pure and mixed comb prefixes')
            pure_count += not pure_bad
            bad_count += bad
            bb = F(0) if pure_bad else (rows[x]['bad_density'] if bad else rows[x]['c'])/q
            change = F(0)
            if x == X0 and y % P == TARGET:
                change = TRANSFER/P**(H-1)
            elif x == X0 and y % P in clean:
                change = -TRANSFER/(len(clean)*P**(H-1))
            if change:
                require(not pure_bad and not bad, 'every changed point is an actual survivor')
                changed_points += 1
            candidate = bb+change
            if x == X0 and y % P == TARGET:
                target_mass_change += mu[x]*(candidate-bb)
            require(candidate >= 0 and candidate <= GLOBAL_CAP/(lam*q), 'global pointwise cap')
            if bad:
                require(candidate == bb <= 1/(lam*q), 'bad density and actual bad atoms unchanged')
            for i, weight in enumerate((bb, candidate)):
                row_total[i] += weight
                row_bad[i] += weight if bad else 0
                totals[i] += mu[x]*weight
                bad_totals[i] += mu[x]*weight if bad else 0
                good_totals[i] += mu[x]*weight if not pure_bad and not bad else 0
            positive_survivors += bb > 0 and not pure_bad and not bad
        require(F(pure_count, q) == lam and F(bad_count, q) == rows[x]['bad_haar'],
                'literal complete forbidden geometry')
        require(row_total == [F(1), F(1)] and row_bad == [rows[x]['beta']]*2,
                'same full old marginal and actual minimum row charge')
    require(totals == [F(1), F(1)] and bad_totals == [1-rho]*2 and good_totals == [rho]*2,
            'same actual survivor normalizer under both full laws')
    require(changed_points == (len(clean)+1)*P**(H-1)
            and target_mass_change == mu[X0]*TRANSFER > 0,
            'literal survivor restrictions and normalized laws really differ')
    return dict(height=H, period=M*q, literal_points=len(points)*q,
                original_forbidden_classes=family,
                original_complete_test_moduli=sorted([1]+[d for d, a in family]),
                all_labels=12*(H+1), changed_actual_survivor_points=changed_points,
                positive_supported_survivor_points=positive_survivors,
                physical_mass=totals[0], minimum_bad_charge=bad_totals[0],
                actual_survivor_mass=rho,
                conditional_target_root_mass_increase=target_mass_change/rho,
                conditioned_Gamma_decrease_at_least=epsilon/rho)


def evaluate(directory):
    raw = read_artifact_bytes(directory/SOURCE)
    source = json.loads(raw)
    require(source['schema'] == 'erdos7-mod3-conditioned-geometry-v1', 'source schema')
    cases = [case for case in source['cases'] if case['name'] == 'PG1']
    require(len(cases) == 1, 'one PG1 source')
    case = cases[0]
    points, weights = case['points'], case['weight_numerators']
    denominator = case['weight_denominator']
    old = [tuple(pair) for pair in case['family']]
    divisors = [d for d in range(1, M+1) if M % d == 0]
    require(len(divisors) == 12 and sorted(d for d, a in old) == divisors[1:], 'old inventory')
    require(points == [x for x in range(M) if all(x % d != a for d, a in old)]
            and len(points) == len(weights) == 75 and denominator == 1000000007
            and all(type(w) is int and w > 0 for w in weights)
            and sum(weights) == denominator, 'unchanged actual PG1 probability')
    mu = dict(zip(points, (F(w, denominator) for w in weights)))
    active = {x: [j for j, d in enumerate(divisors[1:], 1) if x % d == CENTER % d]
              for x in points}
    counts = {x: len(active[x]) for x in points}
    require(mu[X0] == F(16622259, denominator) and mu[CENTER] == F(13119398, denominator),
            'exact selected old masses')
    require(active[X0] == [1] and active[CENTER] == list(range(1, 12))
            and divisors[TARGET] == 5, 'good target and dirty-spoke witness for all heights')
    R0 = 12
    a = F(3*P-1, (P-1)**2)
    target_square_bound = R0**2*(1+P*a)
    deep_factor = P*(2*R0+R0*F(P+1, P-1))
    epsilon = 3*mu[X0]*TRANSFER/5
    increase = mu[X0]*TRANSFER*target_square_bound
    gaps = dict(dirty_spoke=3*mu[CENTER]*F(14, 187),
                pure_root=F(3, P), spine_root_at_height_at_least_two=F(3, P**2),
                misaligned_active_depth_one_label=2*mu[X0]/P)
    require(target_square_bound == F(4977, 8) and deep_factor == F(1275, 2),
            'exact all-height square and deeper-target bounds')
    require(all(gap > increase+epsilon for gap in gaps.values()),
            'every exceptional test class has enough uniform gap')
    require(TRANSFER*deep_factor < 2, 'pure-p/deep-label pair deficit absorbs all target gain')
    require(epsilon == F(49866777, 40960000286720) > 0, 'uniform strict gain')
    fixtures = []
    for H in [1, 2, 3, 16, 100]:
        s, lam, clean, _, _, family, rows, rho = data_at_height(H, points, divisors, old, mu, counts)
        fixtures.append(dict(height=H, s=s, pure_survival=lam, clean_roots=clean,
                             forbidden_label_count=len(family), complete_test_label_count=12*(H+1),
                             selected_good_Haar_density=rows[X0]['c'],
                             selected_row_charge=rows[X0]['beta'], actual_survivor_mass=rho,
                             conditioned_Gamma_decrease_at_least=epsilon/rho))
    return encode(dict(
        schema='erdos7-pg1-global-cap-improvement-v1',
        scope='Fixed PG1 source and center2 CS2 comb at p17, every finite H>=1. One kernel chosen before the complete global test. Physical max and actual survivor-conditioned max strictly decrease; no exact maximum or arbitrary-family result is asserted.',
        source_sha256={SOURCE: sha256(raw).hexdigest()},
        old_family=old, old_point_count=len(points), old_weight_denominator=denominator,
        old_divisors=divisors, forbidden_old_center=CENTER,
        selected_old_point=X0, selected_old_mass=mu[X0], witness_old_mass=mu[CENTER],
        delta=DELTA, global_density_cap=GLOBAL_CAP, transferred_row_mass=TRANSFER,
        target_root=TARGET, target_old_cofactor=5,
        target_root_capacity_slack_lower=F(41, 952),
        donor_root_mass_lower=F(1, P),
        constants=dict(target_conditional_square_upper=target_square_bound,
                       arbitrary_test_increase_upper=increase, test_class_gap_lower_bounds=gaps,
                       gap_margins={key: gap-increase-epsilon for key, gap in gaps.items()},
                       deep_target_gain_coefficient=deep_factor,
                       deep_pair_gap_margin=2-TRANSFER*deep_factor),
        uniform_comparisons=dict(physical_V_decrease_at_least=epsilon,
                                 conditioned_Gamma_decrease_at_least=epsilon,
                                 conditioned_sharper_decrease='epsilon / rho_H',
                                 f59over45_W483_cost_decrease_at_least=F(59, 45)*epsilon),
        exact_height_fixtures=fixtures,
        literal_CRT_replays=[literal(H, points, divisors, old, mu, counts, epsilon) for H in [1, 2]],
        all_height_proof='Three common-test cases: nonclean pure-p root; clean pure-p root with a misaligned active depth1 label; otherwise coherent depth1. In the last case remove at least3 mu0 t/r and absorb higher target gain by its missing pure-p cross pairs, using t*(1275/2)<2. The same argument applies before and after deleting actual bad points; the survivor normalizer is unchanged.'
    ))


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate certificate key: '+key)
        result[key] = value
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path, default=HERE/CERTIFICATE)
    parser.add_argument('--source-directory', type=Path, default=HERE)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = evaluate(args.source_directory)
    if args.write:
        write_certificate_text(args.certificate, json.dumps(result, indent=2)+'\n')
    else:
        stored = json.loads(read_artifact_text(args.certificate), object_pairs_hook=unique_object)
        require(json.dumps(stored, sort_keys=True) == json.dumps(result, sort_keys=True),
                'entire certificate equals exact recomputation')
    print(json.dumps(dict(uniform_physical_gain=result['uniform_comparisons']['physical_V_decrease_at_least'],
                          height_fixtures=len(result['exact_height_fixtures']),
                          literal_points=sum(x['literal_points'] for x in result['literal_CRT_replays']))))


if __name__ == '__main__':
    main()
