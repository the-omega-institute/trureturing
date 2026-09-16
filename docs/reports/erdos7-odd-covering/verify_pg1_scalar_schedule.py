#!/usr/bin/env python3
"""Exact SH28 scalar consumer for all255 final17/19 threshold schedules.

Keep one PG1 law, the certified square/mean/integer hinges, fixed11/T4
and13/T5, and all15*17 admissible final thresholds. Retain every auxiliary
tail through its exact probability and mean. At13/N2, improve only the
positive charge above the convex base W0=f*a*c; the negative energy term
is not independently pooled with a different layout optimum.

The finite outcomes concern this sufficient scalar-feature functional.
They neither lower-bound actual moments nor exclude richer joint costs.
Default: exact certificate replay. --write explicitly regenerates it.
Uses only Python's standard library; -O preserves every require check.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import prod
from pathlib import Path
import argparse
import json

HERE = Path(__file__).resolve().parent
SCHEMA = 'erdos7-pg1-scalar-schedule-v1'
SOURCES = ('pg1_integer_hinges_certificate.json',
           'pg1_exact_depth100_certificate.json',
           'pg1_joint_tail_certificate.json',
           'original9_conditioned_geometry_certificate.json')


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def sources(directory, expected_hashes):
    """Read all actual inputs and validate each declared prerequisite hash."""
    data, hashes = {}, {}

    def read(name, expected=None):
        require(Path(name).name == name, 'adjacent source filename')
        if name not in hashes:
            raw = (directory / name).read_bytes()
            hashes[name] = sha256(raw).hexdigest()
            if name.endswith('.json'):
                item = json.loads(raw)
                data[name] = item
                links = item.get('source_sha256')
                if isinstance(links, dict):
                    for child, stamp in links.items():
                        require(isinstance(stamp, str) and len(stamp) == 64, 'prerequisite hash')
                        read(child, stamp)
        if expected is not None:
            require(hashes[name] == expected, 'source prerequisite hash: ' + name)

    for name in SOURCES:
        read(name)
    hashes = dict(sorted(hashes.items()))
    if expected_hashes is not None:
        require(hashes == expected_hashes, 'all hash-bound source inputs')
    return data, hashes


def auxiliary(prefix, threshold):
    """Exact probabilities below threshold; all remaining mass and mean."""
    probabilities, mean = {1: F(1)}, F(1)
    for p, cap in prefix:
        following = {}
        require(0 < cap <= p, 'unclipped auxiliary height law is a probability')
        for n, probability in probabilities.items():
            for factor in range(1, (threshold-1)//n+1):
                mass = 1-cap/p if factor == 1 else cap*F(p-1, p**factor)
                following[n*factor] = following.get(n*factor, F()) + probability*mass
        probabilities = following
        mean *= 1+cap/(p-1)
    if threshold == 1:
        probabilities = {}
    tail_mass = 1-sum(probabilities.values(), F())
    tail_mean = mean-sum((n*v for n, v in probabilities.items()), F())
    require(all(1 <= n < threshold and value >= 0 for n, value in probabilities.items())
            and tail_mass >= 0 and tail_mean >= threshold*tail_mass,
            'complete auxiliary probability and first-moment tails')
    return probabilities, mean, tail_mass, tail_mean


def feature_value(values, hinges, mean, nonnegative=False):
    first = values[2]-values[1]
    coefficients = [values[j+1]-2*values[j]+values[j-1] for j in range(2, len(values)-1)]
    if nonnegative:
        require(first >= 0 and all(c >= 0 for c in coefficients),
                'nonnegative discrete mean and hinge coefficients')
    value = values[1]+first*(mean-1)
    value += sum((c*hinges[j] for j, c in zip(range(2, len(values)-1), coefficients)), F())
    return value, min([first]+coefficients)


def build_step(p, threshold, future, prefix, hinges, mean, whole_n2):
    d = p-1-threshold
    require(1 <= threshold <= p-2, 'admissible integer threshold')
    cap, a = F(p-1, d), F(3*p-1, (p-1)**2)
    require(cap <= p, 'physical prefix cap')
    minimum_W = future*a*cap
    probabilities, auxiliary_mean, tail_mass, tail_mean = auxiliary(prefix, threshold)
    A, B, features = F(), F(), []
    base_minimum = None
    for n, probability in sorted(probabilities.items()):
        end = (threshold+n-1)//n
        charge = [None] + [F(max(n*j-threshold, 0), d) for j in range(1, end+2)]
        energy = [None] + [future*a*(F(p-1, p-1-min(n*j, threshold))-cap)
                           for j in range(1, end+2)]
        base = [None] + [minimum_W*charge[j]+energy[j] for j in range(1, end+2)]
        charge_bound, _ = feature_value(charge, hinges, mean, True)
        base_bound, minimum = feature_value(base, hinges, mean, True)
        base_minimum = minimum if base_minimum is None else min(base_minimum, minimum)
        improvement = F()
        if p == 13 and threshold == 5 and n == 2:
            require(charge_bound == (hinges[2]+hinges[3])/d,
                    'integer identity (2L-5)+ = (L-2)+ + (L-3)+')
            improvement = max(F(), charge_bound-whole_n2/d)
            charge_bound -= improvement
        # h_W = h_W0 + (W-W0)*charge, with both coefficients valid
        # at W>=W0. Only the second term gets the whole-N2 improvement.
        A += probability*charge_bound
        B += probability*(base_bound-minimum_W*charge_bound)
        features.append((n, probability, end, charge, energy, improvement))
    tail_A = (mean*tail_mean-threshold*tail_mass)/d
    require(tail_A >= 0, 'nonnegative complete affine auxiliary tail')
    A += tail_A
    row = {'prime': p, 'threshold': threshold, 'd': d, 'cap': cap, 'a': a,
           'future_multiplier': future, 'A': A, 'B': B, 'minimum_W': minimum_W,
           'auxiliary_probabilities': probabilities, 'auxiliary_mean': auxiliary_mean,
           'tail_probability': tail_mass, 'tail_mean': tail_mean, 'tail_A': tail_A,
           'minimum_base_feature_coefficient': F() if base_minimum is None else base_minimum,
           'whole_n2_charge_improvement': sum((pr*im for _, pr, _, _, _, im in features), F())}
    return row, features


def verify_at(row, features, W, hinges, mean):
    require(W >= row['minimum_W'], 'continuous convexity at the final W')
    p, threshold, d = row['prime'], row['threshold'], row['d']
    a, cap, future = row['a'], row['cap'], row['future_multiplier']
    total, minimum = F(), None
    for n, probability, end, charge, energy, improvement in features:
        values = [None] + [W*charge[j]+energy[j] for j in range(1, end+2)]
        bound, smallest = feature_value(values, hinges, mean, True)
        first = values[2]-values[1]
        coefficients = [values[j+1]-2*values[j]+values[j-1] for j in range(2, end+1)]
        # Beyond end both sides are affine with slope W*n/d. The finite
        # check below covers every change of slope and its affine suffix.
        require(values[-1]-values[-2] == W*F(n, d), 'final affine feature slope')
        for k in range(1, 2*end+4):
            direct = W*F(max(n*k-threshold, 0), d)
            direct += future*a*(F(p-1, p-1-min(n*k, threshold))-cap)
            recovered = values[1]+first*(k-1)
            recovered += sum((c*max(k-j, 0) for j, c in zip(range(2, end+1), coefficients)), F())
            require(direct == recovered, 'complete integer feature identity')
        bound -= (W-row['minimum_W'])*improvement
        total += probability*bound
        minimum = smallest if minimum is None else min(minimum, smallest)
    total += W*row['tail_A']
    require(total == row['A']*W+row['B'], 'direct final-W evaluation equals affine coefficients')
    return total, F() if minimum is None else minimum


def json_row(row):
    return {key: {str(k): str(v) for k, v in value.items()} if isinstance(value, dict)
            else str(value) if isinstance(value, F) else value for key, value in row.items()}


def evaluate(directory, expected_hashes=None):
    data, hashes = sources(directory, expected_hashes)
    integer, square, joint, original = (data[name] for name in SOURCES)
    require(integer['schema'] == 'erdos7-pg1-integer-hinges-v1'
            and square['schema'] == 'erdos7-pg1-exact-depth100-v1'
            and joint['schema'] == 'erdos7-pg1-joint-tail-v1'
            and original['schema'] == 'erdos7-original9-conditioned-geometry-v1', 'source schemas')
    require(original['source_case'] == 'PG1'
            and original['source_sha256'] == hashes['mod3_conditioned_geometry_certificate.json'],
            'one unchanged PG1 law')
    ih, sq, jt, old = (item['result'] for item in (integer, square, joint, original))
    q0 = F(old['survival_lower'])
    require(q0 == F(ih['source_survival_lower']) == F(sq['source_survival_lower'])
            == F(jt['source_survival_lower']) > 0, 'same actual source-survival denominator')
    G, mean, H2 = F(sq['Gamma_upper']), F(old['hinge2']['mean_upper']), F(old['hinge2']['H2_upper'])
    require(mean == 5 and H2 == 3 and G >= 1, 'simultaneous certified source moments')
    observed = {int(t): F(value) for t, value in ih['conditional_hinge_upper_bounds'].items()}
    require(set(observed) == {3, 4, 6, 7, 8} and min(observed.values()) >= 0, 'five integer hinge observations')
    whole = jt['unweighted_whole_cost']['lambda_upper']
    H5, whole_n2 = F(whole['1'])/q0, F(whole['2'])/q0
    require(ih['reused_H5']['source'] == SOURCES[2]
            and F(ih['reused_H5']['conditional_upper']) == H5, 'same-law inherited whole-N1 and whole-N2 bounds')
    known = {1: mean-1, 2: H2, 5: H5, **observed}
    hinges = {}
    for t in range(1, 18):
        candidates = [G/F(4*t)] + [v for s, v in known.items() if s <= t]
        hinges[t] = min(candidates)
    require(hinges[1] <= mean-1 and min(hinges.values()) >= 0,
            'monotonicity and square-majorant hinge completion')
    outcomes = []
    for T17, T19 in product(range(1, 16), range(1, 18)):
        schedule = [(11, 4), (13, 5), (17, T17), (19, T19)]
        growth = [1+F(3*p-1, (p-1)*(p-1-t)) for p, t in schedule]
        P, prefix, steps, feature_sets = prod(growth), [], [], []
        for i, (p, t) in enumerate(schedule):
            row, features = build_step(p, t, prod(growth[i+1:]), prefix, hinges, mean, whole_n2)
            steps.append(row)
            feature_sets.append(features)
            prefix.append((p, row['cap']))
        A, B = sum((s['A'] for s in steps), F()), sum((s['B'] for s in steps), F())
        D0, minimum_W = P*G-1+B, max(s['minimum_W'] for s in steps)
        # A positive intercept makes A>=1 impossible even without imposing
        # the convexity lower bound. This statement concerns this functional.
        require(D0 > 0, 'positive affine intercept for every tested schedule')
        output = {'T17': T17, 'T19': T19, 'P': str(P), 'A': str(A), 'B': str(B),
                  'positive_intercept': str(D0), 'minimum_W': str(minimum_W),
                  'Gamma_upper': None, 'W': None, 'criterion_residual': None,
                  'minimum_final_feature_coefficient': None,
                  'status': 'no-positive-W-for-this-functional', 'steps': [json_row(s) for s in steps]}
        if A < 1:
            W = max(minimum_W, D0/(1-A))
            verified = [verify_at(s, fs, W, hinges, mean) for s, fs in zip(steps, feature_sets)]
            residual = P*G-1+sum((v for v, _ in verified), F())-W
            require(residual <= 0, 'complete SH28 criterion at the final W')
            output.update({'Gamma_upper': str(1+W), 'W': str(W), 'criterion_residual': str(residual),
                           'minimum_final_feature_coefficient': str(min(v for _, v in verified)),
                           'status': 'finite-sufficient-bound'})
        outcomes.append(output)
    require(len(outcomes) == len({(r['T17'], r['T19']) for r in outcomes}) == 255, 'complete threshold domain')
    finite = [r for r in outcomes if r['Gamma_upper'] is not None]
    require(finite, 'at least one finite sufficient scalar bound')
    best = min(finite, key=lambda r: F(r['Gamma_upper']))
    return {'schema': SCHEMA, 'source_sha256': hashes,
            'result': {'source_case': 'PG1', 'source_survival_lower': str(q0), 'source_Gamma_upper': str(G),
                       'source_mean_upper': str(mean), 'source_hinge2_upper': str(H2),
                       'certified_hinges': {str(t): str(v) for t, v in sorted(known.items())},
                       'completed_hinges': {str(t): str(v) for t, v in sorted(hinges.items())},
                       'whole_N2_upper': str(whole_n2), 'fixed_thresholds': [[11, 4], [13, 5]],
                       'threshold17_range': [1, 15], 'threshold19_range': [1, 17],
                       'schedules': len(outcomes), 'finite_bounds': len(finite),
                       'bounds_below484': sum(F(r['Gamma_upper']) < 484 for r in finite),
                       'bounds_at_most271': sum(F(r['Gamma_upper']) <= 271 for r in finite),
                       'minimum_positive_intercept': str(min(F(r['positive_intercept']) for r in outcomes)),
                       'best_thresholds': [best['T17'], best['T19']], 'best_Gamma_upper': best['Gamma_upper'],
                       'best_A': best['A'], 'best_B': best['B'], 'outcomes_sha256': digest(outcomes),
                       'outcomes': outcomes,
                       'scope': 'Exact SH28 scalar-feature upper functional on one fixed PG1 law for all255 integer17/19 schedules after fixed11/4,13/5. Complete auxiliary probability/mean tails and arbitrary finite physical heights. Every finite result checks convexity and nonnegative integer feature coefficients at its finalW. The existing13/N2 whole-cost bound improves only the positive-charge part above the convex base. Failure of this sufficient functional is not a lower bound on actual moments, an obstruction to richer joint observations, or an unrestricted-prime covering result.'}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path, default=HERE / 'pg1_scalar_schedule_certificate.json')
    parser.add_argument('--source-directory', type=Path, default=HERE)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    expected = None if args.write else json.loads(args.certificate.read_text())
    if expected is not None:
        require(expected['schema'] == SCHEMA, 'certificate schema')
    actual = evaluate(args.source_directory, None if expected is None else expected['source_sha256'])
    if args.write:
        args.certificate.write_text(json.dumps(actual, indent=2) + '\n')
    else:
        require(actual == expected, 'all exact schedule outcomes and source bindings')
    result = actual['result']
    print(json.dumps({key: result[key] for key in ('schedules', 'finite_bounds', 'bounds_below484',
                                                  'bounds_at_most271', 'best_thresholds', 'best_Gamma_upper')}, sort_keys=True))


if __name__ == '__main__':
    main()
