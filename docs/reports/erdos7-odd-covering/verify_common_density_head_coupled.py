#!/usr/bin/env python3
"""Check the fixed common-density head certificate with exact rationals.

Python 3.9+ standard library only. No solver, network or external imports.
The accompanying proof supplies the common-law density and layout meaning;
this checks the profile recurrence, support budgets, all infinite cell sums,
six nonnegative density-row multipliers, bound corrections and continuation.
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
from itertools import combinations, product
from math import prod
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def subsets(s):
    for n in range(len(s) + 1):
        yield from combinations(s, n)

def envelope_sums(primes, c, b):
    """Exact R and K from ordinary and first-ternary-projection coefficients."""
    cutoffs = {}
    for p in primes:
        others = tuple(q for q in primes if q != p)
        ratios = [c[tuple(sorted(t + (p,)))] / c[t] for t in subsets(others)]
        if p == 3:
            ratios += [3 * c[t] / b[t] for t in b]
        else:
            ratios += [b[tuple(sorted(t + (p,)))] / b[t]
                       for t in subsets(others) if 3 in t]
        cutoff = 1 if p == 3 else 0
        while p ** (cutoff + 1) < max(ratios):
            cutoff += 1
        cutoffs[p] = cutoff

    total = moment = F(0)
    for states in product(*(range(cutoffs[p] + 2) for p in primes)):
        exponents = dict(zip(primes, states))
        high = tuple(p for p in primes if exponents[p] == cutoffs[p] + 1)
        low = tuple(p for p in primes if 0 < exponents[p] <= cutoffs[p])
        terms = []
        for t in subsets(low):
            support = tuple(sorted(high + t))
            terms.append(c[support] / prod(p ** exponents[p] for p in t))
            if 3 in t and 3 not in high:
                terms.append(b[support] /
                             (3 * prod(p ** exponents[p] for p in t if p != 3)))
        cell = weighted_cell = min(terms)
        for p in high:
            cell *= F(1, p ** cutoffs[p] * (p - 1))
            weighted_cell *= F((2 * cutoffs[p] + 3) * (p - 1) + 2,
                               p ** cutoffs[p] * (p - 1) ** 2)
        for p in low:
            weighted_cell *= 2 * exponents[p] + 1
        total += cell
        moment += weighted_cell
    return total - 1, moment, cutoffs

def head_recurrence(primes, pair_bounds, density_bound):
    """Keep cylinder envelopes separate from bounds on their actual sums."""
    profiles = {(): ({(): F(1)}, {})}
    metrics = {(): (F(0), F(1))}
    for size in range(1, len(primes) + 1):
        for support in combinations(primes, size):
            candidates = []
            for p in support:
                old = tuple(q for q in support if q != p)
                if old not in profiles:
                    continue
                survival = 1 - metrics[old][0] / (p - 2)
                if survival <= 0:
                    continue
                old_c, old_b = profiles[old]
                c, b = {(): F(1)}, {}
                for t in subsets(support):
                    if not t:
                        continue
                    previous = tuple(q for q in t if q != p)
                    factor = (F(p - 1, p - 2) if p in t else F(1)) / survival
                    c[t] = old_c[previous] * factor
                    if 3 in t:
                        b[t] = (old_c[previous] if p == 3 else old_b[previous]) * factor
                candidates.append((c, b))
            require(candidates, "no certified survivor normalization for a subset")
            c = {t: min(cc[t] for cc, _ in candidates) for t in subsets(support)}
            b = {t: min(bb[t] for _, bb in candidates)
                 for t in subsets(support) if 3 in t}
            if size == 2 and 3 in support:
                q = next(p for p in support if p != 3)
                b[(3,)] = min(b[(3,)], F(6 * (q - 2), 3 * q - 8))
            profiles[support] = c, b
            r, k, _ = envelope_sums(support, c, b)
            if size == 2 and 3 in support:
                joint_r, joint_k = pair_bounds[next(p for p in support if p != 3)]
                r, k = min(r, joint_r), min(k, joint_k)
            if support == (3, 5, 7):
                r = min(r, density_bound)
            metrics[support] = r, k
    return profiles, metrics



def compute_certificate():
    primes = (3, 5, 7, 11)
    pair = {5: (F(15, 7), F(173, 12)), 7: (F(21, 13), F(19, 2)),
            11: (F(33, 25), F(181, 25))}
    profiles, metrics = head_recurrence(primes, pair, F(1649, 360))
    c, b = profiles[primes]
    _, old_k, cutoff = envelope_sums(primes, c, b)
    require(old_k == F(187719326, 1723053), 'Original profile moment mismatch')
    require(cutoff == {3: 2, 5: 1, 7: 0, 11: 0}, 'Unexpected profile cutoffs')
    lower35 = 1 - F(1, 3)
    lower357 = lower35 * (1 - F(15, 7) / 5)
    lowerfull = lower357 * (1 - F(1649, 360) / 9)
    t_max = 1 / lowerfull
    require(lower357 == F(8, 21) and t_max == F(8505, 1591), 'Density lower bounds failed')

    def uncovered_budget(scope, collection):
        return sum(prod(F(1, p - 2) for p in support)
                   for support in subsets(scope) if len(support) >= 2 and
                   not any(set(support) <= set(member) for member in collection))

    budgets = {
        'outside_57_in_357': uncovered_budget((3, 5, 7), ((5, 7),)),
        'all_pairs_in_357': uncovered_budget((3, 5, 7), ((3, 5), (3, 7), (5, 7))),
        'cover_35_57_3711': uncovered_budget(primes, ((3, 5), (5, 7), (3, 7, 11))),
        'cover_35_3711_5711': uncovered_budget(primes, ((3, 5), (3, 7, 11), (5, 7, 11))),
    }
    require(budgets == {'outside_57_in_357': F(3, 5), 'all_pairs_in_357': F(1, 15),
        'cover_35_57_3711': F(7, 45), 'cover_35_3711_5711': F(1, 9)},
        'An exact-support union budget is incorrect')

    # Coordinates are t followed by all pair/triple normalized densities.
    names = ('t', '35', '37', '311', '57', '511', '711', '357', '3511', '3711', '5711')
    index = {name: i for i, name in enumerate(names)}
    def density_name(support):
        return 't' if len(support) <= 1 else ''.join(map(str, support))
    def vector(coefficients):
        return [F(coefficients.get(name, 0)) for name in names]

    # Each selected cell uses one actual complement-density projection.
    selected = {
        (0, 0, 0, 1): (11,), (0, 1, 0, 0): (5,),
        (0, 1, 0, 1): (5, 11), (0, 2, 0, 0): (5,),
        (0, 2, 0, 1): (5, 11), (2, 0, 0, 1): (3, 11),
        (3, 0, 0, 0): (3,), (3, 0, 0, 1): (3, 11),
        (3, 2, 0, 0): (3, 5), (3, 2, 0, 1): (3, 5, 11),
    }
    constant = F(1)
    seven_positive_weight = F(6, 5) * F(3 * 7 - 1, (7 - 1) ** 2)
    eleven_complete_weight = 1 + F(10, 9) * F(3 * 11 - 1, (11 - 1) ** 2)
    transport_coefficient = F(55, 4) * seven_positive_weight * eleven_complete_weight
    require(transport_coefficient == F(671, 54), 'Positive-seven layout transport mismatch')
    objective = vector({'35': transport_coefficient})
    observed = set()
    selected_rows, profile_rows = [], []
    for state in product(*(range(cutoff[p] + 2) for p in primes)):
        if state[2] != 0 or not any(state):
            continue
        exponents = dict(zip(primes, state))
        high = tuple(p for p in primes if exponents[p] == cutoff[p] + 1)
        low = tuple(p for p in primes if 0 < exponents[p] <= cutoff[p])
        terms = []
        for subset in subsets(low):
            support = tuple(sorted(high + subset))
            terms.append(c[support] / prod(p ** exponents[p] for p in subset))
            if 3 in subset and 3 not in high:
                terms.append(b[support] /
                             (3 * prod(p ** exponents[p] for p in subset if p != 3)))
        weight = prod(F((2 * cutoff[p] + 3) * (p - 1) + 2,
                        p ** cutoff[p] * (p - 1) ** 2) for p in high)
        weight *= prod(2 * exponents[p] + 1 for p in low)
        if state in selected:
            observed.add(state)
            support = selected[state]
            require(set(high) <= set(support) <= set(high + low), 'Invalid projection support')
            coefficient = prod(F(p - 1, p - 2) for p in support)
            coefficient /= prod(p ** exponents[p] for p in support if p not in high)
            complement = tuple(p for p in primes if p not in support)
            variable = density_name(complement)
            objective[index[variable]] += weight * coefficient
            selected_rows.append({'cell': list(state), 'projection': list(support),
                'complement_variable': variable, 'coefficient': str(coefficient),
                'infinite_weight': str(weight), 'weighted_coefficient': str(weight * coefficient)})
        else:
            constant += weight * min(terms)
            profile_rows.append({'cell': list(state), 'profile_upper_bound': str(min(terms)),
                'infinite_weight': str(weight), 'contribution': str(weight * min(terms))})
    require(observed == set(selected), 'A selected finite/tail cell was omitted')
    require(constant == F(332692, 7955), 'Unselected profile-cell total mismatch')
    require(objective == vector({'t': F(704, 6075), '35': F(671, 54),
        '37': F(56, 135), '57': F(32, 45), '711': F(44, 135),
        '357': F(16, 45), '3711': F(7, 6), '5711': F(8, 9)}),
        'Density objective mismatch')

    # Six mathematical inequalities; every scalar multiplier is nonnegative.
    rows = [
        ('append_7', vector({'35': 1 - metrics[(3, 5)][0] / 5, '357': -1}), F(0), F(854, 45)),
        ('outside_57_in_357', vector({'57': 1, '357': -1, 't': -budgets['outside_57_in_357']}), F(0), F(1, 54)),
        ('all_pairs_in_357', vector({'35': 1, '37': 1, '57': 1, '357': -1, 't': -(2 + budgets['all_pairs_in_357'])}), F(0), F(56, 135)),
        ('append_11', vector({'357': 1 - F(1649, 360) / 9}), F(1), F(64044, 1591)),
        ('cover_35_57_3711', vector({'35': 1, '57': 1, '3711': 1, 't': -(2 + budgets['cover_35_57_3711'])}), F(1), F(5, 18)),
        ('cover_35_3711_5711', vector({'35': 1, '3711': 1, '5711': 1, 't': -(2 + budgets['cover_35_3711_5711'])}), F(1), F(8, 9)),
    ]
    aggregate = [F(0)] * len(names)
    rhs = F(0)
    for name, row, upper, multiplier in rows:
        require(multiplier >= 0, 'Negative certificate multiplier')
        aggregate = [a + multiplier * r for a, r in zip(aggregate, row)]
        rhs += multiplier * upper
    residual = [o - a for o, a in zip(objective, aggregate)]
    require(residual == vector({'t': F(21017, 6075), '711': F(44, 135)}),
            'Six-row dual residual mismatch')
    require(min(residual) >= 0, 'Unexpected negative residual')
    head = constant + rhs + sum(residual) * t_max
    require(head == F(4939031, 47730) < F(5015891, 47730), 'New exact head failed')

    ratio = head
    bridge = []
    for p, delta in ((67, F(1, 4)), (71, F(53, 200)), (73, F(27, 100))):
        require(0 < delta < 1, 'Continuation threshold is outside (0,1)')
        previous = ratio
        survival = 1 - ratio / (4 * delta * (1 - delta) * (p - 1) ** 2)
        require(survival > 0, 'Continuation survival denominator is not positive')
        ratio *= (1 + F(3 * p - 1, (p - 1) ** 2) / (1 - delta)) / survival
        bridge.append({'prime': p, 'delta': str(delta), 'input': str(previous),
                       'survival_fraction': str(survival), 'output': str(ratio)})
    require(ratio < F(138877, 1000), 'Prime-73 continuation exceeds the tail seed')
    return {
        'schema': 'erdos7-common-density-head-v1', 'prime_support': list(primes),
        'analytical_inputs': {'pair_R_K': {str(p): list(map(str, values)) for p, values in pair.items()},
            'R357': '1649/360', 'Gamma35': '55/4'},
        'ordinary_profile': {'*'.join(map(str, support)) or '1': str(value) for support, value in c.items()},
        'first_ternary_profile': {'*'.join(map(str, support)): str(value) for support, value in b.items()},
        'old_profile_K': str(old_k), 'cutoffs': {str(p): value for p, value in cutoff.items()},
        'lambda_lower_bounds': {'35': str(lower35), '357': str(lower357), 'full': str(lowerfull)},
        'exact_uncovered_support_budgets': {name: str(value) for name, value in budgets.items()},
        'positive_seven_transport': {'seven_weight': str(seven_positive_weight),
            'eleven_weight': str(eleven_complete_weight), 'v35_coefficient': str(transport_coefficient)},
        'selected_density_cells': selected_rows, 'remaining_profile_cells': profile_rows,
        'unit_term': '1', 'constant': str(constant), 'density_variable_order': list(names),
        'objective': list(map(str, objective)),
        'density_dual': [{'name': name, 'row': list(map(str, row)),
            'upper_bound': str(upper), 'multiplier': str(multiplier)}
            for name, row, upper, multiplier in rows],
        'density_dual_rhs': str(rhs), 'density_dual_residual': list(map(str, residual)),
        'variable_bound_corrections': [{'variable': name, 'coefficient': str(value),
            'upper_bound': str(t_max), 'contribution': str(value * t_max)}
            for name, value in zip(names, residual) if value],
        'head_bound': str(head), 'previous_head_bound': '5015891/47730',
        'head_improvement': str(F(5015891, 47730) - head), 'bridge': bridge,
        'prime_73_threshold': '138877/1000',
        'prime_73_threshold_margin': str(F(138877, 1000) - ratio),
    }


def main():
    data = json.loads(read_artifact_text(Path(__file__).resolve().parent / 'certificates/common_density_head_coupled_certificate.json'))
    expected = compute_certificate()
    require(data == expected, 'Fixed common-density certificate differs from exact reconstruction')
    print('Verified six common-density rows and all infinite cylinder cells; Gamma <= ' + expected['head_bound'] + '.')
    print('Positive prime-67/71/73 denominators; F73 = ' + expected['bridge'][-1]['output'] + ' < 138877/1000.')


if __name__ == '__main__':
    main()
