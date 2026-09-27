#!/usr/bin/env python3
"""Reproduce the equal-root, star-screened mixed-height certificate.

All arithmetic deciding a bound is exact.  The only maximum-exponent thresholds
examined are H=3 and H=4; each uses all 64 partitions of six named star slots.
The positive-exponent geometric tails are summed completely, not truncated.

Mathematical source contract (not established by these finite calculations):
For p in P, discard the actual forbidden p-root, or an arbitrary root when
modulus p is absent.  Give each remaining root mass 1/(p-1), condition Haar
inside it on EVERY actual pure-power survivor, and take the product rho.
This gives w(p)=1/(p-1), w(p^e)=1/((p-2)*p^(e-1)) for e>=2, and density
rho <= product_p p/(p-2) times Haar.

Complete the six auxiliary 3p stars as follows.  Retain every original star
whose cylinder has nonzero rho mass, and fill each other slot with a cylinder
using retained roots.  A completed auxiliary star is an additional constraint,
not a replacement of any original.  The submeasure is explicitly

    eta = rho * 1_(ALL actual mixed survivors) * 1_(auxiliary star survivors).

The two retained ternary roots partition the auxiliary stars into A0,A1.
For a support S, retain only star avoidance on coordinates outside S.
This gives the screen used below, also for arbitrary query cylinders.  The
source, auxiliary stars, original phases, and eta stay fixed throughout.

The target family permits all pure originals, all squarefree mixed originals,
and all mixed originals with maximum exponent >= H.  At H=4 the additional
actual mixed labels with maximum exponent 2 or 3 may have total w-weight
v <= 3/40.  Deleting these costs at most v in raw mass and cannot increase
any raw query maximum.

Continuation uses Report569 SD15--SD16's raw same-law count through 23,29:
(566*s-49*R)/567.  Its density conversion is adapted to the density of this
rho; Report569's own old source density is NOT reused.  After the complete
actual pure 23/29 conditioning the density multiplier is 616/567, hence

    Haar(full survivor) >= (566*s-49*R)/(616*D).

These are ordinary mathematical bounds with a finite rational consumer,
not Lean verification, an original-family search, or a proof of unrestricted
Erdos #7.  Negative certificate margins only mean this bound did not close.
"""

import argparse
from fractions import Fraction
from functools import reduce
import hashlib
import json
from operator import mul
from pathlib import Path

F = Fraction
P = (3, 5, 7, 11, 13, 17, 19)
Q = P[1:]
CUTOFFS = (3, 4)
G = F(566, 49)
EXTRA_WEIGHT = F(3, 40)
REPORT569 = (
    'docs/reports/erdos7-odd-covering/profile-notes/arithmetic/'
    '569-complete-suffix-debits-close-the-six-prime-query-target.md'
)


def product(values):
    return reduce(mul, values, F(1))


def power_weight(prime, exponent):
    if exponent == 1:
        return F(1, prime - 1)
    return F(1, (prime - 2) * prime ** (exponent - 1))


def coordinate_tail(prime, cutoff):
    """Sum of w(p^e) over EVERY e >= cutoff, for cutoff >= 2."""
    return F(1, (prime - 2) * (prime - 1) * prime ** (cutoff - 2))


def support_from_mask(mask):
    return tuple(prime for index, prime in enumerate(P) if mask >> index & 1)


SUPPORTS = tuple(support_from_mask(mask) for mask in range(1, 1 << len(P)))
MIXED_SUPPORTS = tuple(support for support in SUPPORTS if len(support) >= 2)
DENSITY = product(F(prime, prime - 2) for prime in P)
RAW_UNSCREENED_QUERY = product(F(prime - 1, prime - 2) for prime in P) - 1


def star_partition(mask):
    left = tuple(prime for index, prime in enumerate(Q) if mask >> index & 1)
    right = tuple(prime for prime in Q if prime not in left)
    return left, right


def star_union_complement(partition):
    return 1 - sum(
        product(1 - power_weight(prime, 1) for prime in group)
        for group in partition
    ) / 2


def star_union_inclusion_exclusion(mask):
    """Independent six-event intersection expansion on the same product law."""
    total = F(0)
    for chosen in range(1, 1 << len(Q)):
        selected = [index for index in range(len(Q)) if chosen >> index & 1]
        roots = {(mask >> index) & 1 for index in selected}
        if len(roots) != 1:
            continue  # Opposite ternary roots have empty intersection.
        intersection = F(1, 2) * product(
            power_weight(Q[index], 1) for index in selected
        )
        total += intersection if len(selected) % 2 else -intersection
    return total


def screen(partition, support):
    factors = [
        product(1 - power_weight(prime, 1)
                for prime in group if prime not in support)
        for group in partition
    ]
    # w(3^e) already includes the ternary root mass.
    return max(factors) if 3 in support else sum(factors) / 2


def support_tail(support, cutoff):
    return (
        product(F(1, prime - 2) for prime in support)
        - product(F(1, prime - 2) - coordinate_tail(prime, cutoff)
                  for prime in support)
    )


def unscreened_mixed_tail(cutoff):
    return (
        product(F(prime - 1, prime - 2) for prime in P)
        - product(F(prime - 1, prime - 2) - coordinate_tail(prime, cutoff)
                  for prime in P)
        - sum(coordinate_tail(prime, cutoff) for prime in P)
    )


def evaluate_partition(cutoff, mask):
    partition = star_partition(mask)
    star_loss = star_union_complement(partition)
    squarefree_other_loss = F(0)
    tail_loss = F(0)
    raw_query_bound = F(0)
    for support in SUPPORTS:
        factor = screen(partition, support)
        raw_query_bound += factor * product(F(1, prime - 2) for prime in support)
        if len(support) < 2:
            continue
        if not (len(support) == 2 and 3 in support):
            squarefree_other_loss += factor * product(
                power_weight(prime, 1) for prime in support
            )
        tail_loss += factor * support_tail(support, cutoff)
    loss_bound = star_loss + squarefree_other_loss + tail_loss
    mass_bound = 1 - loss_bound
    gate = G * mass_bound - raw_query_bound
    extra_mass_bound = mass_bound - EXTRA_WEIGHT
    extra_gate = G * extra_mass_bound - raw_query_bound
    return {
        'mask': mask,
        'star_groups': partition,
        'star_loss': star_loss,
        'squarefree_nonstar_loss': squarefree_other_loss,
        'mixed_tail_loss': tail_loss,
        'total_loss_bound': loss_bound,
        'mass_lower_bound': mass_bound,
        'raw_query_upper_bound': raw_query_bound,
        'normalized_query_upper_bound': raw_query_bound / mass_bound,
        'same_partition_gate_Gs_minus_R': gate,
        'haar_certificate_rhs': 49 * gate / (616 * DENSITY),
        'extra_shallow_weight_cap': EXTRA_WEIGHT,
        'extra_mass_lower_bound': extra_mass_bound,
        'extra_same_partition_gate_Gs_minus_R': extra_gate,
        'extra_haar_certificate_rhs': 49 * extra_gate / (616 * DENSITY),
    }


def extremum(rows, key, minimize):
    value = (min if minimize else max)(row[key] for row in rows)
    return {'value': value, 'masks': [row['mask'] for row in rows if row[key] == value]}


def summarize(rows):
    result = {
        'maximum_loss': extremum(rows, 'total_loss_bound', False),
        'maximum_normalized_query': extremum(rows, 'normalized_query_upper_bound', False),
        'minimum_same_partition_gate': extremum(rows, 'same_partition_gate_Gs_minus_R', True),
        'minimum_haar_certificate_rhs': extremum(rows, 'haar_certificate_rhs', True),
        'minimum_extra_gate': extremum(rows, 'extra_same_partition_gate_Gs_minus_R', True),
        'minimum_extra_haar_certificate_rhs': extremum(rows, 'extra_haar_certificate_rhs', True),
    }
    result['extra_raw_weight_open_budget'] = result['minimum_same_partition_gate']['value'] / G
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    return value


def build_result():
    rows = {cutoff: [evaluate_partition(cutoff, mask) for mask in range(64)]
            for cutoff in CUTOFFS}
    summaries = {cutoff: summarize(items) for cutoff, items in rows.items()}
    checks = {}

    def require(name, condition):
        if not condition:
            raise ArithmeticError('Certificate check failed: ' + name)
        checks[name] = True

    require('complete_coordinate_geometric_tail_recurrence', all(
        coordinate_tail(prime, cutoff)
        == power_weight(prime, cutoff) + coordinate_tail(prime, cutoff + 1)
        for prime in P for cutoff in CUTOFFS
    ))
    require('complete_unscreened_query_profile', RAW_UNSCREENED_QUERY == F(3161, 935))
    require('product_density_cap_constant', DENSITY == F(1729, 135))
    require('six_star_union_matches_inclusion_exclusion', all(
        star_union_complement(star_partition(mask)) == star_union_inclusion_exclusion(mask)
        for mask in range(64)
    ))
    require('support_screen_probability_bounds', all(
        0 < screen(star_partition(mask), support) <= 1
        for mask in range(64) for support in SUPPORTS
    ))
    require('complete_mixed_tail_support_expansion_matches_product_complement', all(
        sum(support_tail(support, cutoff) for support in MIXED_SUPPORTS)
        == unscreened_mixed_tail(cutoff) for cutoff in CUTOFFS
    ))
    numeric_keys = tuple(key for key, value in rows[3][0].items() if isinstance(value, F))
    require('exchange_of_retained_ternary_roots_preserves_every_bound', all(
        all(items[mask][key] == items[63 - mask][key] for key in numeric_keys)
        for items in rows.values() for mask in range(64)
    ))
    require('screened_query_does_not_exceed_unscreened_profile', all(
        row['raw_query_upper_bound'] <= RAW_UNSCREENED_QUERY
        for items in rows.values() for row in items
    ))
    require('positive_retained_mass_in_declared_finite_cases', all(
        row['extra_mass_lower_bound'] > 0 for items in rows.values() for row in items
    ))
    require('H4_joint_loss_extremum_regression', summaries[4]['maximum_loss'] == {
        'value': F(55858334259429305368613, 82085191914103297920000), 'masks': [1, 62]
    })
    require('H4_same_partition_gate_extremum_regression',
            summaries[4]['minimum_same_partition_gate'] == {
                'value': F(53315162291526157368887, 60942036421076690880000),
                'masks': [0, 63]
            })
    require('H4_normalized_query_extremum_regression',
            summaries[4]['maximum_normalized_query'] == {
                'value': F(93480587078394050344810, 10353555939642996897083),
                'masks': [0, 63]
            })
    require('H3_certificate_does_not_close', summaries[3]['minimum_same_partition_gate'] == {
        'value': F(-4080113763416126899, 3732033666449088000), 'masks': [0, 63]
    })
    require('H4_uniform_positive_Haar_above_one_over_185',
            summaries[4]['minimum_haar_certificate_rhs']['value'] > F(1, 185))
    require('extra_shallow_three_over_forty_leaves_positive_gate',
            summaries[4]['minimum_extra_gate']['value'] > 0)
    require('extra_shallow_three_over_forty_Haar_above_one_over_19000',
            summaries[4]['minimum_extra_haar_certificate_rhs']['value'] > F(1, 19000))
    require('same_law_continuation_density_conversion', all(
        row['haar_certificate_rhs']
        == ((566 * row['mass_lower_bound'] - 49 * row['raw_query_upper_bound']) / 567)
        / (DENSITY * F(22, 21) * F(28, 27))
        for items in rows.values() for row in items
    ))

    return {
        'schema': 'screened-root-profile-v1',
        'verification_kind': 'exact finite arithmetic; ordinary proof premises; no Lean verification',
        'source': {
            'program_name': Path(__file__).name,
            'program_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'continuation_reference': {'path': REPORT569, 'equations': ['SD15', 'SD16']},
        },
        'contract': {
            'eta': 'rho times ALL actual mixed survivor mask times auxiliary star survivor mask',
            'auxiliary_stars': 'retain every rho-active actual 3p star; fill other slots on retained roots',
            'scope': 'all pure originals, all squarefree mixed originals, all mixed max-exponent>=H originals; all originals touching23 or29',
            'extra_shallow_scope_H4': 'actual mixed labels with maximum exponent2 or3; sum w(m)<=3/40',
            'same_source': 'one fixed rho, auxiliary-star layout, original family and submeasure for all queries',
            'negative_margin': 'certificate not closed; no actual covering counterexample inferred',
        },
        'constants': {
            'P': P, 'Q': Q, 'cutoffs': CUTOFFS, 'partitions_per_cutoff': 64,
            'continuation_threshold_G': G, 'density_cap_D': DENSITY,
            'raw_unscreened_query_cap': RAW_UNSCREENED_QUERY,
            'extra_shallow_weight_cap': EXTRA_WEIGHT,
        },
        'cutoff_results': {
            cutoff: {'complete_unscreened_mixed_tail': unscreened_mixed_tail(cutoff),
                     'summary': summaries[cutoff], 'partitions': items}
            for cutoff, items in rows.items()
        },
        'checks': checks,
        'check_count': len(checks),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'),
                        help='JSON result path; defaults to this program basename with .json')
    args = parser.parse_args()
    result = build_result()
    args.output.write_text(json.dumps(encode(result), indent=2, sort_keys=True) + '\n', encoding='utf-8')
    summary = result['cutoff_results'][4]['summary']
    print(f"H=3,4; 64 partitions each; {result['check_count']} exact checks passed.")
    print('H4: max query/mass={:.12f}; min gate={:.12f}; Haar>1/185.'.format(
        float(summary['maximum_normalized_query']['value']),
        float(summary['minimum_same_partition_gate']['value']),
    ))
    print('Extra shallow weight <=3/40: positive gate and Haar>1/19000.')
    print('Result:', args.output)


if __name__ == '__main__':
    main()
