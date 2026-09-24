#!/usr/bin/env python3
"""Fixed scalar and actual-geometry controls for clipped query payments.

The 45-root control verifies one sharp seven-label configuration. The
arithmetic does not certify a replacement sampler or the general query target.
"""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    alpha = F(7235955529, 6075000000000)
    target = F(565, 51)
    s4 = F(1, 3) + F(1, 5) + F(1, 7) + F(1, 9)
    s5 = s4 + F(1, 11)
    s6 = s5 + F(1, 13)
    s7 = s6 + F(1, 15)
    stationary_cost = 5 + 13 * (F(12, 13) - s5)
    maximum_upper = F(17, 4) + stationary_cost
    band_upper = maximum_upper + F(9, 8)
    small_beta_lower = 6 + 15 * (1 - F(1, 400) - s6) + F(9, 2)
    kappa = F(272, 1001)
    s3 = s4 - F(1, 9)
    outside_s3 = F(1, 17) + F(1, 19) + F(1, 21)
    c0 = 15 + 16 * kappa - 9 * s3 - 25 * outside_s3
    left_lower = c0 - F(1, 4) + F(56, 27)
    right_lower = c0 - F(5, 2) + F(118, 27)
    sharp_classes = [(3, 0), (9, 1), (5, 0), (15, 2)]
    sharp_survivors = [x for x in range(45)
                       if all(x % d != phase for d, phase in sharp_classes)]
    other_pure_survival = F(6, 7) * F(10, 11) * F(12, 13)
    checks = {
        'D7_sharp_root_count': len(sharp_survivors) == 17,
        'D7_sharp_complete_survivor': F(len(sharp_survivors), 45) * other_pure_survival == kappa,
        'D7_universal_bound_arithmetic': (F(8, 15) - F(4, 45) - F(1, 15)) * other_pure_survival == kappa,
        'D7_mass_above_quarter': kappa > F(1, 4),
        'D7_support_constant': c0 == F(45031219, 4849845),
        'D7_left_margin': left_lower - target == F(5364739, 174594420) > 0,
        'D7_right_margin': right_lower - target == F(6723907, 87297210) > 0,
        'D7_right_minus_left': right_lower - left_lower == F(5, 108),
        'two_term_log_two_lower': 2 * (F(1, 3) + F(1, 81)) == F(56, 81),
        'only_active_labels_11_13_15': s4 < F(659, 800) and s7 > 1,
        'low_branch_increases': 1 - s6 < F(1, 15),
        'middle_stationary_point': 1 - s6 < F(1, 13) < 1 - s5,
        'high_branch_decreases': 1 - s5 > F(1, 11),
        'maximum_cost': stationary_cost == F(19346, 3465),
        'log_maximum_argument': 1 / (13 * alpha) < F(5248, 81),
        'exponential_17_over_4_lower': F(8, 3)**4 * F(41, 32) == F(5248, 81),
        'max_upper_below_10': maximum_upper == F(136289, 13860) < 10,
        'alpha_third_band_below_target': band_upper < target,
        'euler_upper': F(49, 18) < F(11, 4),
        'exp_9_over_2_bound': F(11, 4)**4 * F(5, 3) == F(73205, 768) < 100,
        'small_beta_active_seventh_label': s6 < F(399, 400) < s7,
        'small_beta_endpoint_above_target': small_beta_lower > target,
        'large_h_small_beta_above_target': F(23, 2) > target,
        'large_h_log_argument': 3**7 * 2 < F(16000, 3),
    }
    if not all(checks.values()):
        raise ValueError(checks)
    result = {
        'scope': 'Fixed arithmetic and one actual D7 sharpness configuration; no parameter scan, general phase enumeration or query-law construction',
        'S4': str(s4),
        'S5': str(s5),
        'S6': str(s6),
        'S7': str(s7),
        'stationary_h': '1/13',
        'stationary_cost': str(stationary_cost),
        'minimum_over_beta_maximum_upper': str(maximum_upper),
        'alpha_third_band_upper': str(band_upper),
        'alpha_third_band_margin': str(target - band_upper),
        'alpha_hundredth_small_h_lower': str(small_beta_lower),
        'alpha_hundredth_small_h_margin': str(small_beta_lower - target),
        'D7_support': {
            'kappa': str(kappa),
            'inside_first_three_reciprocal_sum': str(s3),
            'outside_first_three_reciprocal_sum': str(outside_s3),
            'support_constant': str(c0),
            'excluded_h_interval': ['1/100', '1/10'],
            'left_lower': str(left_lower),
            'left_margin': str(left_lower - target),
            'right_lower': str(right_lower),
            'right_margin': str(right_lower - target),
        },
        'D7_sharpness': {
            'three_five_classes': [{'modulus': d, 'residue': a} for d, a in sharp_classes],
            'roots_inspected': 45,
            'surviving_roots': sharp_survivors,
            'other_pure_classes': [{'modulus': p, 'residue': 0} for p in (7, 11, 13)],
            'other_pure_survivor_mass': str(other_pure_survival),
            'complete_survivor_mass': str(F(len(sharp_survivors), 45) * other_pure_survival),
        },
        'checks': checks,
    }
    content = json.dumps(result, indent=2) + '\n'
    if args.output is None:
        print(content, end='')
    else:
        args.output.write_text(content, encoding='utf-8')


if __name__ == '__main__':
    main()
