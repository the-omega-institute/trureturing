#!/usr/bin/env python3
"""Fixed arithmetic for a mixed-chain moment and actual two-chain controls.

The general cylinder, irredundancy, entropy and maximum-phase arguments
are ordinary proofs. This program does not enumerate a CRT period.
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
    a = F(212731, 110592)
    e_lower = F(8, 3)
    e_upper = F(11, 4)
    pure_ceiling = 2 / (3 - e_upper) - F(1, 2)
    mixed_ceiling = 1 + (pure_ceiling - 1) / 5
    product_ceiling = pure_ceiling * mixed_ceiling
    h6 = F(13, 30) + F(1, 2 * 3**6)
    h8 = F(13, 30) + F(1, 2 * 3**8)
    lambda6 = F(6, 5) * sum((F(1, 3**j) for j in range(1, 7)), F())
    rho_unused_upper = (F(39, 20) - F(59, 100)) / F(13, 30)
    atom_unused_upper = 9 * F(39, 20) - 4
    mixture_entropy_upper = F(9, 5)
    mixture_G_upper = F(9, 10) * rho_unused_upper + F(1, 10) * atom_unused_upper + mixture_entropy_upper
    mixture_density_upper = F(9, 10) * F(30, 13) + F(1, 10) * (5 * 3**6)
    maximum_phase_gap = F(1, 10) - F(9, 10) / 13
    n6_moment_lower = e_lower**12 / (5 * 3**6)
    n8_moment_lower = e_lower**16 / (5 * 3**8)
    checks = {
        'finite_euler_upper': F(49, 18) < e_upper < 3,
        'separate_pure_ceiling': pure_ceiling == F(15, 2),
        'separate_mixed_ceiling': mixed_ceiling == F(23, 10),
        'separate_product_ceiling': product_ceiling == F(69, 4),
        'n6_joint_exceeds_separate_product': n6_moment_lower > product_ceiling,
        'n8_joint_exceeds_one_hundred': n8_moment_lower > 100,
        'n8_all_labels_shallow': 5 * 3**8 == 32805 < 10**9,
        'both_survivors_above_thirteen_thirtieths': h6 > F(13, 30) and h8 > F(13, 30),
        'Haar_complete_query_ceiling': F(39, 20) / F(13, 30) == F(9, 2),
        'Haar_entropy_below_one_argument': F(30, 13) < e_lower,
        'log_Lambda_above_six_argument': 3**6 < 800 < 1 / alpha,
        'n6_reciprocal_sum': lambda6 == F(728, 1215) > F(59, 100),
        'n6_uniform_cylinder_query_factor': F(15, 2) * F(9, 4) * F(8, 15) == 9,
        'n6_unused_rho_ceiling': rho_unused_upper == F(204, 65),
        'n6_unused_cylinder_ceiling': atom_unused_upper == F(271, 20),
        'n6_cylinder_entropy_below_nine_argument': 5 * 3**6 < e_lower**9,
        'n6_mixture_G_ceiling': mixture_G_upper == F(15547, 2600) < 6,
        'n6_mixture_density': mixture_density_upper == F(9531, 26) < 800,
        'n6_all_zero_maximum_phase_gap': maximum_phase_gap == F(2, 65) > 0,
        'retained_A_bound': a < F(39, 20),
    }
    if not all(checks.values()):
        raise ValueError(checks)
    result = {
        'scope': 'Two fixed n instances and rational entropy/moment comparisons; no phase or CRT-period enumeration',
        'separate_pure_ceiling': str(pure_ceiling),
        'separate_mixed_ceiling': str(mixed_ceiling),
        'separate_product_ceiling': str(product_ceiling),
        'n6': {
            'period': 5 * 3**6,
            'original_count': 12,
            'survivor_mass': str(h6),
            'reciprocal_sum': str(lambda6),
            'joint_moment_lower': str(n6_moment_lower),
            'joint_minus_separate_margin': str(n6_moment_lower - product_ceiling),
            'mixture_weight': '1/10',
            'mixture_density_upper': str(mixture_density_upper),
            'mixture_G_upper': str(mixture_G_upper),
            'mixture_G_margin_below_six': str(6 - mixture_G_upper),
            'all_zero_maximum_phase_gap': str(maximum_phase_gap),
        },
        'n8': {
            'largest_original': 5 * 3**8,
            'original_count': 16,
            'survivor_mass': str(h8),
            'joint_moment_lower': str(n8_moment_lower),
            'joint_margin_above_one_hundred': str(n8_moment_lower - 100),
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
