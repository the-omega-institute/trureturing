#!/usr/bin/env python3
"""Exact scalar-profile obstruction to improving the first13 PA loss bound.

The two-atom witness is an abstract load measure, not a query realized
by original congruences. Report567 proves the all-real-threshold claim.
"""
import argparse
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json


checks = {}


def check(name, condition):
    if name in checks or not condition:
        raise ValueError(name)
    checks[name] = True


def scalar_data(x, y):
    # Full mean and the only low atoms needed for thresholds1,2,3.
    mass = x * y
    mean = (x + F(1, 4)) * (y + F(1, 6)) * F(7, 6)
    atom1 = (x - F(1, 5)) * (y - F(1, 7)) * F(28, 33)
    atom2 = (F(4, 25) * (y - F(1, 7)) * F(28, 33)
             + (x - F(1, 5)) * F(6, 49) * F(28, 33)
             + (x - F(1, 5)) * (y - F(1, 7)) * F(50, 363))
    f1 = mean - mass
    f2 = mean - 2 * mass + atom1
    f3 = mean - 3 * mass + 2 * atom1 + atom2
    a11 = mass - F(1, 12) - (x / 42 + y / 20 + F(59, 840)) / 3
    return dict(x=x, y=y, auxiliary_mass=mass, full_mean=mean,
                atom1=atom1, atom2=atom2, F1=f1, F2=f2, F3=f3,
                A11=a11, p4=f2 / 2, clipped_optimum=f2 / 4,
                p1_lower=a11 - f2 / 2,
                hinge1_slack=f1 - 3 * f2 / 2,
                hinge3_slack=f3 - f2 / 2)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=Path(__file__).with_name(
        'row13_seventeen_projection_clipping.json'))
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    corners = [scalar_data(x, y) for x, y in
               product((F(1, 2), F(1)), (F(2, 3), F(1)))]
    for i, row in enumerate(corners):
        for field in ('p1_lower', 'hinge1_slack', 'hinge3_slack', 'F2'):
            check(f'positive_corner_{i}_{field}', row[field] > 0)
        check(f'prefix_interval_{i}', row['A11'] <= row['auxiliary_mass'])
        check(f'atom4_clipped_attainment_{i}', F(1, 2) * row['p4'] == row['clipped_optimum'])

    source = json.loads(args.source.read_text())['H5']
    x, y, actual_mass = (F(source[key]) for key in ('x', 'y', 'lambda11'))
    actual = scalar_data(x, y)
    p1 = actual_mass - actual['p4']
    check('H5_prefix_lower', actual_mass >= actual['A11'])
    check('H5_prefix_upper', actual_mass <= x * y)
    check('H5_two_nonnegative_atoms', p1 > 0 and actual['p4'] > 0)
    check('H5_exact_mass', p1 + actual['p4'] == actual_mass)
    check('H5_existing_F13', actual['F2'] == F(source['F13']))
    check('H5_1_hinge', 3 * actual['p4'] <= actual['F1'])
    check('H5_2_hinge', 2 * actual['p4'] == actual['F2'])
    check('H5_3_hinge', actual['p4'] <= actual['F3'])
    check('H5_4_hinge_zero', sum(weight * max(point - 4, 0)
                              for point, weight in ((1, p1), (4, actual['p4']))) == 0)
    kreq = F(6168733163201163811, 1650097635185615616000)
    cut = F(source['credit']) + F(source['S11']) + actual['F2'] / 4 - kreq
    check('H5_cut_from_existing_margin', cut == F(source['clip']) + F(source['margin']))
    check('H5_exact_cut', cut == F(649004327923538200529792761,
                                  14267500448564292689760000000))
    check('H5_relaxed_clip_exceeds_cut', actual['clipped_optimum'] > cut)
    actual.update(actual_prefix_mass=actual_mass, witness_atoms=[[1, p1], [4, actual['p4']]],
                  sufficient_clip_cut=cut, excess_over_cut=actual['clipped_optimum'] - cut)
    result = dict(corners=corners, H5=actual, checks=checks, check_count=len(checks),
        scope='Exact optimum F2/4 of the scalar relaxation: mass m in [A11,xy] and every real stop-loss bounded by the complete PA auxiliary profile. Not a realizable-query optimum, actual-family counterexample, or Lean result.')
    args.output.write_text(json.dumps(result, default=str, indent=2) + '\n')
    print('H5 scalar optimum', actual['clipped_optimum'], float(actual['clipped_optimum']))
    print('H5 sufficient cut', cut, float(cut))
    print('H5 excess', actual['excess_over_cut'], float(actual['excess_over_cut']))
    print('checks', len(checks))


if __name__ == '__main__':
    main()
