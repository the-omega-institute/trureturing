#!/usr/bin/env python3
"""Conditional kernels for eleven children and the Report598 dense head.

Sixty exact equal-cap boundary rows complement Chapter23's analytic range.
The resulting fee permits twelve-vertex blocks at arbitrary attachment
depth. This is ordinary proof arithmetic, not a new Lean certificate.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from math import comb
from pathlib import Path

CHILDREN = 11
MINIMUM_CHILD = 37
ANALYTIC_START = CHILDREN * (CHILDREN + 3) + 3


def numerator_recurrence(k, denominator, cutoff):
    """z[n] = denominator**n times the n-coordinate avoidance polynomial."""
    z = [1]
    for n in range(1, k + 1):
        z.append((denominator - cutoff) * z[-1]
                 - (cutoff + 1) * sum(comb(n - 1, j - 1) * z[n - j]
                                      for j in range(2, n + 1)))
    load = sum(comb(k, j) * z[k - j] for j in range(1, k + 1))
    return z, load


def partition_residuals(k, denominator, cutoff):
    """Independently sum signed support partitions by occupied set size."""
    coefficients = [1]
    for n in range(1, k + 1):
        coefficients.append(-cutoff * coefficients[-1]
                            - (cutoff + 1) * sum(comb(n - 1, j - 1)
                                                * coefficients[n - j]
                                                for j in range(2, n + 1)))
    return [sum(F(comb(n, j) * coefficients[j], denominator**j)
                for j in range(n + 1)) for n in range(k + 1)]


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    base = Path(__file__).parent
    parser.add_argument('--head', type=Path,
                        default=base / 'central_high_support_augmentation.json')
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    checks = {}

    def require(name, condition):
        if not condition:
            raise ArithmeticError(name)
        checks[name] = True

    require('analytic_threshold_157', ANALYTIC_START == 157)
    rows = []
    for s in range(MINIMUM_CHILD, ANALYTIC_START, 2):
        denominator = s - 3
        fee = F(1, 2**((s - 1) // 2))
        candidates = []
        for cutoff in range(1, (s - 3) // 2 + 1):
            nums, load_num = numerator_recurrence(CHILDREN, denominator, cutoff)
            if min(nums) <= 0:
                continue
            cost = F(load_num, 2 * 3**cutoff * nums[-1])
            if cost < fee:
                candidates.append((cost / fee, cutoff, nums, load_num, cost))
        require(f'positive_kernel_exists_{s}', bool(candidates))
        ratio, cutoff, nums, load_num, cost = min(candidates)
        residuals = [F(numerator, denominator**n)
                     for n, numerator in enumerate(nums)]
        load = F(load_num, denominator**CHILDREN)
        require(f'all_coordinate_residuals_positive_{s}',
                len(residuals) == CHILDREN + 1 and min(residuals) > 0)
        require(f'independent_partition_sum_{s}',
                residuals == partition_residuals(CHILDREN, denominator, cutoff))
        require(f'original_support_load_{s}',
                load == sum(F(comb(CHILDREN, j), denominator**j)
                            * residuals[CHILDREN - j]
                            for j in range(1, CHILDREN + 1)))
        require(f'positive_strict_fee_margin_{s}',
                cutoff >= 1 and cost == load / (2 * 3**cutoff * residuals[-1])
                and 0 < cost < fee)
        rows.append(dict(minimum_child=s,cutoff=cutoff,cap=F(1,denominator),
                         residuals=residuals,load=load,parent3_blocker_upper=cost,
                         fee=fee,fee_ratio=ratio,margin=fee-cost))
    require('complete_sixty_odd_boundary_rows',
            len(rows) == 60 and [r['minimum_child'] for r in rows]
            == list(range(37, 157, 2)))
    worst = max(rows, key=lambda row: row['fee_ratio'])
    require('worst_row_exact', worst['minimum_child'] == 37
            and worst['cutoff'] == 12
            and worst['parent3_blocker_upper'] == F(49074500591689,17621384873374478358)
            and worst['fee_ratio'] == F(6432292941553860608,8810692436687239179))
    require('worst_ratio_below_three_quarters', worst['fee_ratio'] < F(3,4))

    head_bytes = args.head.read_bytes()
    head = json.loads(head_bytes)
    require('head_recorded_checks_true', bool(head['checks'])
            and all(v is True for v in head['checks'].values()))
    head_producer = args.head.with_suffix('.py')
    require('head_producer_fingerprint',
            sha256(head_producer.read_bytes()).hexdigest() == head['producer_sha256'])
    density = F(head['consequence']['haar_lower'])
    require('head_density_gt_1_18000', density > F(1,18000))
    attachment_fee = F(1,2**17)
    require('odd_tail_geometric_fee',
            attachment_fee == F(1,2**18) / (1 - F(1,2)))
    extendible = density - attachment_fee
    require('extendible_head_gt_1_21000', extendible > F(1,21000))
    require('extendible_head_exact',
            extendible == F(22770908741233363852242307711,
                            468579418066477236879360000000000))

    data = dict(schema='twelve-vertex-attachment-kernel-v1',
                scope=dict(children_at_most=CHILDREN,vertices_at_most=CHILDREN+1,
                           minimum_actual_child_prime=MINIMUM_CHILD,
                           finite_boundary='Every odd minimum from37 through155',
                           analytic_range='minimum>=157, Chapter23 CK23--CK30 with eleven children',
                           padding='Unused larger dummy primes; only the actual minimum is charged',
                           larger_blocks='k children with minimum>=k(k+3)+3',
                           heights_and_original_phases='Arbitrary finite heights; globally fixed arbitrary phases',
                           measure_boundary='Bound on extendible head Haar; full Haar requires division by outside period',
                           lean_verified=False,unrestricted_erdos7_resolved=False),
                sources=dict(head_file=args.head.name,
                             head_sha256=sha256(head_bytes).hexdigest(),
                             head_producer_sha256=head['producer_sha256']),
                child_count=CHILDREN,analytic_start=ANALYTIC_START,
                boundary_rows=rows,worst_ratio_row=worst,
                consequence=dict(head_density_lower=density,
                                 attachment_fee_upper=attachment_fee,
                                 extendible_head_lower=extendible,
                                 strictly_greater_than=F(1,21000),
                                 full_density_lower='extendible_head_lower / Q_outside'),
                checks=checks,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(data),indent=2)+'\n')
    print(json.dumps(encode(dict(rows=len(rows),checks=len(checks),
                                 worst_ratio=worst['fee_ratio'],
                                 extendible_head_lower=extendible,
                                 strictly_greater_than=F(1,21000)))))


if __name__ == '__main__':
    main()
