#!/usr/bin/env python3
"""Exact two-head-coordinate attachment fees above the entry prime53.

Finite parent-label truncations retain every child exponent. An analytic
rectangle bound pays all entry primes from971 onward without a height or
prime-count cutoff. This is ordinary proof arithmetic, not Lean verification.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from heapq import heappop, heappush
import json
from math import isqrt
from pathlib import Path

FIRST_ENTRY = 53
RECTANGLE_START = 22
FINITE_STOP = 2 * RECTANGLE_START**2 + 3


def parent_prefix(count, primes=(3, 5)):
    pending = [1]
    seen = {1}
    labels = []
    while len(labels) < count:
        value = heappop(pending)
        for p in primes:
            child = value * p
            if child not in seen:
                seen.add(child)
                heappush(pending, child)
        if value > 1:
            labels.append(value)
    return labels


def exponent_pair(value, primes=(3, 5)):
    pair = []
    for p in primes:
        exponent = 0
        while value % p == 0:
            value //= p
            exponent += 1
        pair.append(exponent)
    if value != 1:
        raise ArithmeticError('not a literal parent label')
    return pair


def is_prime(value):
    return value >= 2 and all(value % d for d in range(2, isqrt(value) + 1))


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
                        default=base / 'twelve_vertex_attachment_kernel.json')
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    checks = {}

    def require(name, predicate):
        if not predicate:
            raise ArithmeticError(name)
        checks[name] = True

    require('analytic_boundary_971', FINITE_STOP == 971)
    labels = parent_prefix(FINITE_STOP)
    require('strictly_ordered_distinct_parent_labels',
            labels == sorted(set(labels)) and labels[0] == 3)
    # Independent bounded grid enumeration verifies that no smaller label
    # was missed by the priority queue. Bounds are derived from its last value.
    grid = []
    p3 = 1
    while p3 <= labels[-1]:
        value = p3
        while value <= labels[-1]:
            if value > 1:
                grid.append(value)
            value *= 5
        p3 *= 3
    require('complete_heap_prefix_matches_exponent_grid', sorted(grid) == labels)
    pairs = [exponent_pair(value) for value in labels]
    require('literal_label_roundtrip',
            all(3**a * 5**b == value for value, (a, b) in zip(labels, pairs)))
    total = F(3,2) * F(5,4) - 1
    require('complete_nonunit_parent_reciprocal_mass', total == F(7,8))
    tails = [total]
    for value in labels:
        tails.append(tails[-1] - F(1,value))
    require('positive_remaining_infinite_parent_tails', min(tails) > 0)
    primes = [q for q in range(FIRST_ENTRY, FINITE_STOP) if is_prime(q)]
    # Sieve verification does not use the trial-division predicate.
    sieve = [True] * FINITE_STOP
    sieve[0] = sieve[1] = False
    for d in range(2, isqrt(FINITE_STOP - 1) + 1):
        if sieve[d]:
            for multiple in range(d*d, FINITE_STOP, d):
                sieve[multiple] = False
    require('complete_finite_prime_inventory',
            primes == [q for q in range(FIRST_ENTRY, FINITE_STOP) if sieve[q]]
            and len(primes) == 148 and primes[-1] == 967)
    rows = []
    for q in primes:
        fee, count = min((tails[n] / (q - 3 - n), n) for n in range(q - 3))
        require(f'positive_shallow_reserve_{q}', q - 3 - count > 0)
        require(f'actual_truncation_identity_{q}',
                fee == (total - sum((F(1,d) for d in labels[:count]),F()))
                / (q - 3 - count) and fee > 0)
        rows.append(dict(entry_prime=q,shallow_parent_label_count=count,
                         last_shallow_label=labels[count-1] if count else None,
                         remaining_parent_reciprocal_mass=tails[count],
                         reserve_denominator=q-3-count,blocker_fee_upper=fee))
    finite_fee = sum((row['blocker_fee_upper'] for row in rows),F())
    require('finite_fee_exact', finite_fee == F(
        26367566679970603998162514215695685748991796027092345257,
        715166192625059001701426870634865611791610717773437500000000))
    # All odd q>=2*n0**2+3 are grouped in square intervals. This arithmetic
    # evaluates the analytic geometric bound proved in the accompanying text.
    tail_fee = F(135,8 * RECTANGLE_START * 3**RECTANGLE_START)
    require('analytic_tail_exact', tail_fee == F(5,204558018192))
    require('square_interval_boundary',
            2*RECTANGLE_START**2+3 == FINITE_STOP
            and 2*(RECTANGLE_START+1)**2+1 < 2*(RECTANGLE_START+1)**2+3)
    pair_fee = finite_fee + tail_fee

    head_bytes = args.head.read_bytes()
    head = json.loads(head_bytes)
    require('head_checks_true', bool(head['checks'])
            and all(v is True for v in head['checks'].values()))
    require('head_producer_fingerprint',
            sha256(args.head.with_suffix('.py').read_bytes()).hexdigest()
            == head['producer_sha256'])
    head_density = F(head['consequence']['head_density_lower'])
    ordinary_fee = F(head['consequence']['attachment_fee_upper'])
    old_extendible = F(head['consequence']['extendible_head_lower'])
    require('same_head_and_single_port_reserve',
            head_density-ordinary_fee == old_extendible and ordinary_fee == F(1,2**17))
    new_extendible = old_extendible-pair_fee
    require('simultaneous_two_port_reserve_positive', new_extendible > 0)
    require('simultaneous_two_port_reserve_gt_1_90000', new_extendible > F(1,90000))

    # Low entries can all be admitted when their two head parents avoid3.
    # Their ordered pair is then at least(5,7). The >=53 table is unchanged.
    low_labels = parent_prefix(47, (5, 7))
    low_grid = []
    p5 = 1
    while p5 <= low_labels[-1]:
        value = p5
        while value <= low_labels[-1]:
            if value > 1:
                low_grid.append(value)
            value *= 7
        p5 *= 5
    require('low_parent_prefix_complete', sorted(low_grid) == low_labels)
    low_total = F(5,4) * F(7,6) - 1
    low_tails = [low_total]
    for value in low_labels:
        low_tails.append(low_tails[-1] - F(1,value))
    require('low_parent_total', low_total == F(11,24) and min(low_tails) > 0)
    low_primes = [q for q in range(37,53) if is_prime(q)]
    require('all_low_entry_primes', low_primes == [37,41,43,47])
    low_rows = []
    for q in low_primes:
        fee, count = min((low_tails[n] / (q-3-n),n) for n in range(q-3))
        require(f'low_entry_positive_reserve_{q}', q-3-count > 0 and fee > 0)
        require(f'low_entry_original_label_identity_{q}',
                fee == (low_total - sum((F(1,d) for d in low_labels[:count]),F()))
                / (q-3-count))
        low_rows.append(dict(entry_prime=q,shallow_parent_label_count=count,
                             last_shallow_label=low_labels[count-1] if count else None,
                             remaining_parent_reciprocal_mass=low_tails[count],
                             reserve_denominator=q-3-count,blocker_fee_upper=fee))
    low_fee = sum((row['blocker_fee_upper'] for row in low_rows),F())
    require('low_fee_exact', low_fee == F(5241874291,463242937500000))
    expanded_extendible = new_extendible-low_fee
    require('expanded_reserve_gt_1_2500000', expanded_extendible > F(1,2500000))
    result = dict(schema='two-parent-entry-attachment-v1',
                  scope=dict(minimum_entry_prime=FIRST_ENTRY,
                             parent_coordinates='Any two distinct head primes; lower comparison3,5',
                             low_entry_extension='Entries37,41,43,47 also allowed when neither head parent is3',
                             entry_domains='One actual private descendant domain per entry prime',
                             head_touching_originals='Supported on its two head parents and its entry prime',
                             branches='Pairwise disjoint exterior prime sets; ordinary single-port branches also allowed',
                             all_original_heights='Unbounded finite; no numerical label or phase merged',
                             excluded='Arbitrary multiple-entry shared separators and unrestricted Erdos7',
                             lean_verified=False),
                  source=dict(file=args.head.name,sha256=sha256(head_bytes).hexdigest(),
                              producer_sha256=head['producer_sha256']),
                  parent_label_prefix=[dict(modulus=value,exponents=pair)
                                       for value,pair in zip(labels,pairs)],
                  finite_rows=rows,
                  analytic_tail=dict(rectangle_start=RECTANGLE_START,
                                     first_odd_entry=FINITE_STOP,
                                     bound=tail_fee,
                                     formula='135 / (8 n0 3^n0)'),
                  consequence=dict(finite_two_port_fee=finite_fee,
                                   total_two_port_fee=pair_fee,
                                   head_density_lower=head_density,
                                   ordinary_attachment_fee=ordinary_fee,
                                   extendible_head_lower=new_extendible,
                                   strictly_greater_than=F(1,90000),
                                   full_density_lower='extendible_head_lower / Q_outside'),
                  low_entry_extension=dict(parent_comparison=[5,7],
                                           parent_label_prefix=[dict(modulus=d,exponents=exponent_pair(d,(5,7)))
                                                                for d in low_labels],
                                           rows=low_rows,fee=low_fee,
                                           expanded_extendible_head_lower=expanded_extendible,
                                           strictly_greater_than=F(1,2500000),
                                           full_density_lower='expanded_extendible_head_lower / Q_outside'),
                  checks=checks,producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(result),indent=2)+'\n')
    print(json.dumps(encode(dict(checks=len(checks),prime_rows=len(rows),
                                finite_fee=finite_fee,analytic_tail=tail_fee,
                                extendible_head_lower=new_extendible,
                                strictly_greater_than=F(1,90000),
                                low_fee=low_fee,expanded_reserve=expanded_extendible,
                                expanded_strictly_greater_than=F(1,2500000)))))


if __name__ == '__main__':
    main()
