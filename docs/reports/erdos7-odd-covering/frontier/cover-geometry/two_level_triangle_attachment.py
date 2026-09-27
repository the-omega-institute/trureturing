#!/usr/bin/env python3
"""Exact full-prime budget for two levels of shared two-coordinate interfaces.

The accompanying ordinary proof supplies all-height and same-source semantics.
This certificate checks literal parent-label tails and the complete arithmetic
reserve; it does not claim Lean verification.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from heapq import heappop, heappush
import json
from math import isqrt
from pathlib import Path


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def smooth_prefix(pair, count):
    pending, seen, result = [1], {1}, []
    while len(result) < count:
        d = heappop(pending)
        for p in pair:
            if p*d not in seen:
                seen.add(p*d)
                heappush(pending, p*d)
        if d > 1:
            result.append(d)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir', type=Path, default=Path(__file__).parent)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    checks = {}

    def require(name, value):
        if not value:
            raise ArithmeticError(name)
        checks[name] = True

    source_path = args.source_dir / 'staged_two_parent_attachment.json'
    raw = source_path.read_bytes()
    prior = json.loads(raw)
    require('source_checks_true', bool(prior['checks'])
            and all(v is True for v in prior['checks'].values()))
    require('source_producer_fingerprint', prior['producer_sha256']
            == sha256(source_path.with_suffix('.py').read_bytes()).hexdigest())
    old_simple = F(prior['consequence']['simple_extendible_head_lower'])
    old_exact = F(prior['consequence']['extendible_head_lower'])
    require('inherited_simple_reserve', old_exact > old_simple
            == F(31991, 2048000000))
    alpha = F(prior['constants']['alpha'])
    c = F(prior['constants']['c'])
    early_density = F(prior['constants']['early_pair_density'])
    beta = alpha*(1-c)*early_density
    require('early_continuation_loss_at_most_full_haar_loss',
            beta == F(46191477, 720966400) and 0 < beta < 1)

    n0, boundary = 22, 971
    require('tail_covers_every_odd_child_from971', 2*n0*n0+3 == boundary)
    primes = [p for p in range(37, boundary)
              if all(p%d for d in range(2, isqrt(p)+1))]
    sieve = [True]*boundary
    sieve[0] = sieve[1] = False
    for d in range(2, isqrt(boundary-1)+1):
        if sieve[d]:
            for k in range(d*d, boundary, d):
                sieve[k] = False
    require('complete_parent_and_child_prime_lists', len(primes) == 152
            and primes == [p for p in range(37, boundary) if sieve[p]])
    parent_rows = {}
    for tag in ('3_5', '3_23'):
        rows = prior['fee_tables'][tag]['finite_rows']
        require(tag+'_complete_parent_rows', [r['entry_prime'] for r in rows] == primes)
        parent_rows[tag] = {}
        for row in rows:
            q, count = row['entry_prime'], row['selected_label_count']
            denom = q-3-count
            amplification = F(q-1, denom)
            require(f'{tag}_selected_parent_denominator_{q}',
                    denom >= 1 and amplification <= q-1
                    and F(row['reciprocal_tail'])/denom == F(row['blocker_fee_upper']))
            parent_rows[tag][q] = amplification

    pair = (3, 37)
    complete_mass = F(37, 24)
    labels = smooth_prefix(pair, boundary)
    grid = []
    pa = 1
    while pa <= labels[-1]:
        value = pa
        while value <= labels[-1]:
            if value > 1:
                grid.append(value)
            value *= pair[1]
        pa *= pair[0]
    require('3_37_literal_prefix_agrees_with_exponent_grid', sorted(grid) == labels
            and len(set(labels)) == len(labels))
    tails = [complete_mass-1]
    for d in labels:
        tails.append(tails[-1]-F(1, d))
    require('3_37_all_complete_tails_positive', min(tails) > 0)
    rows = []
    for s in primes[1:]:
        fee, count = min((tails[n]/(s-3-n), n) for n in range(s-3))
        choices = [(amp, tag, q) for tag, table in parent_rows.items()
                   for q, amp in table.items() if q < s]
        amplification, maximizing_tag, maximizing_q = max(choices)
        require(f'child_{s}_complete_reciprocal_tail',
                tails[count] == complete_mass-1-sum((F(1, d) for d in labels[:count]), F())
                and count < s-3 and fee > 0)
        require(f'child_{s}_both_stages_all_smaller_parent_entries',
                len(choices) == 2*sum(q < s for q in primes)
                and all(amp <= amplification < s for amp, tag, q in choices))
        rows.append(dict(child_prime=s, selected_label_count=count,
                         reciprocal_tail=tails[count], pair_blocker_fee=fee,
                         inherited_amplification=amplification,
                         maximizing_parent_prime=maximizing_q,
                         maximizing_parent_table=maximizing_tag,
                         final_head_fee=amplification*fee))
    finite = sum((row['final_head_fee'] for row in rows), F())
    # For n>=22 the interval's weighted factor is <=4n+11, since
    # (4n+11)(n^2+1)-(2n+1)(2n^2+4n+3)=(n-2)(n-4)>=0.
    # Sum_{n>=n0}(4n+11)3^-n = (12n0+39)/(2*3^n0).
    x = F(1, 3)
    geometric = x**n0/(1-x)
    first_moment = x**n0*(F(n0)/(1-x)+x/(1-x)**2)
    tail = 2*complete_mass*(4*first_moment+11*geometric)
    require('exact_weighted_geometric_tail',
            tail == complete_mass*F(12*n0+39, 3**n0)
            == F(3737, 251048476872))
    require('tail_polynomial_domination_range', n0 >= 4)
    total = finite+tail
    require('entire_secondary_prime_series_below_1_85000', total < F(1, 85000))
    simple_final = old_simple-F(1, 85000)
    actual_final = old_exact-total
    require('positive_early_gate_before_continuation', F(1, 32000)-beta*total > 0)
    require('complete_two_level_positive_reserve',
            actual_final > old_simple-total > simple_final
            == F(134247, 34816000000) > F(1, 260000))
    result = dict(schema='two-level-triangle-attachment-v1',
                  sources={'staged_two_parent_attachment.json':
                           dict(sha256=sha256(raw).hexdigest(),
                                producer_sha256=prior['producer_sha256'])},
                  scope=dict(head='Report598 ten-prime restrictions',
                             primary_entry_prime_minimum=37,
                             secondary_entry_condition='s > its primary entry q; no extra cutoff',
                             secondary_parent_pair='(p,q) or (r,q), where (p,r) is the primary head pair',
                             private_interiors='Pairwise disjoint ordinary block-tree interiors',
                             secondary_interface_levels=1,
                             number_of_branches='Arbitrary finite',
                             all_original_heights='Arbitrary finite, no common bound',
                             residues='Arbitrary, globally fixed, one per distinct numerical original',
                             excluded='Further recursive shared-pair interfaces; unrestricted Erdos7',
                             lean_verified=False),
                  constants=dict(reference_child_pair=pair, complete_reciprocal_mass=complete_mass,
                                 alpha=alpha, c=c, early_pair_density=early_density,
                                 early_loss_to_final_head_multiplier=beta,
                                 inherited_simple_head_reserve=old_simple,
                                 inherited_exact_head_reserve=old_exact),
                  parent_amplifications=parent_rows,
                  literal_prefix=dict(count=len(labels), last=labels[-1], values=labels),
                  finite_rows=rows, finite_fee=finite,
                  analytic_tail=dict(first_odd_child=boundary, rectangle_start=n0,
                                     interval='2n^2+3 <= s <= 2(n+1)^2+1',
                                     pointwise_fee='2 C 3^-n/(n^2+1)',
                                     amplification_bound='A_q <= q-1 < s',
                                     weighted_interval_bound='2 C (4n+11) 3^-n',
                                     infinite_bound=tail),
                  consequence=dict(total_secondary_fee=total, fee_strictly_below=F(1, 85000),
                                   extendible_head_lower=actual_final,
                                   simple_extendible_head_lower=simple_final,
                                   strictly_greater_than=F(1, 260000),
                                   full_density_lower='1/(260000 Q_off)'),
                  checks=checks,
                  producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(result), indent=2)+'\n')
    print(json.dumps(encode(dict(checks=len(checks), child_rows=len(rows),
                                total_secondary_fee=total,
                                simple_final_lower=simple_final,
                                strictly_greater_than=F(1, 260000)))))


if __name__ == '__main__':
    main()
