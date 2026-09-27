#!/usr/bin/env python3
"""Use one retained exact two-depth block table in a complete mixed-loss budget.

Numerical label ranks use an infinite monotone frontier. No original phases
are searched and no original constraints or deep tail are discarded.
"""
from fractions import Fraction as F
from itertools import combinations
from math import prod
from pathlib import Path
import argparse
import hashlib
import heapq
import json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dp', type=Path, default=Path(__file__).with_name('two_depth_subset_dp.json'))
    parser.add_argument('--tail', type=Path, default=Path(__file__).with_name('phase_resampling_arithmetic.json'))
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    raw_dp = args.dp.read_bytes()
    dp_pin = 'd0a9f89564428214cd05630f2a2de40379a45369a68f64fe9e64782bc67f7d17'
    if hashlib.sha256(raw_dp).hexdigest() != dp_pin:
        raise ValueError('DP source pin mismatch')
    raw_tail = args.tail.read_bytes()
    tail_pin = 'da1e922b5745ede67d601c3780043f6d97aa8ee1bf64944479c58b2113f9d10f'
    if hashlib.sha256(raw_tail).hexdigest() != tail_pin:
        raise ValueError('tail source pin mismatch')
    dp, tail_data = json.loads(raw_dp), json.loads(raw_tail)
    checks = {}

    def require(name, condition):
        checks[name] = bool(condition)
        if not condition:
            raise ValueError(name)

    P = (3, 5, 7, 11, 13, 17, 19)
    Q = P[1:]
    M = 1 << len(Q)
    require('DP_completed', dp['complete'] is True)
    require('DP_all_checks_passed', len(dp['checks']) == dp['passed_count']
            and all(dp['checks'].values()))
    require('DP_prime_order', tuple(dp['prime_order']) == Q)
    D = dp['common_denominator']
    require('DP_integer_denominator', D == prod(p*(p-2) for p in Q))
    require('tail_cutoff', tail_data['cutoff'] == 10**9)
    require('tail_alpha', F(tail_data['alpha']) == F(7235955529, 6075000000000))
    cases = dp['cases']
    for name, case in cases.items():
        table = case['minimum_integer_matrix']
        N = case['allowed_cell_count']
        require(name+'_matrix_shape', len(table) == M and all(len(row) == M for row in table))
        require(name+'_positive_cell_count', N in (5, 6, 8, 9))
        require(name+'_empty_block', table[0][0] == D*(2*N-1))
    bounds = [[max(1-F(case['minimum_integer_matrix'][a][b],
                       D*(2*case['allowed_cell_count']-1))
                   for case in cases.values()) for b in range(M)] for a in range(M)]
    require('all_block_bounds_probabilities',
            all(0 <= x <= 1 for row in bounds for x in row))

    def cap(d):
        return F(1, d)*prod(F(p-1, p-2) for p in P if d % p == 0)

    block_labels = {factor*p for factor in (3, 9) for p in Q}
    heap, seen = [], set()

    def add(d):
        if d not in seen:
            seen.add(d)
            heapq.heappush(heap, (-cap(d), d))

    for p, q in combinations(P, 2):
        add(p*q)
    rank, popped = [], []
    max_n = 40
    while len(rank) < max_n:
        priority, d = heapq.heappop(heap)
        popped.append((d, -priority))
        if d not in block_labels:
            rank.append((d, -priority))
        for p in P:
            add(d*p)
    require('frontier_global_order', all(a[1] >= b[1] for a, b in zip(popped, popped[1:])))
    require('all_block_labels_expanded', block_labels.issubset({d for d, _ in popped}))
    require('remaining_frontier_dominated', all(-k <= rank[-1][1] for k, _ in heap))
    require('frontier_pop_bound', len(popped) <= max_n+12)
    require('remaining_distinct_nonblock_labels',
            len({d for d, _ in rank}) == max_n and all(d not in block_labels for d, _ in rank))
    cumulative = [F(0)]
    for _, value in rank:
        cumulative.append(cumulative[-1]+value)
    deep = F(4096, 935)*F(tail_data['tail'])
    threshold = F(173, 250)
    records = []
    for n in range(max_n+1):
        worst, worst_a, worst_b = F(-1), None, None
        for a in range(M):
            for b in range(M):
                slots = a.bit_count()+b.bit_count()
                if slots > n:
                    continue
                value = bounds[a][b]+cumulative[n-slots]+deep
                if value > worst:
                    worst, worst_a, worst_b = value, a, b
        records.append({'max_shallow_mixed_labels': n, 'loss_upper': str(worst),
                        'parent_mask': worst_a, 'child_mask': worst_b,
                        'below_loss_threshold': worst < threshold})
    require('envelopes_increase', all(F(x['loss_upper']) <= F(y['loss_upper'])
                                    for x, y in zip(records, records[1:])))
    valid = [r for r in records if r['below_loss_threshold']]
    require('original_sixteen_count_retained', records[16]['below_loss_threshold'])
    require('both_threshold_sides_in_requested_range', 0 < len(valid) < len(records))
    last = valid[-1]
    result = {
        'scope': 'same actual pure source block-plus-tail bound, not a phasewise change of law',
        'dp_input_name': args.dp.name, 'dp_input_sha256': dp_pin,
        'tail_input_name': args.tail.name, 'tail_input_sha256': tail_pin,
        'primes': list(P), 'cutoff': tail_data['cutoff'],
        'block_labels': sorted(block_labels), 'deep_capacity_upper': str(deep),
        'nonblock_rank': [{'label': d, 'cap': str(v)} for d, v in rank],
        'popped_labels': len(popped), 'remaining_frontier_count': len(heap),
        'maximum_tested_head_count': max_n, 'loss_threshold': str(threshold),
        'profiles_by_count': records, 'largest_certified_count': last['max_shallow_mixed_labels'],
        'last_certificate': last, 'next_count': records[last['max_shallow_mixed_labels']+1],
        'conclusion_boundary': 'failure of the sufficient envelope above the threshold '
                               'is not an actual-family lower witness or count optimality',
        'checks': checks, 'passed_count': len(checks),
    }
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'passed_count': len(checks), 'largest_certified_count': last['max_shallow_mixed_labels'],
                      'last_upper': last['loss_upper'], 'next_upper': result['next_count']['loss_upper'],
                      'output': str(args.output)}, indent=2))


if __name__ == '__main__':
    main()
