#!/usr/bin/env python3
"""Exact uniform costs for increasing two-parent networks.

Selected complete parent towers followed by normalized capped kernels give
one sequential law with coordinate density at most six. This checks the
finite LCM-tail moments and complete prime-tail reserve; the accompanying
ordinary proof supplies original-source and whole-network quantifiers.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from heapq import heappop, heappush
import json
from math import isqrt
from pathlib import Path


def encode(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, dict):
        return {str(k): encode(v) for k, v in x.items()}
    if isinstance(x, (tuple, list)):
        return [encode(v) for v in x]
    return x


def prefix(p, count):
    pending, seen, out = [(1, 0, 0)], {(0, 0)}, []
    while len(out) < count:
        d, i, j = heappop(pending)
        out.append((d, i, j))
        for ii, jj in ((i+1, j), (i, j+1)):
            if (ii, jj) not in seen:
                seen.add((ii, jj))
                heappush(pending, (3**ii*p**jj, ii, jj))
    return out


def moment_table(p, cap, count, require):
    labels = prefix(p, count)
    grid = []
    first, i = 1, 0
    while first <= labels[-1][0]:
        d, j = first, 0
        while d <= labels[-1][0]:
            grid.append((d, i, j))
            d *= p
            j += 1
        first *= 3
        i += 1
    tag = f'3_{p}_cap{cap}'
    require(tag+'_literal_prefix_grid', sorted(grid) == labels)

    def kernel(x, y):
        i, j = max(x[1], y[1]), max(x[2], y[2])
        return (cap if j else F(1))/(3**i*p**j)

    def row(x):
        d, i, j = x
        first = F(i+1, 3**i)+F(1, 2*3**i)
        second = 1+cap/F(p-1) if j == 0 else cap*(F(j+1, p**j)+F(1, p**j*(p-1)))
        return first*second

    total = 3*(1+cap*(F(3, p-1)+F(2, (p-1)**2)))
    m, row_sum, square_sum = total, F(), F()
    values = []
    for n, x in enumerate(labels):
        cross = sum((kernel(x, y) for y in labels[:n]), F())
        diagonal = kernel(x, x)
        m -= 2*(row(x)-cross)-diagonal
        row_sum += row(x)
        square_sum += 2*cross+diagonal
        require(f'{tag}_tail_{n}', m > 0 and m == total-2*row_sum+square_sum
                and (not values or m <= values[-1]))
        values.append(m)
    return labels, values, total


def optimum(q, moments):
    candidates = []
    for n in range(q-3):
        d = q-3-n
        if 6*d <= q-1:
            break
        delta = min(F(1, 2), 1-F(q-1, 6*d))
        fee = moments[n]/(4*delta*(1-delta)*d*d)
        candidates.append((fee, n, delta))
    return min(candidates)


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

    path = args.source_dir/'staged_two_parent_attachment.json'
    raw = path.read_bytes()
    old = json.loads(raw)
    require('source_checks_true', bool(old['checks']) and all(v is True for v in old['checks'].values()))
    require('source_producer_fingerprint', old['producer_sha256'] == sha256(path.with_suffix('.py').read_bytes()).hexdigest())
    old_simple = F(old['consequence']['simple_extendible_head_lower'])
    old_exact = F(old['consequence']['extendible_head_lower'])
    beta = F(old['constants']['alpha'])*(1-F(old['constants']['c']))*F(old['constants']['early_pair_density'])
    require('inherited_simple_reserve', old_exact > old_simple == F(31991, 2048000000))
    require('early_conversion', beta == F(46191477, 720966400) and 0 < beta < 1)
    require('deep_first_coordinate_domination', F(6, 41) < F(1, 3))

    boundary, n0 = 971, 22
    primes = [q for q in range(37, boundary) if all(q%d for d in range(2, isqrt(q)+1))]
    sieve = bytearray(b'\1')*boundary
    sieve[:2] = b'\0\0'
    for p in range(2, isqrt(boundary-1)+1):
        if sieve[p]:
            sieve[p*p:boundary:p] = b'\0'*((boundary-1-p*p)//p+1)
    require('prime_lists_agree', len(primes) == 152 and primes == [q for q in range(37, boundary) if sieve[q]])
    amps = {q: F() for q in primes}
    parent_rows = {}
    for tag in ('3_5', '3_23'):
        old_rows = old['fee_tables'][tag]['finite_rows']
        require(tag+'_complete_parent_rows', [r['entry_prime'] for r in old_rows] == primes)
        table = {}
        for row in old_rows:
            q, n = row['entry_prime'], row['selected_label_count']
            d = q-3-n
            a = F(q-1, d)
            require(f'{tag}_parent_{q}', d >= 1 and a <= q-1
                    and F(row['reciprocal_tail'])/d == F(row['blocker_fee_upper']))
            table[q] = a
            amps[q] = max(amps[q], a)
        parent_rows[tag] = table

    tables = {}
    for tag, p, cap in (('direct', 37, F(1)), ('deep', 41, F(6))):
        labels, moments, total = moment_table(p, cap, boundary, require)
        tables[tag] = dict(reference_pair=(3, p), second_coordinate_cap=cap,
                           all_label_pair_moment=total,
                           literal_prefix=labels, tail_moments=moments)

    rows = []
    for q in primes[1:]:
        earlier = [p for p in primes if p < q]
        first_amp = max(amps[p] for p in earlier)
        # A deep node has an actual intervening introduced prime between
        # its primary ancestor and itself. Its primary cannot be the
        # immediately preceding available prime.
        deep_amp = max((amps[p] for p in earlier[:-1]), default=F())
        mode_rows = {}
        for tag, amp in (('direct', first_amp), ('deep', deep_amp)):
            fee, n, delta = optimum(q, tables[tag]['tail_moments'])
            d = q-3-n
            cap = F(q-1, d)/(1-delta)
            require(f'{q}_{tag}_valid_normalized_kernel',
                    0 <= n < q-3 and 0 < delta <= F(1, 2) and cap <= 6)
            require(f'{q}_{tag}_finite_optimum',
                    all(fee <= tables[tag]['tail_moments'][nn]
                        /(4*min(F(1,2),1-F(q-1,6*(q-3-nn)))
                          *(1-min(F(1,2),1-F(q-1,6*(q-3-nn))))*(q-3-nn)**2)
                        for nn in range(q-3) if 6*(q-3-nn)>q-1))
            mode_rows[tag] = dict(selected_label_count=n, threshold=delta,
                                  haar_density_cap=cap, unselected_pair_moment=tables[tag]['tail_moments'][n],
                                  node_violation_fee=fee, primary_amplification=amp,
                                  weighted_fee=amp*fee)
        require(f'{q}_primary_ancestor_weight',
                first_amp < q and deep_amp < q and (q != 41 or deep_amp == 0))
        fee = max(mode_rows[t]['weighted_fee'] for t in ('direct', 'deep'))
        rows.append(dict(node_prime=q, modes=mode_rows, final_head_fee=fee))
    finite = sum((r['final_head_fee'] for r in rows), F())

    require('tail_interval_boundary', 2*n0*n0+3 == boundary and n0 >= 22)
    require('tail_row_constants', 3*(1+F(6)*(F(3,36)+F(2,36**2))) == F(163,36)
            and F(163,72)+F(37,2) == F(1495,72) < 21
            and F(163,36)+F(703,36) == F(433,18) < 25)
    # Analytic inequalities for every n>=22 are proved in the report:
    # weighted interval <= (5/n)*(21n+25)*3^-n <=115*3^-n.
    tail = F(345, 2*3**n0)
    require('entire_weighted_tail', tail == F(115,20920706406))
    total = finite+tail
    simple = old_simple-F(1,94500)
    exact = old_exact-total
    require('full_recursive_fee_below_1_94500', total < F(1,94500))
    require('positive_early_gate', F(1,32000)-beta*total > 0)
    require('complete_arbitrary_depth_reserve',
            exact > old_simple-total > simple == F(1950299,387072000000) > F(1,200000))
    result = dict(schema='recursive-pair-forward-kernels-v1',
                  sources={'staged_two_parent_attachment.json':
                           dict(sha256=sha256(raw).hexdigest(), producer_sha256=old['producer_sha256'])},
                  scope=dict(head='Report598 restrictions', primary_minimum=37,
                             primary_component='Two distinct head parents p,r and outside q>max(p,r); primary p^i r^j q^e towers and q ordinary domain',
                             generated_entries='Globally distinct v>q in increasing order; two fixed distinct parents from p,r,q and earlier generated nodes of this component; v exceeds both parents',
                             parent_restriction='At least one parent outside the head; later pair(p,r) forbidden; parents need not already be adjacent',
                             network='Arbitrary finite depth and width; cross-sibling parent choices and two generated parents allowed; unbounded co-occurrence treewidth',
                             ownership='Each actual triangle label belongs to its unique largest introduced prime, with positive owner exponent',
                             components='Different primary components share only head coordinates; outside entries and private interiors disjoint; no cross-component originals',
                             ordinary_interiors='Report599 private trees, disjoint away from declared roots; ordinary Type I and separate components unchanged',
                             modes='Direct iff both parents initial, hence (p,q) or (r,q); deep iff at least one parent generated, giving q<w<v',
                             blocker='One B_down on full (p,r,q), imposing only later network and its private ordinary trees; excludes head legality, q ordinary domain and primary triangle',
                             heights='Arbitrary finite, unbounded', residues='One arbitrary globally fixed residue per distinct original numerical modulus',
                             source='Actual full coordinates; one normalized sequential law for each whole later network from product Haar on p,r,q; one primary amplification',
                             excluded='Unrestricted Erdos7; unrestricted head labels; later two-head parent pairs; multiple parent pairs at one node; cross-primary originals; non-increasing network assignment', lean_verified=False),
                  constants=dict(uniform_conditional_haar_density=6, beta=beta,
                                 inherited_simple_reserve=old_simple, inherited_exact_reserve=old_exact),
                  parent_amplifications=parent_rows, moment_tables=tables, finite_rows=rows,
                  finite_fee=finite,
                  analytic_tail=dict(first_odd_node=boundary, rectangle_start=n0,
                                     selected_rectangle='0<=i,j<n, excluding unit', selected_count='n^2-1',
                                     threshold='1/2', conditional_haar_cap='at most4, hence at most6',
                                     moment_bound='(21n+25)3^-n', weighted_interval_bound='115*3^-n', bound=tail),
                  consequence=dict(total_additional_fee=total, strictly_below=F(1,94500),
                                   extendible_head_lower=exact, simple_extendible_head_lower=simple,
                                   strictly_greater_than=F(1,200000), full_density_lower='1/(200000 Q_off)'),
                  checks=checks, producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(result), indent=2)+'\n')
    print(json.dumps(encode(dict(checks=len(checks), node_rows=len(rows), finite_fee=finite,
                                total_additional_fee=total, simple_final=simple,
                                strictly_greater_than=F(1,200000)))))


if __name__ == '__main__':
    main()
