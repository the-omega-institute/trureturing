#!/usr/bin/env python3
"""Exact early/late blocker budgets for two-parent entries from prime37.

Retains all original heights through complete parent reciprocal tails.
The accompanying proof performs both restrictions on actual measures.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from heapq import heappop, heappush
import json
from math import isqrt, prod
from pathlib import Path


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(item) for item in value]
    return value


def prefix(pair, count):
    pending, seen, result = [1], {1}, []
    while len(result) < count:
        d = heappop(pending)
        for p in pair:
            if d * p not in seen:
                seen.add(d * p)
                heappush(pending, d * p)
        if d > 1:
            result.append(d)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    base = Path(__file__).parent
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    checks = {}

    def require(name, predicate):
        if not predicate:
            raise ArithmeticError(name)
        checks[name] = True

    sources = {}

    def load(name):
        path = base / name
        raw = path.read_bytes()
        data = json.loads(raw)
        require(name + '_checks_true', bool(data['checks'])
                and all(v is True for v in data['checks'].values()))
        require(name + '_producer_fingerprint',
                sha256(path.with_suffix('.py').read_bytes()).hexdigest()
                == data['producer_sha256'])
        sources[name] = dict(sha256=sha256(raw).hexdigest(),
                             producer_sha256=data['producer_sha256'])
        return data

    head = load('central_high_support_augmentation.json')
    prior = load('two_parent_entry_attachment.json')
    c = F(head['constants']['continuation_c'])
    density = F(head['constants']['source_density_D'])
    multiplier = F(head['constants']['continuation_density_multiplier'])
    gate = F(head['consequence']['new_gate'])
    require('inherited_complete_moment_gate',
            c == F(1084133, 201247200)
            and density == F(3458, 405) and multiplier == F(200, 33)
            and gate == F(26345885990886052732242307711,
                          9055182074115772514304000000000))
    alpha = 1 / (density * multiplier)
    require('same_head_density', alpha * gate == F(head['consequence']['haar_lower'])
            == F(prior['consequence']['head_density_lower']))
    coordinate_density = [F(2)] + [F(p, p-2) for p in (5, 7, 11, 13, 17, 19)]
    pair_density = max(coordinate_density[i] * coordinate_density[j]
                       for i in range(7) for j in range(i+1, 7))
    require('early_pair_density_10_over_3', pair_density == F(10, 3)
            and prod(coordinate_density) == density)

    n0, boundary = 22, 971
    require('rectangle_tail_boundary', 2*n0*n0+3 == boundary)
    primes = [q for q in range(37, boundary)
              if all(q % d for d in range(2, isqrt(q)+1))]
    sieve = [True] * boundary
    sieve[0] = sieve[1] = False
    for d in range(2, isqrt(boundary-1)+1):
        if sieve[d]:
            for multiple in range(d*d, boundary, d):
                sieve[multiple] = False
    require('complete_152_prime_rows', len(primes) == 152
            and primes == [q for q in range(37, boundary) if sieve[q]])
    prior_rows = {row['entry_prime']: row for row in prior['finite_rows']}
    tables = {}
    for pair, target in [((3, 5), F(1, 2600)), ((3, 23), F(1, 125000))]:
        tag = f'{pair[0]}_{pair[1]}'
        labels = prefix(pair, boundary)
        grid = []
        first = 1
        while first <= labels[-1]:
            value = first
            while value <= labels[-1]:
                if value > 1:
                    grid.append(value)
                value *= pair[1]
            first *= pair[0]
        require(tag + '_literal_prefix_complete', sorted(grid) == labels
                and len(set(labels)) == len(labels))
        complete_mass = prod(F(p, p-1) for p in pair)
        tails = [complete_mass - 1]
        for d in labels:
            tails.append(tails[-1] - F(1, d))
        require(tag + '_complete_tail_positive', min(tails) > 0)
        rows = []
        for q in primes:
            fee, count = min((tails[n] / (q-3-n), n) for n in range(q-3))
            require(f'{tag}_original_parent_tail_{q}', 0 <= count < q-3
                    and fee > 0
                    and tails[count] == complete_mass-1
                    - sum((F(1, d) for d in labels[:count]), F()))
            if pair == (3, 5) and q in prior_rows:
                old = prior_rows[q]
                require(f'unchanged_600_fee_{q}',
                        fee == F(old['blocker_fee_upper'])
                        and count == old['shallow_parent_label_count'])
            rows.append(dict(entry_prime=q, selected_label_count=count,
                             reciprocal_tail=tails[count], blocker_fee_upper=fee))
        finite = sum((row['blocker_fee_upper'] for row in rows), F())
        tail = 9 * complete_mass / (n0 * 3**n0)
        total = finite + tail
        require(tag + '_infinite_fee_target', total < target)
        if pair == (3, 5):
            require('unchanged_600_analytic_tail',
                    tail == F(prior['analytic_tail']['bound']) == F(5, 204558018192))
        else:
            require('late_pair_analytic_tail', tail == F(23, 1125069100056))
        tables[tag] = dict(reference_parents=pair, finite_rows=rows,
                          prefix_count=len(labels), prefix_last=labels[-1],
                          finite_fee=finite, analytic_tail=tail, total_fee=total,
                          strictly_less_than=target)

    early_loss = pair_density * tables['3_5']['total_fee']
    new_gate = gate - (1-c)*early_loss
    head_lower = alpha * new_gate
    simple_loss = F(1, 780)
    simple_head = alpha * (gate - (1-c)*simple_loss)
    require('early_loss_below_1_780', early_loss < simple_loss)
    require('positive_early_gate_and_head', new_gate > 0
            and head_lower > simple_head > F(1, 32000))
    ordinary_fee = F(prior['consequence']['ordinary_attachment_fee'])
    require('unchanged_ordinary_branch_fee', ordinary_fee == F(1, 2**17))
    final = head_lower - ordinary_fee - tables['3_23']['total_fee']
    simple_final = F(1, 32000)-F(1, 125000)-ordinary_fee
    require('simple_joint_reserve', simple_final == F(31991, 2048000000)
            and final > simple_final > F(1, 65000))

    result = dict(schema='staged-two-parent-attachment-v1', sources=sources,
                  scope=dict(minimum_entry_prime=37,
                             head='Report598 ten-prime head restriction',
                             parents='Any two distinct head coordinates',
                             branches='Report600 disjoint private branches; Report599 private blocks',
                             all_original_heights='Unbounded finite',
                             residue_choice='One globally fixed phase per numerical original',
                             transport='Only head digit coordinates change; outside coordinates fixed',
                             excluded='General recursive two-parent separators; unrestricted Erdos7',
                             lean_verified=False),
                  constants=dict(c=c, inherited_gate=gate, density_D=density,
                                 continuation_multiplier=multiplier, alpha=alpha,
                                 early_pair_density=pair_density),
                  fee_tables=tables,
                  analytic_tail=dict(first_odd_entry=boundary, rectangle_start=n0,
                                     formula='9 C / (n0 3^n0), C=a/(a-1)b/(b-1)'),
                  consequence=dict(early_deletion_upper=early_loss,
                                   early_gate_lower=new_gate,
                                   head_after_continuation_lower=head_lower,
                                   simple_head_lower=simple_head,
                                   ordinary_attachment_fee=ordinary_fee,
                                   extendible_head_lower=final,
                                   simple_extendible_head_lower=simple_final,
                                   strictly_greater_than=F(1, 65000),
                                   full_density_lower='1/(65000 Q_outside)'),
                  checks=checks, producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(result), indent=2)+'\n')
    print(json.dumps(encode(dict(checks=len(checks),
                                early_fee=tables['3_5']['total_fee'],
                                late_fee=tables['3_23']['total_fee'],
                                head_lower=head_lower,
                                final_lower=final,
                                simple_final_lower=simple_final,
                                strictly_greater_than=F(1, 65000)))))


if __name__ == '__main__':
    main()
