"""Complete-period control for a prime-normalized all-private scalar noncover.

Standard library only. Numerical moduli repeat; there are no identical APs.
"""
import argparse
from itertools import product
from math import isqrt, prod
from collections import Counter
from pathlib import Path
import json

PATTERNS = ('**001', '**010', '*0*10', '*0101', '0*1*0', '000*1', '001**',
            '01*0*', '010**', '01111', '10*00', '100**', '10111', '11000',
            '11011', '11100', '11101', '11110', '11111')
DEFAULT_PRIMES = (3, 5, 7, 11, 13)

def need(test, message):
    if not test:
        raise ValueError(message)

def evaluate(primes):
    need(len(primes) == 5 and len(set(primes)) == 5, 'need five distinct primes')
    need(all(type(p) is int and p > 2 and p % 2 == 1
             and all(p % d for d in range(2, isqrt(p) + 1)) for p in primes),
         'prime support must contain five odd primes')
    words = list(product((0, 1), repeat=5))
    match = lambda w, b: all(t == '*' or int(t) == x for t, x in zip(w, b))
    bcounts = {b: sum(match(w, b) for w in PATTERNS) for b in words}
    need([b for b, c in bcounts.items() if c == 0] == [(0,) * 5], 'Boolean holes')
    need(all(sum(b) >= 2 for b, c in bcounts.items() if c == 1), 'private boundary')
    need(all(sum(bcounts[b] == 1 and match(w, b) for b in words) == 1
             for w in PATTERNS), 'pattern private witnesses')
    weight_one_counts = [bcounts[tuple(int(i == j) for i in range(5))] for j in range(5)]
    need(all(c == 2 for c in weight_one_counts), 'weight-one multiplicity must be two')

    classes = [(p, 0, 'prime') for p in primes]
    for w in PATTERNS:
        fixed = [i for i, t in enumerate(w) if t != '*']
        m = prod(primes[i] for i in fixed)
        choices = [(1,) if w[i] == '0' else range(2, primes[i]) for i in fixed]
        for rs in product(*choices):
            a = sum(r * (m // primes[i]) * pow(m // primes[i], -1, primes[i])
                    for i, r in zip(fixed, rs)) % m
            classes.append((m, a, w))
    need(len({(m, a) for m, a, _ in classes}) == len(classes), 'duplicate AP')
    Q = prod(primes)
    counts = [0] * Q
    last_owner = [-1] * Q
    for i, (m, a, _) in enumerate(classes):
        need(m > 1 and m % 2 == 1 and Q % m == 0, 'bad odd modulus')
        for x in range(a, Q, m):
            counts[x] += 1
            last_owner[x] = i
    holes = [x for x in range(Q) if counts[x] == 0]
    need(holes == [1], 'actual hole set')
    private = [x for x in range(Q) if counts[x] == 1]
    owner_private = Counter(last_owner[x] for x in private)
    need(len(owner_private) == len(classes), 'not irredundant')

    # Check the exact pointwise Boolean identity at all nonzero-coordinate points.
    nonzero_checks = 0
    for x in range(Q):
        if all(x % p for p in primes):
            b = tuple(int(x % p != 1) for p in primes)
            need(counts[x] == bcounts[b], 'wrong all-nonzero multiplicity')
            nonzero_checks += 1

    all_private_rows = 0
    zero_demand_rows = 0
    by_prime = []
    for p in primes:
        B = Q // p
        line_sums = [sum(counts[r + k * B] for k in range(p)) for r in range(B)]
        line_holes = [any(counts[r + k * B] == 0 for k in range(p)) for r in range(B)]
        row_count = 0
        min_slack = None
        missed_incidence = []
        for x in private:
            m, _, _ = classes[last_owner[x]]
            if m % p:
                # The unique p-free owner contributes p to its complete line.
                need(line_sums[x % B] - p >= 0, 'failed zero-demand row')
                zero_demand_rows += 1
                continue
            # In this squarefree period this is exactly the full directional LS row:
            # each compatible nonowner label contributes one to the line sum.
            service = line_sums[x % B] - 1
            slack = service - (p - 1)
            need(slack >= 0, 'failed actual private directional inequality')
            min_slack = slack if min_slack is None else min(min_slack, slack)
            row_count += 1
            if line_holes[x % B]:
                missed_incidence.append({'point': x, 'owner_modulus': m, 'service': service})
        need(len(missed_incidence) == 1 and missed_incidence[0]['owner_modulus'] == p,
             'unexpected private-to-hole boundary')
        need(missed_incidence[0]['service'] == 2 * (p - 2),
             'wrong service on private-to-hole line')
        all_private_rows += row_count
        by_prime.append({'prime': p, 'positive_demand_private_rows': row_count,
                         'minimum_slack': min_slack, 'PS1_failures': missed_incidence})

    out = {
        'result': 'PASS', 'period': Q, 'primes': list(primes),
        'class_count': len(classes), 'distinct_modulus_count': len({m for m, _, _ in classes}),
        'modulus_multiplicities': dict(sorted(Counter(m for m, _, _ in classes).items())),
        'private_point_count': len(private), 'overlap_point_count': sum(c >= 2 for c in counts),
        'holes': holes, 'all_classes_have_private_points': True,
        'all_nonzero_boolean_identity_checks': nonzero_checks,
        'positive_demand_private_rows_checked': all_private_rows,
        'zero_demand_private_rows_checked': zero_demand_rows,
        'all_private_prime_rows_checked': all_private_rows + zero_demand_rows,
        'Boolean_weight_one_multiplicities': weight_one_counts, 'by_prime': by_prime,
        'scope': 'Every actual private point and every support-prime row, including zero-demand rows, checked on the complete period. Moduli are squarefree, so all divisor-cut rows are either these rows or zero-demand rows. All moduli odd and nonunit, prime classes normalized, no identical APs, but numerical moduli repeat. This is not a distinct-odd counterexample or a Lean proof.'
    }
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--primes', nargs=5, type=int, default=DEFAULT_PRIMES,
                        metavar='P', help='five distinct odd primes')
    args = parser.parse_args()
    result = evaluate(tuple(args.primes))
    Path(args.output).write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({key: result[key] for key in
                      ('result', 'period', 'class_count', 'private_point_count',
                       'all_private_prime_rows_checked')}, sort_keys=True))


if __name__ == '__main__':
    main()
