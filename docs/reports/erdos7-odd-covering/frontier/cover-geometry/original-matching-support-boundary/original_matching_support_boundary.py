#!/usr/bin/env python3
"""Actual divisor-closed local matching versus prime-support collision controls."""
from collections import Counter
from fractions import Fraction as F
from math import lcm, gcd
from pathlib import Path
import argparse
import json

def need(ok, message):
    if not ok:
        raise ValueError(message)

def support(n):
    ans = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            ans.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        ans.append(n)
    return tuple(ans)

def build(p, q):
    classes = [(p, 0)]
    classes += [(q ** j, q ** (j - 1)) for j in range(1, p)]
    classes += [(p * q ** j, q ** j * ((j * pow(q ** j, -1, p)) % p)) for j in range(1, p)]
    L = lcm(*(m for m, a in classes))
    moduli = {m for m, a in classes}
    need(len(moduli) == len(classes) and all(m > 1 and m % 2 for m in moduli), 'literal odd distinct moduli')
    need(all(m % d or d in moduli for m in moduli for d in range(2, m + 1)), 'divisor closure above one')
    hits = [[s for s, (m, a) in enumerate(classes) if x % m == a] for x in range(L)]
    need(all(any(row == [s] for row in hits) for s in range(len(classes))), 'every original has a private point')
    order = sorted(range(len(classes)), key=lambda s: classes[s][0])
    priority = {s: i for i, s in enumerate(order)}
    owner = [min(row, key=priority.get) if row else -1 for row in hits]
    comparable = 0
    for s, (m, a) in enumerate(classes):
        for t, (n, b) in enumerate(classes):
            if s < t and (m % n == 0 or n % m == 0):
                need((a - b) % gcd(m, n) != 0, 'actual comparable classes disjoint')
                comparable += 1
    fibre = [x for x in range(L) if x % (q ** (p - 1)) == 0]
    need(len(fibre) == p and all(len(hits[x]) == 1 for x in fibre), 'complete actual p-fibre at cofactor zero')
    suppliers = []
    for a in range(1, p):
        x = next(x for x in fibre if x % p == a)
        s = hits[x][0]
        m, residue = classes[s]
        need(m == p * q ** a, 'original matching cofactor identity')
        suppliers.append(s)
    need(len({classes[s][0] // p for s in suppliers}) == p - 1, 'full synchronized matching in distinct original cofactors')
    bins = Counter(support(classes[s][0]) for s in suppliers)
    need(len(bins) == 1 and next(iter(bins.values())) == p - 1, 'all suppliers have same ordinary prime support')
    phi = sum(k * (k - 1) // 2 for k in bins.values())
    need(phi == (p - 1) * (p - 2) // 2, 'maximal first-digit support assignment cost')
    private_p = {x for x, row in enumerate(hits) if row == [0]}
    cofactor_period = q ** (p - 1)
    Rp = {b for b in range(cofactor_period) if all(b % m != a for m, a in classes if m % p)}
    Vp = {x for x in range(L) if x % cofactor_period in Rp}
    need(len(Vp) == p * len(private_p), 'actual prime-private product identity')
    # In this family p occurs at height one, so changing it is both a first-digit
    # change and the entire original p-coordinate change.
    pure_owned = {x for x in Vp if owner[x] >= 0 and support(classes[owner[x]][0]) == (p,)}
    lines = Counter(x % cofactor_period for x in pure_owned)
    need(set(lines) == Rp and all(h >= 1 for h in lines.values()), 'prime-private root gives a pure owner on each line')
    delta = F((p - 2) * sum(h * (p - h) for h in lines.values()), 2 * L)
    pure_mass_bound = F(1, p)
    bound = F(p - 2, 2) * F(len(Vp), L) * (1 - pure_mass_bound)
    need(delta == bound, 'pure-owner positive defect bound is exact at original p-height one')
    need(any(not row for row in hits), 'explicitly a noncover')
    return dict(p=p, q=q, period=L, classes=[dict(modulus=m, residue=a) for m,a in classes],
        private_witnesses=[next(x for x, row in enumerate(hits) if row == [s]) for s in range(len(classes))],
        comparable_pairs=comparable, holes=sum(not row for row in hits),
        source_cofactor=0, complete_p_fibre=fibre, original_cofactor_matching_rank=p-1,
        ordinary_support_assignment_cost=phi, maximal_possible_assignment_cost=phi,
        prime_private_mass=str(F(len(private_p), L)), full_private_cofactor_cylinder_mass=str(F(len(Vp), L)),
        pure_owner_defect=str(delta), pure_owner_defect_lower_bound=str(bound),
        boundary='Full p-fibre coverage and synchronized matching hold at the specified cofactor, not throughout the actual R_p.')

cases = [build(3, 5), build(5, 3), build(7, 3)]
pure_classes = [(3,0),(9,1),(27,2)]
pure_points = {x for x in range(27) if any(x % m == a for m,a in pure_classes)}
first_digit_lines = Counter(x // 3 for x in pure_points)
need(len(first_digit_lines) == 9 and min(first_digit_lines.values()) >= 1, 'complete high tail retained in first-digit lines')
pure_delta = F(sum(h * (3-h) for h in first_digit_lines.values()), 54)
pure_bound = F(1,2) * (1-sum((F(1,m) for m,a in pure_classes), F(0)))
need(pure_delta == F(8,27) > pure_bound == F(7,27), 'higher pure-height defect retains sufficient-bound direction')
duplicate_classes = [(3,0),(3,1),(3,2)]
duplicate_owners = [[s for s,(m,a) in enumerate(duplicate_classes) if x % m == a] for x in range(3)]
need(all(len(row) == 1 for row in duplicate_owners), 'repeated pure modulus partition remains irredundant')
duplicate_delta = F(3 * (3-3), 6)
duplicate_actual_T = sum((F(1,m) for m,a in duplicate_classes), F(0))
duplicate_collapsed_T = sum((F(1,m) for m in {m for m,a in duplicate_classes}), F(0))
need(duplicate_delta == 0 and duplicate_actual_T == 1 and duplicate_collapsed_T == F(1,3), 'pure-modulus uniqueness is material to strict positivity')
out = dict(scope='Ordinary exact controls, not Lean. General construction is odd, distinct, divisor closed and irredundant; it is an explicit noncover.', cases=cases,
    higher_pure_control=dict(classes=pure_classes,period=27,first_digit_line_occupancies=dict(Counter(first_digit_lines.values())),
        exact_defect=str(pure_delta),lower_bound=str(pure_bound)),
    repeated_pure_boundary=dict(classes=duplicate_classes,period=3,designated_prime_private_mass='1/3',
        exact_defect=str(duplicate_delta),multiplicity_counted_T=str(duplicate_actual_T),
        invalid_collapsed_T=str(duplicate_collapsed_T),invalid_collapsed_positive_bound='1/3',
        scope='Repeated numerical modulus; this rejects omitting the explicit pure-modulus uniqueness premise.'))
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
options = parser.parse_args()
options.output.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps([{k:v for k,v in c.items() if k not in ('classes','private_witnesses','complete_p_fibre')} for c in cases], indent=2))
