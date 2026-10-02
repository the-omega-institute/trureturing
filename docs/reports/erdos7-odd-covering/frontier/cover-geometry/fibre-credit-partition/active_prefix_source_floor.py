"""Exact finite controls for active-prefix source floors at ternary height two.

No optimizer and no project imports. All original labels and phases are explicit.
This checks a noncover; it does not certify extremality or settle Erdős #7.
"""
import argparse
from fractions import Fraction as F
from itertools import combinations, product
from math import gcd, lcm
from pathlib import Path
import json

FAMILY = ((3, 0), (5, 0), (9, 2), (15, 11), (25, 6), (45, 1), (75, 1))
PRIVATE = {3: 3, 5: 5, 9: 2, 15: 26, 25: 31, 45: 46, 75: 76}
CHECKS = 0

def need(condition, description):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise ValueError(description)

def frac(value):
    return str(F(value))

def valuation(n, p):
    ans = 0
    while n % p == 0:
        n //= p
        ans += 1
    return ans

def cylinder(depth, residue, q=5, height=2):
    return frozenset(x for x in range(q ** height) if x % (q ** depth) == residue)

def pure_mass_floor(q, h, s, m):
    u = sum((F(1, q ** j) for j in range(1, h + 1)), F(0))
    tail = sum((F(1, q ** j) for j in range(m + 1, h + 1)), F(0))
    return (s - tail) / (1 - u)

period = lcm(*(m for m, _ in FAMILY))
labels = {m for m, _ in FAMILY}
need(period == 225, 'Actual complete CRT period')
need(len(labels) == len(FAMILY), 'Numerical labels distinct')
need(all(m > 1 and m % 2 == 1 for m in labels), 'All moduli odd nonunits')
for m in labels:
    for d in range(2, m + 1):
        if m % d == 0:
            need(d in labels, 'Divisor closure')
for m, a in FAMILY:
    x = PRIVATE[m]
    hits = [d for d, b in FAMILY if x % d == b]
    need(hits == [m], 'Explicit private witness for each original')
for (m, a), (n, b) in combinations(FAMILY, 2):
    if m % n == 0 or n % m == 0:
        need((a - b) % gcd(m, n) != 0, 'Comparable originals disjoint by CRT')
uncovered = [x for x in range(period) if all(x % m != a for m, a in FAMILY)]
need(bool(uncovered), 'Actual family is a noncover')
q_survivors = frozenset(x for x in range(25) if x % 5 != 0 and x != 6)
t_survivors = tuple(x for x in range(9) if x % 3 != 0 and x != 2)
need(len(q_survivors) == 19, 'Same pure-conditioned q source')
need(t_survivors == (1, 4, 5, 7, 8), 'Actual ternary source leaves')
stars = []
for m, a in FAMILY:
    i, j = valuation(m, 3), valuation(m, 5)
    if i and j:
        need(m == 3 ** i * 5 ** j, 'Star retains complete original label')
        stars.append({'modulus': m, 'residue': a, 'i': i, 'j': j,
                      'ternary_residue': a % (3 ** i), 'q_residue': a % (5 ** j)})

rows = []
for t in t_survivors:
    active = [s for s in stars if t % (3 ** s['i']) == s['ternary_residue']]
    prefixes = [(s, cylinder(s['j'], s['q_residue'])) for s in active]
    union = frozenset().union(*(c for _, c in prefixes))
    maximal = [(s, c) for s, c in prefixes if not any(c < d for _, d in prefixes)]
    for (_, c), (_, d) in combinations(maximal, 2):
        need(c.isdisjoint(d), 'Maximal active q-prefix cylinders form an antichain')
    need(frozenset().union(*(c for _, c in maximal)) == union, 'Antichain retains actual union')
    s_mass = sum((F(len(c), 25) for _, c in maximal), F(0))
    beta = F(len(union & q_survivors), len(q_survivors))
    mdepth = min(s['j'] for s, _ in maximal)
    floors = sum((pure_mass_floor(5, 2, F(1, 5 ** s['j']), s['j']) for s in active), F(0))
    cap = sum((F(25, 19 * 5 ** s['j']) for s in active), F(0))
    removed = sum((F(1, 5 ** j) for j, a in ((1, 0), (2, 6))
                   if cylinder(j, a).issubset(union)), F(0))
    exact_from_prefixes = F(25, 19) * (s_mass - removed)
    need(beta == exact_from_prefixes, 'Exact pure-overlap prefix formula')
    floor = pure_mass_floor(5, 2, s_mass, mdepth)
    need(beta >= floor, 'Antichain floor with actual q height')
    for h_upper in range(2, 9):
        need(beta >= pure_mass_floor(5, h_upper, s_mass, mdepth), 'Height-upper-bound floor')
    need(beta <= cap, 'Complete active-label upper cap')
    rows.append({'t_mod_9': t, 'active_labels': [s['modulus'] for s in active],
                 'maximal_prefix_labels': [s['modulus'] for s, _ in maximal],
                 'antichain_haar_mass': frac(s_mass), 'beta': frac(beta),
                 'antichain_floor': frac(floor), 'sum_individual_floors': frac(floors),
                 'sum_label_upper_caps': frac(cap)})
need([r['beta'] for r in rows] == ['4/19', '1/19', '4/19', '1/19', '4/19'], 'Exact full beta table')
need(rows[0]['sum_individual_floors'] == '5/19', 'Actual nested-prefix failure')
mean_beta = sum((F(r['beta']) for r in rows), F(0)) / 5
mean_individual_floor = sum((F(r['sum_individual_floors']) for r in rows), F(0)) / 5
mean_upper_cap = sum((F(r['sum_label_upper_caps']) for r in rows), F(0)) / 5
need((mean_beta, mean_individual_floor, mean_upper_cap) == (F(14, 95), F(15, 95), F(18, 95)), 'One-law integrated values')
need(F(len(uncovered), period) == F(19, 25) * F(5, 9) * (1 - mean_beta), 'Actual survivor Haar factorization')

# Independent law: uniform first q roots 2,3,4, with uniform tails.
nu = {x: (F(1, 15) if x % 5 in (2, 3, 4) else F(0)) for x in range(25)}
need(sum(nu.values(), F(0)) == 1, 'Nu is one probability')
need(all(nu[x] == 0 for x in range(25) if x not in q_survivors), 'Nu supported on actual R3')
for depth in (1, 2):
    for a in range(5 ** depth):
        mass = sum((nu[x] for x in range(25) if x % (5 ** depth) == a), F(0))
        need(mass <= F(1, 3 ** depth), 'PC7 one-link prefix cap')
for s in stars:
    c = cylinder(s['j'], s['q_residue'])
    need(bool(c & q_survivors), 'Star has nonempty actual R3 trace')
    need(sum((nu[x] for x in c), F(0)) == 0, 'Admissible capped law gives zero star mass')
# All complete 3-ary subtrees through the actual height 2 meet actual R3.
subsets = tuple(combinations(range(5), 3))
trees = 0
for roots in subsets:
    for branch_choices in product(subsets, repeat=3):
        leaves = frozenset(r + 5 * child for r, children in zip(roots, branch_choices) for child in children)
        need(len(leaves) == 9 and bool(leaves & q_survivors), 'Complete 3-ary height-two tree obstruction')
        trees += 1
need(trees == 10000, 'All complete 3-ary height-two trees enumerated')

result = {
    'contract': 'actual finite noncover, ordinary mathematical control, no Lean or extremality claim',
    'family': [{'modulus': m, 'residue': a, 'private_witness': PRIVATE[m]} for m, a in FAMILY],
    'period': period, 'uncovered_count': len(uncovered), 'haar_survivor_mass': frac(F(len(uncovered), period)),
    'source_q_survivors_mod_25': sorted(q_survivors), 'source_ternary_leaves_mod_9': list(t_survivors),
    'beta_rows': rows,
    'integrals_same_lambda3': {'actual_beta': frac(mean_beta), 'invalid_sum_individual_floors': frac(mean_individual_floor), 'valid_sum_label_upper_caps': frac(mean_upper_cap)},
    'capped_residual_law': {'positive_first_roots': [2, 3, 4], 'first_root_mass': '1/3', 'depth_two_atom_mass': '1/15', 'all_star_trace_masses': '0', 'complete_tree_count': trees},
    'checks': CHECKS,
}
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
if args.output is None:
    print(rendered, end='')
else:
    args.output.write_text(rendered, encoding='utf-8')
