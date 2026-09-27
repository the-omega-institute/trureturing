#!/usr/bin/env python3
"""One actually empty central fibre after freeing within-edge endpoints.

Construct34 globally fixed, distinct odd congruence labels. Check the local
49x121 product and the complete1334025-period residue table. This is a local
source obstruction, not an odd covering-system counterexample. Standard
library exact arithmetic only; no Lean verification.
"""
import argparse
import hashlib
import json
from fractions import Fraction as F
from itertools import combinations
from math import gcd, lcm, prod
from pathlib import Path

CENTRAL = 106
CENTRAL_PERIOD = 225
CHECKS = []


def check(name, condition, count=1):
    if not condition:
        raise ArithmeticError(name)
    CHECKS.append(dict(name=name, count=count))


def crt(parts):
    parts = [(m, a % m) for m, a in parts if m > 1]
    check('pairwise_coprime_CRT_components', all(gcd(m, n) == 1 for (m, _), (n, _) in combinations(parts, 2)))
    modulus = prod(m for m, _ in parts)
    residue = sum(a*(modulus//m)*pow(modulus//m, -1, m) for m, a in parts) % modulus
    check('fixed_CRT_phase', all(residue % m == a for m, a in parts))
    return modulus, residue


def make_family():
    family = []

    def add(name, group, parts):
        modulus, residue = crt(parts)
        family.append(dict(name=name, group=group, modulus=modulus, residue=residue,
                           components=[dict(modulus=m, residue=a % m) for m, a in parts if m > 1]))

    for m, a in ((3,2), (9,1), (5,4), (25,1), (7,0), (49,43), (11,0)):
        add(f'pure_{m}', 'pure', [(m,a)])
    add('central_15', 'central_mask', [(15,0)])
    for q, outside in ((7,(2,3,4,5,6,1,8)), (11,(1,2,3,4,5,1,1))):
        for central, exponent, a in zip((3,5,15,9,25,3,5), (1,1,1,1,1,2,2), outside):
            add(f'star_{central}_{q}^{exponent}', f'star_{q}', [(central,CENTRAL), (q**exponent,a)])
    for j, central in enumerate((1,3,5,15)):
        add(f'edge_11_c{central}', 'edge_11', [(central,CENTRAL), (7,1), (11,6+j)])
        add(f'edge_21_c{central}', 'edge_21', [(central,CENTRAL), (49,15+7*j), (11,10)])
        add(f'edge_12_c{central}', 'edge_12_source_null', [(central,CENTRAL), (7,0), (121,0)])
    check('34_distinct_odd_numerical_labels', len(family) == len({x['modulus'] for x in family}) == 34 and
          all(x['modulus'] > 1 and x['modulus'] % 2 == 1 for x in family))
    return family


def hit(n, row):
    return n % row['modulus'] == row['residue']


def exact_uniform_box_obstruction():
    qs = (7,11,13,17,19)
    r = [F(1,q-1) for q in qs]
    a = [F(1,q*(q-2)) for q in qs]
    z = [1-5*x-2*y for x,y in zip(r,a)]
    edges = list(combinations(range(5), 2))
    beta = [r[q]*r[s]+a[q]*r[s]+r[q]*a[s] for q,s in edges]
    u = [b/(z[q]*z[s]) for b,(q,s) in zip(beta,edges)]
    clique_sum = sum((x for x,(q,s) in zip(u,edges) if q == 0), F())
    check('unconditional_q7_clique_exceeds_one', clique_sum > 1)
    values = []
    for mask in range(1024):
        es = [e for e in range(10) if mask >> e & 1]
        v = 1-sum((u[e] for e in es), F())
        v += sum((u[e]*u[f] for e,f in combinations(es,2) if set(edges[e]).isdisjoint(edges[f])), F())
        values.append(v)
    return dict(primes=qs, zmin=list(map(str,z)),
                beta_unconditional=list(map(str,beta)), normalized_caps=list(map(str,u)),
                q7_clique_cap_sum=str(clique_sum), q7_clique_polynomial=str(1-clique_sum),
                full_matching_polynomial=str(values[-1]),
                nonpositive_induced_polynomials=sum(v <= 0 for v in values),
                all12_active_7_11_cap=str(4*beta[0]/(z[0]*z[1])))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = ap.parse_args()
    family = make_family()
    period = lcm(*(row['modulus'] for row in family))
    check('exact_full_period', period == 225*49*121 == 1334025)
    base = [row for row in family if not row['group'].startswith('edge_')]
    edges = [row for row in family if row['group'].startswith('edge_')]
    stars = [row for row in family if row['group'].startswith('star_')]
    check('all_14_stars_centrally_active', len(stars) == 14 and
          all(CENTRAL % row['components'][0]['modulus'] == row['components'][0]['residue'] for row in stars))
    purecentral = [row for row in family if row['modulus'] in (3,9,5,25,15)]
    check('central_cell_live_before_outside_deletions', all(not hit(CENTRAL,row) for row in purecentral))
    cell = list(range(CENTRAL, period, CENTRAL_PERIOD))
    check('exact_local_coordinate_bijection', len(cell) == 49*121 and
          len({(n % 49,n % 121) for n in cell}) == 49*121)
    local_star = [n for n in cell if all(not hit(n,row) for row in base)]
    local_full = [n for n in cell if all(not hit(n,row) for row in family)]
    check('actual_star_product_is_220_points', len(local_star) == 220)
    check('actual_local_fibre_is_empty', len(local_full) == 0)
    q_survivors = sorted({n % 49 for n in local_star})
    s_survivors = sorted({n % 121 for n in local_star})
    check('q_survivors_are_four_registered_children', q_survivors == [15,22,29,36])
    check('s_survivors_are_five_registered_roots', s_survivors == [n for n in range(121) if n % 11 in range(6,11)])
    check('local_star_set_is_cartesian_product', len(q_survivors)*len(s_survivors) == len(local_star))
    hits = []
    for row in edges:
        count = sum(hit(n,row) for n in local_star)
        hits.append(dict(name=row['name'], modulus=row['modulus'], residue=row['residue'], hits=count))
    check('four_first_root_rectangles_each_cover_44', [x['hits'] for x in hits if x['name'].startswith('edge_11_')] == [44]*4)
    check('four_square_cylinders_each_cover_11', [x['hits'] for x in hits if x['name'].startswith('edge_21_')] == [11]*4)
    check('four_other_square_labels_are_source_null', [x['hits'] for x in hits if x['name'].startswith('edge_12_')] == [0]*4)
    check('eight_active_labels_partition_actual_star_product', all(sum(hit(n,row) for row in edges) == 1 for n in local_star), len(local_star))
    # Actual root-balanced pure marginals. Higher digits may be uniform.
    rho7 = [F() if n % 7 == 0 or n == 43 else F(1,36) if n % 7 == 1 else F(1,42) for n in range(49)]
    rho11 = [F() if n % 11 == 0 else F(1,110) for n in range(121)]
    check('actual_pure_marginals_are_probabilities', sum(rho7) == sum(rho11) == 1)
    check('actual_first_root_caps', all(sum(rho7[n] for n in range(49) if n % 7 == k) == F(1,6) for k in range(1,7)) and
          all(sum(rho11[n] for n in range(121) if n % 11 == k) == F(1,10) for k in range(1,11)))
    check('actual_square_and_density_caps', max(rho7) <= F(1,35) and max(rho11) <= F(1,99) and
          49*max(rho7) <= F(7,5) and 121*max(rho11) <= F(11,9))
    f7 = sum(rho7[n] for n in q_survivors)
    f11 = sum(rho11[n] for n in s_survivors)
    z7,z11 = 1-F(5,6)-F(2,35), 1-F(5,10)-F(2,99)
    check('positive_actual_uniform_thinning_available', 0 < z7 <= f7 and 0 < z11 <= f11)
    # Global residue table checks the SAME34 phases, not independently chosen cells.
    live = bytearray(b'\1')*period
    for row in family:
        m, a = row['modulus'], row['residue']
        live[a::m] = b'\0'*((period-1-a)//m+1)
    global_count = live.count(1)
    witness = live.index(1)
    check('global_family_is_not_a_cover', global_count > 0 and all(not hit(witness,row) for row in family))
    check('direct_cell_and_global_table_agree', all(live[n] == 0 for n in cell), len(cell))
    result = dict(schema='free-within-edge-actual-dead-central-fibre-v1', scope=__doc__,
                  family=family, actual_prime_support=[3,5,7,11],
                  containing_literal_core=[3,5,7,11,13,17,19], exact_global_period=period,
                  central_cell=dict(residue=CENTRAL,modulus=CENTRAL_PERIOD,coordinate_points=len(cell),
                                    actual_star_survivors=len(local_star), actual_final_survivors=len(local_full),
                                    q49_survivors=q_survivors,s121_survivors=s_survivors,edge_hit_counts=hits),
                  actual_source=dict(q7_star_mass=str(f7),q11_star_mass=str(f11),
                                     Z7=str(z7),Z11=str(z11),thinning7=str(z7/f7),thinning11=str(z11/f11),
                                     positive_product_mass=str(z7*z11),edge_union_probability='1'),
                  global_uncovered_count=global_count,global_uncovered_witness=witness,
                  global_uncovered_density=str(F(global_count,period)),
                  complete_global_survivor_table_sha256=hashlib.sha256(live).hexdigest(),
                  uniform_box_obstruction=exact_uniform_box_obstruction(),
                  checks=CHECKS,check_count=len(CHECKS),new_lean_verification=False,
                  producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ('exact_global_period','global_uncovered_count','global_uncovered_witness','check_count')},indent=2))
    print('local:220 ->0; global family is not a cover; no Lean verification')


if __name__ == '__main__':
    main()
