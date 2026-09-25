#!/usr/bin/env python3
"""An actual irredundant core defeats unrestricted linear schedule credits.

Exact finite cylinder counts and Euler tails; no optimizer or Lean claim.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from math import lcm, prod
from pathlib import Path


def encode(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, dict):
        return {str(k): encode(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [encode(v) for v in x]
    return x


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=Path(__file__).with_name('linear_schedule_credit_obstruction_input.json'))
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    raw = args.input.read_bytes()
    source = json.loads(raw)
    checks = {}
    evaluations = 0

    def require(name, condition):
        nonlocal evaluations
        evaluations += 1
        if not condition:
            raise ArithmeticError(name)
        checks[name] = True

    P = source['primes']
    rows = source['originals']
    labels = [r['modulus'] for r in rows]
    require('reference_seven_primes', P == [3, 5, 7, 11, 13, 17, 19])
    require('forty_distinct_sorted_odd_labels', len(labels) == len(set(labels)) == 40
            and labels == sorted(labels) and all(d > 1 and d % 2 for d in labels))
    period = lcm(*labels)
    require('full_squarefree_period', period == prod(P) == 4849845)
    alive = bytearray(b'\1') * period
    for row in rows:
        d, a, z = (row[k] for k in ('modulus', 'residue', 'private_witness'))
        require('literal_valid_original_' + str(d), 0 <= a < d and period % d == 0)
        require('private_witness_own_class_' + str(d), 0 <= z < period and z % d == a)
        for other in rows:
            require('private_witness_other_classes',
                    other['modulus'] == d or z % other['modulus'] != other['residue'])
        alive[a::d] = bytes(len(range(a, period, d)))
    count = alive.count(1)
    h = F(count, period)
    A = prod(F(p, p-1) for p in P) - 1
    alpha = F(7235955529, 6075000000000)
    target = F(566, 49)
    old_target = F(565, 51)
    reciprocal_originals = sum((F(1, d) for d in labels), F())
    unused_Haar_upper = (A-reciprocal_originals)/h
    require('exact_actual_survivor', count == 741126 and h == F(247042, 1616615))
    require('nontrivial_reciprocal_Haar_regime', F(3, 20) < h < A/target < A/old_target)
    require('full_unused_Haar_cost_below_four',
            unused_Haar_upper == F(99943555709, 27320868864) < 4)
    require('known_seven_prime_density_constant', 0 < alpha < F(1, 800) < h)
    require('complete_nonunit_Euler_mass', A == F(212731, 110592))
    witness = next(i for i, flag in enumerate(alive) if flag)
    require('literal_common_survivor', all(witness % row['modulus'] != row['residue'] for row in rows))

    # e <= 1+1+1/2 + (1/6) sum_{j>=0}4^-j = 49/18 < 11/4.
    exp_one_majorant = F(5, 2) + F(1, 6)/(1-F(1, 4))
    require('entire_exponential_tail_majorant', exp_one_majorant == F(49, 18) < F(11, 4))
    alpha_over_Z_upper = F(1, 800)*F(11, 4)**4/F(3, 20)
    credit_lower = len(labels)*(1-alpha_over_Z_upper)
    require('all_schedule_certificate_lower_bound',
            alpha_over_Z_upper == F(14641, 30720)
            and credit_lower == F(16079, 768) > target)

    # Resolve only these forty gcd labels exactly. All other query gcds,
    # and all exponent heights, are paid by one exact Euler remainder.
    query_rows = []
    charged = F()
    reciprocal_charge = F()
    for d in labels:
        counts = [alive[a::d].count(1) for a in range(d)]
        require('complete_residue_partition_' + str(d), sum(counts) == count)
        maximum = max(counts)
        phase = counts.index(maximum)
        factor = prod(F(p, p-1) for p in P if d % p == 0)
        require('query_cylinder_Haar_cap_' + str(d), maximum <= period//d)
        q = F(maximum, count)
        charged += factor*q
        reciprocal_charge += factor/d
        query_rows.append(dict(gcd_label=d, maximizing_phase=phase,
                               survivor_count=maximum, query_probability=q,
                               complete_height_coefficient=factor))
    tail = A-reciprocal_charge
    require('positive_entire_unresolved_gcd_tail', tail > 0)
    query_upper = charged+tail/h
    require('one_actual_law_full_query_bound',
            query_upper == F(1506044247059, 409813032960) < 4 < old_target < target)
    out = dict(schema='linear-schedule-credit-obstruction-v1',
               input=dict(file=args.input.name, sha256=sha256(raw).hexdigest()),
               scope=dict(numerical_labels='forty actual irredundant distinct odd moduli',
                          source='normalized Haar on the full actual survivor, with independent Haar tails',
                          method='fractionally cover every label by nonnegative schedule credits whose total is at most one',
                          excluded='restricted actual-query incidence credits; exponential inside-survival methods; unrestricted Erdos7 settlement',
                          lean_verified=False),
               period=period, original_count=len(labels), survivor_count=count,
               survivor_Haar=h, avoiding_integer=witness,
               constants=dict(all_nonunit_reciprocal_mass=A, alpha7=alpha,
                              target=target, old_target=old_target,
                              original_reciprocal_mass=reciprocal_originals),
               obstruction=dict(unused_Haar_upper=unused_Haar_upper,
                                free_energy_upper_strict=4,
                                alpha_over_Z_strict_upper=alpha_over_Z_upper,
                                schedule_certificate_strict_lower=credit_lower),
               actual_law=dict(query_rows=query_rows, finite_query_sum=charged,
                               all_unresolved_gcd_reciprocal_tail=tail,
                               full_all_height_query_upper=query_upper),
               checks=checks, predicate_evaluations=evaluations,
               producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(encode(out), indent=2)+'\n')
    print(json.dumps(encode(dict(checks=len(checks), evaluations=evaluations,
                                survivor_Haar=h, certificate_lower=credit_lower,
                                actual_full_query_upper=query_upper))))


if __name__ == '__main__':
    main()
