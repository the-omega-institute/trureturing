"""Reuse the pinned paired 763 source; check two actual head extensions.

All new computation is exact rational arithmetic. Same-source support,
restriction monotonicity and analytic continuation are ordinary proof inputs.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
import json
from pathlib import Path
import sys

SOURCE_FILES = {
    'fibre-credit-depth-two-obstruction/fibre_credit_depth_two_eight_head_tail.py':
    '3fbc339694e007783611b33f2a79a0b810df601e4a9f795991c50cbd3f45233a',
    'fibre-credit-depth-two-obstruction/fibre_credit_depth_two_eight_head_tail.json':
    '7d36e5003e12630787184af423db7a29972fa446195aa70c9b4765fc0d6d86eb',
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def step(mass, moment, prime):
    a = F(3 * prime - 1, (prime - 1) ** 2)
    return mass - moment / (prime - 1) ** 2, moment * (1 + 2 * a)


def tail_allowance(cutoff, ell):
    need(cutoff >= 286 and ell >= 4 and 3 ** ell <= cutoff,
         'Inherited prime-product premise parameters')
    # Integration by parts, evaluated at log(B)>=ell. This recurrence
    # independently matches the degree-four factorial sum used in 763.
    polynomial = F(1)
    for degree in range(1, 5):
        polynomial = 1 + F(degree, ell) * polynomial
    c = F(2 * ell ** 2 + 1, 2 * ell ** 2 - 1)
    tau = c ** 4 / cutoff * F(cutoff, cutoff - 1) ** 2 * polynomial
    return polynomial, c, tau


def calculate(base):
    need(not sys.flags.optimize, 'Pinned source evaluator requires assertions enabled')
    sys.dont_write_bytecode = True
    for name, pin in SOURCE_FILES.items():
        need(sha256((base / name).read_bytes()).hexdigest() == pin,
             'Pinned source mismatch: ' + name)
    path = base / next(iter(SOURCE_FILES))
    spec = spec_from_file_location('e7_paired_head763', path)
    source = module_from_spec(spec)
    spec.loader.exec_module(source)
    result = source.calculate(base)
    retained = json.loads(path.with_suffix('.json').read_text())
    need(json.loads(json.dumps(result, default=str)) == retained,
         'Fresh paired source recomputation must equal its retained result')
    mass = result['source_mass_lower']
    moment = result['joint_query_seed_upper']
    need(mass == F(10237584019, 168750000000), 'Eight-head source mass')
    need(moment == F(26010182627, 1040449536), 'Eight-head source joint moment')
    initial = (mass, moment)
    heads = [{'head_size': 8, 'added_reference_prime': None,
              'mass_lower': mass, 'joint_query_upper': moment}]
    for prime in (31, 37):
        old_mass, old_moment = mass, moment
        mass, moment = step(mass, moment, prime)
        need(0 < mass <= old_mass and moment >= old_moment,
             'Positive homogeneous head recurrence')
        heads.append({'head_size': len(heads) + 8,
                      'added_reference_prime': prime,
                      'new_bad_mass_upper': old_moment / (prime - 1) ** 2,
                      'mass_lower': mass, 'joint_query_upper': moment})
    need(heads[1]['mass_lower'] == F(60153961455906929, 1828915200000000000),
         'Nine-head exact mass')
    need(heads[1]['joint_query_upper'] == F(7048759491917, 234101145600),
         'Nine-head exact joint moment')
    need(mass == F(817539304151922053, 84652646400000000000),
         'Ten-head exact mass')
    need(moment == F(2671479847436543, 75848771174400),
         'Ten-head exact joint moment')
    rows = []
    for head, cutoff, ell, lower in zip(
            heads, (1400, 3000, 10000), (6, 7, 8),
            (F(1, 256), F(1, 200), F(1, 1100))):
        polynomial, c, tau = tail_allowance(cutoff, ell)
        charge = F(4, 3) * head['joint_query_upper'] * tau
        margin = head['mass_lower'] - charge
        need(margin > lower > 0, 'Strict positive all-prime tail margin')
        rows.append(dict(head, tail_cutoff=cutoff, ell=ell,
                         integral_polynomial=polynomial,
                         prime_product_constant=c, tau4=tau,
                         tail_charge_upper=charge,
                         final_distorted_mass_lower=margin,
                         simple_final_strict_lower=lower))
    need(rows[0]['final_distorted_mass_lower'] ==
         result['distorted_survivor_mass_lower'], 'Eight-head baseline agrees')
    failed_mass, _ = step(mass, moment, 41)
    need(failed_mass < 0, 'The same scalar ledger does not certify an eleventh head')
    return {
        'scope': 'Finite pairwise-distinct odd numerical moduli>1. '
        'At least one of 3,5,7,11 is absent from the entire original LCM. '
        'For each row, at most head_size prime divisors are <=tail_cutoff. '
        'All original phases, finite heights, support arities and the finite '
        'number of larger primes are unrestricted.',
        'source_files': SOURCE_FILES,
        'source_dependencies': result['dependencies'],
        'source_mass_and_joint_moment': initial,
        'source_geometry_reexecuted': False,
        'source_formula_vertices_recomputed': 32,
        'head_delta': F(1, 2),
        'head_kernel_cap': F(2),
        'head_charge_factor': F(1),
        'actual_bad_set_deleted_after_each_added_head': True,
        'head_law_renormalized': False,
        'tail_delta': F(1, 4),
        'tail_kernel_cap': F(4, 3),
        'tail_charge_factor': F(4, 3),
        'rows': rows,
        'eleventh_reference_prime': 41,
        'eleventh_scalar_ledger_mass_lower': failed_mass,
        'eleventh_failure_scope': 'Failure of this sufficient scalar bound only; '
        'not a covering example or an obstruction to another source or method.',
        'analytic_prime_product_proved_by_code': False,
        'same_source_restriction_proved_by_code': False,
        'lean_verification': False,
        'mass_interpretation': 'All final lower bounds are distorted mass, '
        'not asserted uniform final Haar-density bounds.',
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write-result', type=Path)
    args = parser.parse_args()
    base = Path(__file__).resolve().parent.parent
    result = json.loads(json.dumps(calculate(base), default=str))
    if args.write_result:
        args.write_result.write_text(json.dumps(result, indent=2) + '\n')
    else:
        retained = json.loads(Path(__file__).with_suffix('.json').read_text())
        need(result == retained, 'Retained result agrees with exact recomputation')
    print(json.dumps(result, indent=2))
