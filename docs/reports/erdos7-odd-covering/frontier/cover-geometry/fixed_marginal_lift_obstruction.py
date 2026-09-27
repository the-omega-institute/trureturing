"""Actual full-seven-support obstruction to an R_Q-only inverse bridge.

The24-label prior is explicitly constructed, not identified with a PA output.
A separate fixed-cofactor variant uses the empty-input PA Haar source.
All finite checks use exact integers/Fractions and remain active under -O.
"""
from fractions import Fraction as F
from itertools import combinations
from math import prod
from pathlib import Path
import json

Q = (5, 7, 11, 13, 17, 19)
D = prod(Q[1:])
rH = prod((F(p, p-1) for p in Q), start=F(1))-1
other_factor = prod((1+F(p, p-1) for p in Q[1:]), start=F(1))
target = F(566, 49)
Bstar = F(432040125182653876501, 86355045355449035400)
checks = []


def check(label, claim):
    if not claim:
        raise ValueError(label)
    checks.append(label)


def example(N, enumerate_ternary=False):
    labels = []
    for e in range(1, N+1):
        for v in (1, 2):
            j = 2*e-2+v
            cofactor = 5**j*D
            ternary_modulus = 3**e
            ternary_residue = v*3**(e-1)
            modulus = ternary_modulus*cofactor
            residue = (cofactor*((ternary_residue*pow(cofactor, -1, ternary_modulus))
                                 % ternary_modulus)) % modulus
            labels.append({'e': e, 'v': v, 'j': j, 'cofactor': cofactor,
                           'modulus': modulus, 'residue': residue,
                           'ternary_modulus': ternary_modulus,
                           'ternary_residue': ternary_residue})
            check(f'N{N}: CRT ternary {j}', residue % ternary_modulus == ternary_residue)
            check(f'N{N}: CRT Q {j}', residue % cofactor == 0)
            check(f'N{N}: all seven primes divide label {j}',
                  all(modulus % p == 0 for p in (3,)+Q))
            check(f'N{N}: no extra prime {j}', modulus == 3**e*5**j*D)
    check(f'N{N}: exactly 2N labels', len(labels) == 2*N)
    check(f'N{N}: distinct numerical moduli', len({r['modulus'] for r in labels}) == 2*N)
    check(f'N{N}: every numerical Q cofactor occurs once',
          len({r['cofactor'] for r in labels}) == 2*N)
    for a, b in combinations(labels, 2):
        common = 3**min(a['e'], b['e'])
        check(f'N{N}: disjoint ternary cylinders {a["j"]},{b["j"]}',
              (a['ternary_residue']-b['ternary_residue']) % common != 0)
    removed_cells = sum(3**(N-r['e']) for r in labels)
    check(f'N{N}: exact complement count', removed_cells == 3**N-1)
    check(f'N{N}: zero survives every actual label',
          all(r['ternary_residue'] != 0 for r in labels))
    if enumerate_ternary:
        survivors = [t for t in range(3**N)
                     if all(t % r['ternary_modulus'] != r['ternary_residue']
                            for r in labels)]
        check(f'N{N}: direct ternary enumeration', survivors == [0])

    atom_full_query = (2*N+F(5, 4))*other_factor
    eps = (2-rH)/(atom_full_query-1-rH)
    check(f'N{N}: positive proper mixture', 0 < eps < 1)
    prior_query = (1-eps)*rH+eps*(atom_full_query-1)
    check(f'N{N}: exact prior query two', prior_query == 2)
    check(f'N{N}: below PA scalar bound', prior_query < Bstar)
    lower = eps*((N+F(3, 2))*atom_full_query-1)
    check(f'N{N}: linear lower certificate', lower > (2-rH)*N)
    fixed_marginal_lower = N*eps*atom_full_query
    check(f'N{N}: any-joint fixed-marginal linear lower', fixed_marginal_lower > (2-rH)*N)
    fixed_marginal_complete_lower = prior_query+(N+F(1, 2))*eps*atom_full_query
    check(f'N{N}: complete fixed-marginal lower strengthens truncation',
          fixed_marginal_complete_lower > fixed_marginal_lower)

    # The complete actual Q-fibre profile, no enormous cell enumeration.
    # Outside the other five zero roots: c=1. Inside, j is capped v5(x).
    profiles = [{'name': 'outside_other_roots', 'haar_mass': 1-F(1, D), 'c': F(1)}]
    for j in range(2*N+1):
        hp = F(4, 5**(j+1)) if j < 2*N else F(1, 5**(2*N))
        c = F(1, 3**(j//2)) if j % 2 == 0 else F(2, 3**((j+1)//2))
        profiles.append({'name': f'capped_v5_{j}', 'haar_mass': hp/D,
                         'c': c, 'deep': j == 2*N})
        if enumerate_ternary:
            active = [r for r in labels if r['j'] <= j]
            count = sum(all(t % r['ternary_modulus'] != r['ternary_residue']
                            for r in active) for t in range(3**N))
            check(f'N{N}: actual fibre profile {j}', F(count, 3**N) == c)
    check(f'N{N}: Haar profile normalized', sum((r['haar_mass'] for r in profiles), F(0)) == 1)
    for r in profiles:
        r['pi_mass'] = (1-eps)*r['haar_mass'] + (eps if r.get('deep') else 0)
    Z = sum((r['pi_mass']/r['c'] for r in profiles), F(0))
    check(f'N{N}: inverse moment at least deep-atom charge', Z >= eps*3**N)
    check(f'N{N}: finite positive inverse normalization', Z >= 1)
    for r in profiles:
        r['raw_prior_mass'] = r['pi_mass']/r['c']/Z
        check(f'N{N}: actual inverse product-deletion recovery {r["name"]}',
              r['raw_prior_mass']*r['c']*Z == r['pi_mass'])
    check(f'N{N}: inverse prior normalized', sum((r['raw_prior_mass'] for r in profiles), F(0)) == 1)

    # Explicit alternative GOOD law in the SAME conditional-fibre class.
    # Avoid the smallest zero-Q cylinder; it contains all original Q events.
    good_RQ = rH/(1-F(1, 5*D))
    good_RP = F(1, 2)+F(3, 2)*good_RQ
    check(f'N{N}: an alternative good law remains below target', good_RP < target)
    return {'N': N, 'labels': labels, 'atom_full_Q_query': atom_full_query,
            'epsilon': eps, 'prior_RQ': prior_query,
            'conditioned_RP_lower': lower, 'linear_lower': (2-rH)*N,
            'any_joint_fixed_marginal_RP_lower': fixed_marginal_lower,
            'any_joint_fixed_marginal_complete_RP_lower': fixed_marginal_complete_lower,
            'inverse_moment': Z, 'inverse_moment_lower': eps*3**N,
            'profile_count': len(profiles), 'profiles': profiles,
            'alternative_good_RQ': good_RQ, 'alternative_good_RP': good_RP}


check('Haar Q query constant', rH == F(157435, 165888))
small = [example(n, True) for n in range(1, 6)]
actual = example(12)
check('24-label mixture exact', actual['epsilon'] == F(174341, 168009842))
check('24-label conditional query lower exact',
      actual['conditioned_RP_lower'] == F(9781743339019, 688168312832))
check('24-label conditional query exceeds target', actual['conditioned_RP_lower'] > target)
check('24-label linear lower already exceeds target', actual['linear_lower'] > target)
check('24-label any-joint fixed-marginal lower exact',
      actual['any_joint_fixed_marginal_RP_lower'] == F(3257561585, 257805312))
check('24-label any-joint fixed-marginal lower exceeds target',
      actual['any_joint_fixed_marginal_RP_lower'] > target)
check('24-label complete fixed-marginal lower exact',
      actual['any_joint_fixed_marginal_complete_RP_lower'] == F(93813694601, 6187327488))
check('24-label complete fixed-marginal lower exceeds fifteen',
      actual['any_joint_fixed_marginal_complete_RP_lower'] > 15)
deep_density = 1-actual['epsilon']+actual['epsilon']*5**24*D
check('24-label Q density exceeds ten to nineteen', deep_density > 10**19)

# Fixed two-cofactor variant: actual empty-input PA gives Haar Q.
# Check small actual instances, while the proof supplies arbitrary depth.
for n in range(1, 6):
    fixed_labels = [(3**e*5**v*D, e, v) for e in range(1, n+1) for v in (1, 2)]
    check(f'fixed-cofactor N{n}: distinct actual numerical labels',
          len({m for m, e, v in fixed_labels}) == 2*n)
    check(f'fixed-cofactor N{n}: one original per cofactor and ternary exponent',
          len({(5**v*D, e) for m, e, v in fixed_labels}) == 2*n)
    surviving = [t for t in range(3**n)
                 if all(t % 3**e != v*3**(e-1) for m, e, v in fixed_labels)]
    check(f'fixed-cofactor N{n}: common Q cell forces unique ternary word', surviving == [0])
fixed_depth = 1000000
fixed_a = F(13, 4)*other_factor
fixed_cell_mass = F(1, 25*D)
fixed_coefficient = fixed_cell_mass*fixed_a
fixed_lower = fixed_depth*fixed_coefficient
fixed_complete_lower = rH+(fixed_depth+F(1, 2))*fixed_coefficient
check('Haar-source variant full Q query factor', fixed_a == F(2407405, 18432))
check('Haar-source variant linear coefficient', fixed_coefficient == F(481, 29767680))
check('Haar-source variant exact large-depth lower', fixed_lower == F(1503125, 93024))
check('Haar-source variant crosses gate', fixed_lower > target)
check('Haar-source variant complete lower exact', fixed_complete_lower == F(9166519379, 535818240))
check('Haar-source variant complete lower exceeds seventeen', fixed_complete_lower > 17)
check('actual empty-input PA scalar norm below one', rH < 1)


def encode(x):
    if isinstance(x, F):
        return str(x)
    if isinstance(x, dict):
        return {str(k): encode(v) for k, v in x.items()}
    if isinstance(x, list):
        return [encode(v) for v in x]
    return x


result = {'verdict': 'RQ-only fixed-marginal lift refuted', 'checks_passed': len(checks),
          'actual24_prior_is_claimed_PA_output': False,
          'optimized_conditional_class_refuted': False,
          'unrestricted_noncoverage_refuted': False,
          'Lean_run': False,
          'Q': Q, 'D': D, 'Haar_RQ': rH, 'other_query_factor': other_factor,
          'Bstar': Bstar, 'continuation_target': target,
          'actual24': actual, 'small_depth_checks': [r['N'] for r in small],
          'actual24_Q_density_on_deep_cell': deep_density,
          'fixed_two_cofactor_Haar_source': {
              'cofactors': [5*D, 25*D], 'N': fixed_depth,
              'number_of_actual_originals': 2*fixed_depth,
              'Q_source': 'Haar; actual PA output for empty selected input',
              'source_is_asserted_appropriate_for_every_selector': False,
              'RQ': rH, 'common_Q_cell_Haar_mass': fixed_cell_mass,
              'full_Q_query_factor': fixed_a, 'linear_lower_coefficient': fixed_coefficient,
              'any_joint_fixed_Haar_marginal_RP_lower': fixed_lower,
              'any_joint_fixed_Haar_marginal_complete_RP_lower': fixed_complete_lower,
              'complete_lower_decimal': float(fixed_complete_lower),
              'lower_decimal': float(fixed_lower),
              'large_original_inventory_enumerated': False},
          'decimals': {key: float(actual[key]) for key in ('epsilon', 'prior_RQ',
                'conditioned_RP_lower', 'linear_lower', 'inverse_moment_lower',
                'alternative_good_RP', 'any_joint_fixed_marginal_RP_lower',
                'any_joint_fixed_marginal_complete_RP_lower')},
          'check_labels': checks}
Path(__file__).with_suffix('.json').write_text(json.dumps(encode(result), indent=2)+'\n')
print(json.dumps({'verdict': result['verdict'], 'checks_passed': len(checks),
                  'decimals': result['decimals']}, indent=2))
