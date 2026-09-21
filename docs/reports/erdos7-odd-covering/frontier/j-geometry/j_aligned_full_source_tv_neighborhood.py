#!/usr/bin/env python3
"""Exact numerical companion for the complete357 source-TV lemma."""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
DEFAULT_BASE = Path(__file__).resolve().parents[2]
CERTIFICATE = Path('certificates/source_norms/j-geometry/j_aligned_full_source_tv_neighborhood.json')
INPUTS = (
    'certificates/source_norms/j-geometry/j_aligned_complete_moment_comparison.json',
    'certificates/source_norms/j-geometry/j_compact_source_neighborhood.json',
)
ANCHORS = (
    'profile-notes/001-064/18-actual-bb-kernels-with-fixed-old-second-moment-need-not-be-uniformly-continuous.md',
    'profile-notes/001-064/62-endpoint-square-from-cylinder-intersections.md',
    'profile-notes/257-320/302-a-positive-actual-source-neighborhood-keeps-j-below403.md',
    'profile-notes/257-320/317-the-complete-actual-aligned-j-comparison-crosses403.md',
    'profile-notes/257-320/318-a-finite-aligned-source-neighborhood-keeps-j-below403.md',
)


def require(value, message):
    if not value:
        raise ValueError(message)


def product(values):
    ans = F(1)
    for value in values:
        ans *= value
    return ans


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def calculate(base, io):
    raws = [io.read_artifact_bytes(base/p) for p in INPUTS]
    c, comp = [json.loads(raw, object_pairs_hook=io._unique) for raw in raws]
    require(c['schema'] == 'erdos7-aligned-complete-moment-comparison-v1'
            and comp['schema'] == 'erdos7-j-compact-neighborhood-companion-v1',
            'Actual aligned endpoint and unchanged original target inventory')
    targets = comp['original_target_increment_bounds']
    names = ['cost-'+str(i) for i in range(52)] + [
        'AP11-'+str(i) for i in range(4)] + ['hinge4', 'mean', 'square']
    require(len(targets) == 59 and {r['name'] for r in targets} == set(names)
            and {r['name'] for r in c['results']} == set(names),
            'Every original independent target, without duplicate names')
    f = {r['name']: (F(r['low_load_values'][0]), F(r['quadratic_increment_constant']))
         for r in targets}
    require(all(v >= 0 and l >= 0 for v, l in f.values()), 'Nonnegative target data')
    # Recheck the full increment property from the retained finite head and
    # polynomial tail, including the transition from load8 to load9.
    for row in targets:
        head = list(map(F, row['low_load_values']))
        a0, a1, a2 = map(F, row['tail_polynomial'])
        require(len(head) == 8, 'Original finite integer head')
        extended = head + [a0+9*a1+81*a2]
        L = f[row['name']][1]
        require(all(abs(extended[i]-extended[i-1]) <= L*(2*i+1)
                    for i in range(1,9)) and abs(a2)+abs(a1)/19 <= L,
                'Whole integer quadratic-increment certificate '+row['name'])

    weights = list(map(F, c['cost_weights']))
    signed = F(c['signed_mass_coefficient'])
    square = F(c['complete_square_weight'])
    offset = F(c['offset'])
    a, b = F(1,7986), F(1,87846)
    require(len(weights) == 52 and min(weights) > 0 and signed < 0 and square > 0,
            'Original signed comparison prices')
    require(F(c['count_law']['remaining_hinge1_coefficient']) == a
            and F(c['count_law']['whole_constant_coefficient']) == b,
            'The entire original count tail')
    N0 = abs(signed)+sum(w*f['cost-'+str(i)][0] for i,w in enumerate(weights))+square*f['square'][0]
    N1 = sum(w*f['cost-'+str(i)][1] for i,w in enumerate(weights))+square*f['square'][1]
    E0 = 1+f['hinge4'][0]/6+(sum(f['AP11-'+str(i)][0] for i in range(4))+a*f['mean'][0]+abs(b-a))/7
    E1 = f['hinge4'][1]/6+(sum(f['AP11-'+str(i)][1] for i in range(4))+a*f['mean'][1])/7
    require((N0,N1,E0,E1) == (
        F(1556107055932111300021081,5393494724947082158204800),
        F(2070782892374236779637510453,148113662831239102344547200),
        F(29283,29282), F(1357579,38740086)), 'Exact combined59-target modulus')

    S2 = product(F(p*(p+1),(p-1)**2) for p in (3,5,7))
    S4 = product(F(p*(p**3+11*p*p+11*p+1),(p-1)**4) for p in (3,5,7))
    centered = S4-2*S2+1
    require((S2,S4,centered) == (F(35,4),F(16625,12),F(16427,12)),
            'Whole geometric CRT moments and their nonnegative centered polynomial')
    density_centered = F(6,5)*centered
    require(density_centered == F(16427,10) < 41**2, 'Complete rational square-root majorant')
    t = F(1,100000000)
    m = F(41,10000)
    require(density_centered*t < m*m, 'Exact square-root payment at the stated TV radius')
    N = F(c['comparison_upper']['numerator'])
    E = F(c['comparison_upper']['denominator'])
    require(N > 0 and E > 0 and offset+N/E == F(c['comparison_upper']['comparison']),
            'Exact original endpoint comparison')
    lifted_N, lowered_E = N+N0*t+N1*m, E-E0*t-E1*m
    require(lowered_E > 0, 'Positive complete denominator after all independent errors')
    j = offset+lifted_N/lowered_E
    upper = F(401051,1000)
    require(j < upper < F(803,2) < 403, 'Explicit actual measure-TV neighborhood')
    cut = 18
    T = F(35,16)*(1-product(1-F(1,p**(cut+1)) for p in (3,5,7)))
    T7 = F(1,6*7**cut)
    coupling = F(12,5)*(T+T7)
    require(0 < coupling < t, 'Full forbidden and normalization tails for matching source prefixes')
    pins = {p: sha256(raw).hexdigest() for p,raw in zip(INPUTS,raws)}
    pins.update({p: sha256(io.read_artifact_bytes(base/p)).hexdigest() for p in ANCHORS})
    return encode({
        'schema': 'erdos7-aligned-full-source-tv-neighborhood-v1',
        'source_sha256': pins,
        'complete_own_target_count': 59,
        'crt_second_moment': S2, 'crt_fourth_moment': S4,
        'centered_fourth_moment': centered,
        'difference_density_bound': F(6,5),
        'centered_density_moment': density_centered,
        'numerator_mass_coefficient': N0, 'numerator_moment_coefficient': N1,
        'denominator_mass_coefficient': E0, 'denominator_moment_coefficient': E1,
        'full_variation_radius': t, 'moment_payment_upper': m,
        'comparison_rational_upper': upper,
        'source_prefix_exponent_cut': cut,
        'full_forbidden_tail': T, 'pure7_tail': T7,
        'matching_prefix_full_variation_upper': coupling,
        'source_parameter_radius': 'not-established',
        'scope': 'Actual aligned effective9 chart of318; complete357 survivor-TV radius around any actual aligned endpoint; all59 original own tests and all tails retained. Matching source prefixes give the displayed coupling. No inverse qJ/rho modulus, Gamma19 bound, global join, unrestricted Erdos7 conclusion or Lean claim.'
    }), j, lowered_E


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=DEFAULT_BASE)
    parser.add_argument('--output', type=Path)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location('aligned_tv_io',args.base/'certificate_io.py')
    require(spec is not None and spec.loader is not None, 'Canonical certificate IO available')
    io = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(io)
    result, j, E = calculate(args.base,io)
    output = args.output if args.output is not None else args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(output,json.dumps(result,indent=2)+'\n')
    else:
        given = json.loads(io.read_artifact_bytes(output),object_pairs_hook=io._unique)
        require(given == result, 'Exact canonical numerical companion replay')
    print('PASS; full source-TV radius=10^-8; complete own targets=59')
    print('J upper',float(j),'positive denominator lower',float(E))
    print('Matching source exponent box18 TV upper',float(F(result['matching_prefix_full_variation_upper'])))
    print('No numerical qJ/rho source-parameter radius established')


if __name__ == '__main__':
    main()
