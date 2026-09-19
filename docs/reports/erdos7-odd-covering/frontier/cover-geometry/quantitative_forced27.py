#!/usr/bin/env python3
"""Quantify the original forbidden27 wrong-cell deficit near a whole K face.

Exact rational continuum coefficients and finite actual source/union checks.
The universal source-tree proof is in profile121; no finite cutoff proves it.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/cover-geometry/quantitative_forced27.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/source-budgets/source_mass_compatibility.py': 'f65f0be22b250ab94d7da847a45b49c39355c15499f9cde8f18f267ca3365645',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def concentrated_bounds(sigma):
    sigma = F(sigma)
    require(0 <= sigma <= F(2, 27), 'Quantitative forced27 concentration domain')
    gap = F(1, 135)-sigma/72
    dmin = F(3, 4)-sigma/2
    zmax = F(3, 4)+sigma/4
    guards = (dmin/27, gap, dmin*(F(1, 54)-sigma/8), (F(1, 4)-sigma)/27)
    require(min(guards) == gap > 0, 'Every wrong depth3 child loses the common positive gap')
    return {'sigma': sigma, 'gap': gap, 'source_child_eta': F(0),
            'late31_additional_lower': gap, 'late_child_eta_lower': 5*gap,
            'third_child_eta_upper': F(1, 54)+sigma/8,
            'dmax_lower': dmin, 'z_upper': zmax, 'wrong_child_gap_guards': guards,
            'ideal27_defect_factor_upper': zmax/(27*gap)}


def defect_upper(sigma, z, dmax, E27, E_ge4, omega):
    data = concentrated_bounds(sigma)
    require(data['dmax_lower'] <= dmax <= z <= data['z_upper'], 'Concentrated actual availabilities')
    require(min(E27, E_ge4, omega) >= 0, 'Actual disjoint capacity defects and union error')
    factor = dmax/(27*data['gap'])
    return {'wrong_seven_weight_upper': min(F(1, 5), E27/data['gap']),
            'wrong_virtual_mass_upper': (factor-1)*E27,
            'ideal27_defect_mass_upper': (z-dmax)/135+factor*E27,
            'complete_deep_defect_mass_upper': (z-dmax)/90+E_ge4+factor*E27+omega}


def deep_reference_cap(a, b):
    require(isinstance(a, int) and isinstance(b, int) and min(a, b) >= 0, 'Nonnegative original test depths')
    three = F(1, 18) if a <= 3 else (a-F(3, 2))/3**a
    return three/(5*5**b)


def common_error_cap(a, b):
    virtual = ((a+F(3, 2))*(b+F(5, 4))-1)/(5*3**a*5**b)
    return deep_reference_cap(a, b)+virtual


def complete_five_error(mass, first_depth=2):
    """Entire independent five tail using min(mass,(108*b+67)/360/5**b)."""
    mass = F(mass)
    require(mass >= 0 and isinstance(first_depth, int) and first_depth >= 0,
            'Positive common error and a complete five tail')
    if mass == 0:
        return F(0), None
    crossing = first_depth
    while F(108*crossing+67, 360*5**crossing) > mass:
        crossing += 1
    return ((crossing-first_depth)*mass+F(270*crossing+235, 720*5**crossing), crossing)


def finite_source(constructor, height=5):
    A, B = 3**height, 5**height
    all5 = (1 << B)-1
    state, without31 = [all5]*A, [all5]*A
    pure3, pure5 = [True]*A, all5
    labels = []
    for a in range(height+1):
        for b in range(height+1):
            if a+b == 0:
                continue
            aa, ra, bb, rb = constructor.source_label(a, b, 398)
            require((aa, bb) == (a, b), 'Inherited original source label')
            labels.append((a, ra, b, rb))
            removed = sum(1 << y for y in range(rb, B, 5**b))
            if a == 0:
                pure5 &= all5 ^ removed
            for x in range(ra, A, 3**a):
                state[x] &= all5 ^ removed
                if (a, b) != (3, 1):
                    without31[x] &= all5 ^ removed
                if b == 0:
                    pure3[x] = False
    require(len(labels) == len({(a, b) for a, _, b, _ in labels}), 'Independent distinct original source moduli')
    t = sum((F(1, 3**a) for a in range(3, height+1)), F(0))
    five_deleted = sum((F(1, 5**b) for b in range(1, height+1)), F(0))
    eta = [F(1, 9)-t]+[F(1, 9)]*4
    z = 1-five_deleted
    d = [z, z, 1-3*five_deleted, 1-2*five_deleted, 1-2*five_deleted]
    late = t*five_deleted
    cells = (0, 3, 1, 4, 7)
    n = [eta[c]*d[c]-(late if c == 0 else 0) for c in range(5)]
    require([F(sum(state[x].bit_count() for x in range(c, A, 9)), A*B) for c in cells] == n,
            'Actual35 masks agree with the five source cell masses')
    source_children = [F(sum(pure3[x] for x in range(c, A, 27)), A) for c in (9, 18, 0)]
    ell31 = F(sum(a.bit_count()-b.bit_count() for a, b in zip(without31, state)), A*B)
    require(source_children[0] == 0 and source_children[1] == F(1, 27) and ell31 == F(1, 135),
            'Actual source27 is empty and source135 contributes its distinct late child')
    pi = 1-F(1, 7**height)
    qK = (18*t)**2*(4*five_deleted)**4*pi
    sigma = 1-qK
    bound = concentrated_bounds(sigma)
    require(9*t >= (1-sigma)/2 and late >= (1-sigma)/72,
            'Actual original barycentric mass supplies both source concentrations')
    require(ell31 >= bound['gap'] and source_children[2] <= bound['third_child_eta_upper'],
            'Finite actual child masses obey the universal source-tree guards')
    return {'height': height, 'A': A, 'B': B, 'state': state, 'pure5': pure5,
            'eta': eta, 'd': d, 'n': n, 'z': z, 'sigma': sigma, 'pi': pi,
            'source_children': source_children, 'ell31': ell31}


def finite_case(source, mode):
    height, A, B = source['height'], source['A'], source['B']
    state, z, dmax = source['state'], source['z'], max(source['d'])
    P = 7**height
    pure7 = (1 << P)-1
    for e in range(1, height+1):
        pure7 &= ~sum(1 << j for j in range(6*7**(e-1), P, 7**e))
    labels = []
    for a in range(1, height+1):
        for e in range(1, height+1):
            if a == 1:
                residue = 1
            elif a == 2:
                residue = 3
            elif a == 3:
                residue = {'good': 3+9*(e % 3), 'source': 9, 'late': 18, 'third': 0,
                           'root1': 1, 'absent': None,
                           'varied': (3, 18, None, 1, 0)[e-1]}[mode]
            else:
                residue = (3+3**(a-1)) if e % 2 else (1+e*3**(a-1)) % 3**a
            if residue is None:
                continue
            re = (a+e*e) % 7**e
            seven = sum(1 << j for j in range(re, P, 7**e)) & pure7
            labels.append((a, e, residue, F(6, 5*7**e), seven))
    require(len(labels) == len({(a, e) for a, e, _, _, _ in labels}), 'Independent original forbidden labels')
    virtual = [F(0)]*A
    actual_delete = [F(0)]*A
    good_density = [F(0)]*A
    v27 = vgood = vbad = v_ge4 = good_weight = F(0)
    for a, e, residue, u, seven in labels:
        raw = F(sum(state[x].bit_count() for x in range(residue, A, 3**a)), A*B)
        require(raw <= dmax/3**a, 'Every genuine pure3 carrier respects its existing complete cap')
        if a == 3:
            v27 += u*raw
            if residue % 9 == 3:
                vgood += u*raw
                good_weight += u
                for x in range(residue, A, 27):
                    good_density[x] += u
            else:
                vbad += u*raw
                require(dmax/27-raw >= concentrated_bounds(source['sigma'])['gap'],
                        'Actual wrong27 carrier loses the universal source-tree gap')
        elif a >= 4:
            v_ge4 += u*raw
    for x in range(A):
        union = 0
        for a, e, residue, u, seven in labels:
            if x % 3**a == residue:
                virtual[x] += u
                union |= seven
        actual_delete[x] = F(union.bit_count(), pure7.bit_count())
        require(actual_delete[x] <= virtual[x], 'One actual seven union lies below its original-label virtual sum')
    weights = [F(mask.bit_count(), A*B) for mask in state]
    V = sum(a*b for a, b in zip(weights, virtual))
    delta = sum(a*b for a, b in zip(weights, actual_delete))
    omega = V-delta
    E27, E_ge4 = dmax/135-v27, dmax/270-v_ge4
    wrong_weight = F(1, 5)-good_weight
    gap = concentrated_bounds(source['sigma'])['gap']
    upper = defect_upper(source['sigma'], z, dmax, E27, E_ge4, omega)
    xi27, xi_ge4 = z/135-vgood, z/270-v_ge4
    require(E27 >= gap*wrong_weight and vbad <= upper['wrong_virtual_mass_upper'],
            'Complete wrong or absent seven weights and their actual virtual mass share E27')
    require(v27 == vgood+vbad and xi27 <= upper['ideal27_defect_mass_upper'], 'Correct-cell ideal27 defect identity and upper')
    require(xi27+xi_ge4+omega <= upper['complete_deep_defect_mass_upper'], 'One complete deep defect including all later depths')
    # Every absent/wrong depth3 label is referred to child[3]_27 of cell1.
    phi_density = [g+(wrong_weight if x % 27 == 3 else 0) for x, g in enumerate(good_density)]
    xi_mass = sum((p*source['pure5'].bit_count()-g*mask.bit_count())/(A*B)
                  for p, g, mask in zip(phi_density, good_density, state))
    require(xi_mass == xi27 and all(p >= g for p, g in zip(phi_density, good_density)),
            'One positive actual ideal27 defect, with all missing-label tail references included')
    require(all(p == 0 for x, p in enumerate(phi_density) if x % 9 != 3), 'Entire ideal27 reference is supported on cell1')
    independent_tests = []
    for b in range(1, height+1):
        residue = (b*b+2) % 5**b
        fm = sum(1 << j for j in range(residue, B, 5**b))
        qF = F((source['pure5'] & fm).bit_count(), B)
        phiF = sum(p*qF/A for p in phi_density)
        goodF = sum(g*F((mask & fm).bit_count(), A*B) for g, mask in zip(good_density, state))
        require(phiF == qF/135 and phiF >= goodF, 'Exact five section for arbitrary independently labelled tests')
        independent_tests.append({'depth': b, 'residue': residue, 'ideal27_section': phiF, 'actual_good27_section': goodF})
    eta, n = source['eta'], source['n']
    R = dmax/18+(sum(eta)+max(sum(eta[:2]), sum(eta[2:]))+max(eta))/4+F(1, 72)
    T = (source['pi']*(n[1]+sum(n[2:]))+R)/5
    rho = T-delta
    E5, E15 = sum(eta)/25, sum(eta[2:])/25  # These forbidden families are absent.
    require(E5+E15+E27+E_ge4+omega <= rho and E27+E_ge4 == dmax/90-v27-v_ge4,
            'E27 is a subfamily of E3; distinct unused capacities share one actual rho')
    return {'mode': mode, 'source_height': height, 'sigma': source['sigma'], 'z': z, 'dmax': dmax,
            'gap': gap, 'wrong_or_absent_seven_weight': wrong_weight,
            'V27_good': vgood, 'V27_wrong': vbad, 'E27': E27, 'E_ge4': E_ge4,
            'Xi27_mass': xi27, 'Xi_ge4_mass': xi_ge4, 'omega': omega, 'rho': rho,
            **upper, 'independent_five_tests': independent_tests}


def calculate(base):
    io = module('forced27_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    constructor = module('forced27_source', base/'frontier/source-budgets/source_mass_compatibility.py')
    endpoint = concentrated_bounds(F(2, 27))
    require(endpoint['gap'] == F(31, 4860) and endpoint['ideal27_defect_factor_upper'] == F(415, 93),
            'Uniform interval gap and improved ideal-defect amplification')
    # B(s)=third-child gap minus common gap; B decreases on the full interval.
    B = lambda s: F(7, 1080)-77*s/864+s*s/16
    C = lambda s: F(1, 540)-5*s/216
    require(B(F(2, 27)) == F(13, 58320) and -F(77, 864)+F(2, 27)/8 == -F(23, 288),
            'Positive endpoint minimum with a negative uniform derivative upper')
    require(C(F(2, 27)) == F(1, 7290), 'Positive endpoint minimum for the affine root1 guard')
    require(F(1, 54)*F(1, 5) == F(1, 270) and F(1, 135)+F(1, 270) == F(1, 90),
            'Original depth3 and later-depth capacities partition the complete deep3 family')
    tail_cases = []
    for mass in (F(0), F(1, 1000000), F(1, 60000), F(1, 1000), F(1, 100), F(1, 5)):
        value, crossing = complete_five_error(mass)
        if crossing is not None:
            remainder = F(270*crossing+235, 720*5**crossing)
            require(remainder == common_error_cap(0, crossing)+F(270*(crossing+1)+235, 720*5**(crossing+1)),
                    'Exact complete polynomial-geometric tail recurrence')
        tail_cases.append({'mass_upper': mass, 'first_depth': 2, 'complete_error_upper': value, 'crossing': crossing})
    require(complete_five_error(F(1, 5))[0] == F(31, 720), 'Unclipped complete descendant-five error cap')
    for a in range(9):
        for b in range(9):
            require(common_error_cap(a, b) >= 0, 'Common positive reference and union-error cylinder caps')
            if a == 0:
                require(common_error_cap(a, b) == F(108*b+67, 360*5**b), 'Pure-five specialization of the complete cylinder cap')
    source = finite_source(constructor)
    cases = [finite_case(source, mode) for mode in ('good', 'source', 'late', 'third', 'root1', 'varied', 'absent')]
    return {'schema': 'erdos7-quantitative-forced27-v1', 'source_sha256': PINS,
            'concentrated_bounds': [concentrated_bounds(x) for x in (F(0), F(1, 27), F(2, 27))],
            'continuum_guards': {'third_minus_gap_coefficients': [F(7, 1080), -F(77, 864), F(1, 16)],
                                 'third_derivative_upper': -F(23, 288), 'third_minimum': F(13, 58320),
                                 'root1_minus_gap_coefficients': [F(1, 540), -F(5, 216)], 'root1_minimum': F(1, 7290)},
            'source_children_actual_eta': source['source_children'], 'source_late31_actual_additional_mass': source['ell31'],
            'complete_later_depth_capacity_coefficient': F(1, 270), 'complete_deep_capacity_coefficient': F(1, 90),
            'shared_budget': 'E5+E15+E27+E_ge4+omega<=rho, E27+E_ge4=E3; use no additional copy of E3 or rho.',
            'complete_five_error_cases': tail_cases, 'actual_original_label_cases': cases,
            'scope': 'Ordinary quantitative wrong27 source-tree exclusion, complete original-label defect transport and exact rational experiments. All later3 and missing7 tails retained. No new global comparison, Lean verification or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    require(sha256((args.base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned certificate reader')
    io = module('forced27_writer', args.base/'certificate_io.py')
    result = encode(calculate(args.base))
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical complete forced27 certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: gap31/4860 and factor415/93 on sigma<=2/27; seven actual original-label source/union cases and complete tails.')


if __name__ == '__main__':
    main()
