#!/usr/bin/env python3
"""Exact constants for an actual-source five-slot tradeoff on a broad slab.

The ordinary proof retains the actual virtual capacity defects and the
single V-delta loss. Arithmetic checks cover complete tails, all slab
guards, source-factor domains, and the bounded six-label hinge interface.
No old-margin increment, global K update, or Lean result is claimed.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/broad_five_slot_tradeoff.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'verify_joint_frontier.py': 'a40fce0a5cb6a713dc8cb569b874d284b8dd66fb3f0a5e48fc2c69cb8fe286fe',
    'frontier/joint_survival_carriers.py': '4fd5744bebf3a20ba2a62a1fc798e0278b903b4d139ae1808c62a392d419043d',
    'frontier/common_deleted_measure_coupling.py': '8d3cf988e05dfe0467a8f3cf83c6bc745156b989774c686349bb043e72a32ef2',
    'certificates/source_norms/common_deleted_measure_coupling.json': '949b92e13b4d1f72804fac7c15b9aa1f016e920d22137fd5b540ef9f61c2d4f6',
    'frontier/global_control_faces.py': '649e9c395ed07896ccc93064c8634e402e1a277b2a96c06a3688e8b566f85c93',
    'certificates/source_norms/global_control_faces.json': 'd99736841c20977095c5c397c5949dec20960a4ee1afd72a3f926f2e773b8817',
}
ROOT = (0, 0, 1, 1, 1)
DELTA0 = F(1, 18)
R0 = F(1, 12000)
G0 = F(397, 36000)
A0 = F(1199, 60000)
C0 = F(4000, 397)
HEAD_FACTOR = F(800, 397)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module: '+str(path))
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


def geometric(prime, start):
    return F(1, prime**start)/(1-F(1, prime))


def gamma_lower(residual_after_best_slot):
    require(residual_after_best_slot >= 0, 'The actual charged residual is nonnegative')
    return max(F(0), min(G0, A0-C0*residual_after_best_slot))


def head_load(layout, cell, slot):
    r3, c9, s5, r15, s15, c45, s45 = layout
    return (1+int(ROOT[cell] == r3)+int(cell == c9)+int(slot == s5)
            +int(ROOT[cell] == r15 and slot == s15)+int(cell == c45 and slot == s45))


def source_domain(source):
    parameters = list(source.vertices())
    require(len(parameters) == 1296, 'Pinned complete effective-source vertex domain')
    h_values, root_values, differences, cell_values = [], [], [], []
    deficits = set()
    for parameter in parameters:
        deficit, alpha, beta, late, z = parameter
        deficits.add(deficit)
        require(min(deficit+alpha+beta+late) >= 0 and sum(deficit) <= F(1, 2)
                and sum(alpha) <= F(1, 4) and sum(beta) <= F(1, 4)
                and sum(late) <= F(1, 72) and F(3, 4) <= z <= 1, 'Actual parameter-domain caps')
        eta = tuple((1-v)/9 for v in deficit)
        h, h0, h1 = sum(eta), sum(eta[:2]), sum(eta[2:])
        p, a, b = z-F(3, 4), F(1, 4)-alpha[1], F(1, 4)-sum(beta[2:])
        require(all(0 <= v <= F(1, 4) for v in (p, a, b)), 'Three affine source-budget deficits')
        require(F(1, 2) <= h <= F(5, 9) and F(5, 18) <= h1 <= F(1, 3)
                and h1-h0 >= F(1, 18) and min(eta) >= F(1, 18)
                and max(eta) <= F(1, 9), 'Affine source-domain inequalities')
        widths = tuple(9*v for v in eta)
        require(sum(widths)/180 == h/20 and max(sum(widths[:2]), sum(widths[2:]))/180 == h1/20,
                'The old conditional cap retains separate complete pure5 and3-times5 budgets')
        require(h/25+h/100 == h/20 and h1/25+h1/100 == h1/20,
                'Each first-depth cofactor capacity is a distinct summand of the complete old cap')
        h_values.append(h)
        root_values.append(h1)
        differences.append(h1-h0)
        cell_values.extend(eta)
    require(len(deficits) == 6, 'All vertices of the deficit simplex are included')
    return {'vertex_count': len(parameters), 'deficit_vertices': sorted(deficits),
            'h_range': [min(h_values), max(h_values)], 'h1_range': [min(root_values), max(root_values)],
            'h1_minus_h0_lower': min(differences), 'eta_range': [min(cell_values), max(cell_values)],
            'justification': 'The asserted domain inequalities are affine in each simplex; vertex verification extends to every parameter point by convex combinations.'}


def slab_guards(domain):
    hmin, hmax = domain['h_range']
    h1min = domain['h1_range'][0]
    etamin = domain['eta_range'][0]
    require(F(1, 10)-DELTA0 == F(2, 45) > 0, 'Positive root-wide packing remainder')
    require(F(1, 4)-DELTA0-geometric(5, 2) == F(13, 90) > 0,
            'Each first source label is forced, in root1 where applicable; coincidences contradict the same tail budget')
    gaps = [hmin/5-R0, h1min/5-R0, etamin/5-R0,
            h1min*(F(1, 10)-DELTA0)-2*R0]
    require(min(gaps) == G0 > 0 and gaps[-1] == F(1973, 162000), 'Every first-five slot gap is uniformly positive')
    require(gaps[-1]-G0 == F(373, 324000), 'Strict fourth-slot guard')
    require(R0 < min(hmin/5, h1min/5, etamin/5), 'Best slot differs from all three first source slots')
    require((hmin/5-R0)/5 == A0 and hmax/5 == F(1, 9), 'Uniform m/5 lower and m upper')
    require(F(1, 9)/G0 == C0 > 1, 'Uniform coefficient max(1,m/G)')
    require(R0/5 == F(1, 60000), 'Large-r branch gives actual mass residual')
    # For15, r1<=r. Wrong-root, first-beta and Q losses retain these guards.
    wrong_root = domain['h1_minus_h0_lower']/5-R0
    require(wrong_root == G0 and min(gaps[1:]) >= G0, 'Every non-root1-H15 carrier loses at least r1+g0')
    flat_end, zero_start = (A0-G0)/C0, A0/C0
    require(0 < flat_end < zero_start and gamma_lower(0) == G0
            and gamma_lower(flat_end) == G0 and gamma_lower(zero_start) == 0,
            'Exact breakpoints of the retained mass-residual tradeoff')
    # Verify the defining affine pieces at their endpoints and an interior point.
    for value in (F(0), flat_end/2, flat_end):
        require(gamma_lower(value) == G0, 'Constant branch')
    for value in (flat_end, (flat_end+zero_start)/2, zero_start):
        require(gamma_lower(value) == A0-C0*value, 'Decreasing affine branch')
    for value in (zero_start, 2*zero_start):
        require(gamma_lower(value) == 0, 'Zero branch')
    return {'delta_upper': DELTA0, 'r_split': R0, 'source_slot_gap_lower': G0,
            'four_gap_guards': gaps, 'wrong_root15_gap_guard': wrong_root,
            'm_over5_lower': A0, 'm_upper': F(1, 9), 'residual_coefficient_upper': C0,
            'large_r_mass_residual_lower': F(1, 60000), 'first_label_forcing_margin': F(13, 90),
            'positive_part_breakpoints': [flat_end, zero_start]}


def concentration(faces):
    expected = [[[1], [2], [3, 4, 5], [1], [0], [14]],
                [[2], [2], [3, 4, 5], [2], [0], [13]]]
    require(faces['factor_names'] == ['deficit', 'alpha', 'beta', 'late', 'z']
            and faces['factor_sizes'] == [6, 3, 6, 6, 2], 'Same product source factors')
    require(faces['targets']['K']['maximal_cartesian_zero_boxes'] == expected, 'Both entire K zero boxes')
    for row in faces['targets']['K']['zero_controls']:
        require(row['factors'][1] == 2 and row['factors'][2] in (3, 4, 5)
                and row['factors'][4] == 0, 'Zero set lies inside the common alpha/beta/z event')
    zeta0 = F(25, 27)
    single = (1-zeta0)/4
    require(single == F(1, 54) and 3*single == DELTA0, 'Product concentration forces the broad source-budget slab')
    return {'zero_boxes': expected, 'zeta_lower': zeta0, 'outside_zero_mass_upper': 1-zeta0,
            'individual_p_a_b_upper': single, 'delta_upper': DELTA0,
            'factor_formulas': {'p': '(1-z0)/4', 'a': '(1-alpha2)/4', 'b': '(1-beta345)/4'},
            'justification': 'The zero union is contained in each common factor event, so its product mass cannot exceed any of their three weights.'}


def bounded_heads():
    require(F(1, 45)/G0 == HEAD_FACTOR > 1, 'Bounded-column virtual-capacity coefficient and single omega absorption')
    maxima, witnesses = {4: 0, 5: 0}, {}
    digest, checks = sha256(), 0
    for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
        for slot in range(5):
            values = [head_load(layout, c, slot) for c in range(5)]
            for threshold in (4, 5):
                phi = [max(v-threshold, 0) for v in values]
                maximum = 6-threshold
                require(max(phi) <= maximum and sum(phi) <= maximum,
                        'Pointwise and entire-column bounded six-label hinge')
                checks += 1
                digest.update(json.dumps([layout, slot, threshold, phi], separators=(',', ':')).encode())
                if sum(phi) > maxima[threshold]:
                    maxima[threshold], witnesses[threshold] = sum(phi), {'layout': layout, 'slot': slot, 'column': phi}
    require(checks == 125000 and maxima == {4: 2, 5: 1}, 'Complete head and column inventory')
    return {'original_head_moduli': [1, 3, 9, 5, 15, 45], 'column_checks': checks,
            'all_head_columns_sha256': digest.hexdigest(), 'maximum_column_hinges': maxima,
            'maximizing_witnesses': witnesses,
            'raw_column_integral_uppers': {str(t): F(6-t, 45) for t in (4, 5)},
            'rho_coefficients': {str(t): (6-t)*HEAD_FACTOR for t in (4, 5)},
            'base_rho_coefficient': HEAD_FACTOR,
            'scope': 'The enumeration checks bounded head functions, not actual covering families. The ordinary proof gives the arbitrary-source integral and single shared residual charge.'}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('broad_slot_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source: '+path)
    faces = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/global_control_faces.json'))
    coupling = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/common_deleted_measure_coupling.json'))
    for record in (faces, coupling):
        for path, pin in record['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited dependency')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited source: '+path)
            used[path] = pin
    source = module('broad_slot_source', base/'verify_joint_frontier.py')
    domain = source_domain(source)
    tails = []
    for cut in (1, 3, 8):
        five_prefix = sum(F(1, 5**j) for j in range(2, cut+1))
        seven_prefix = sum(F(6, 5*7**j) for j in range(1, cut+1))
        five_tail, seven_tail = geometric(5, max(2, cut+1)), F(6, 5)*geometric(7, cut+1)
        require(five_prefix+five_tail == F(1, 20) and seven_prefix+seven_tail == F(1, 5), 'Complete5 and7 tails')
        tails.append({'cut': cut, 'five_prefix': five_prefix, 'five_tail': five_tail,
                      'seven_prefix': seven_prefix, 'seven_tail': seven_tail})
    require(geometric(5, 1) == F(1, 4) and geometric(5, 2) == F(1, 20)
            and F(6, 5)*geometric(7, 1) == F(1, 5), 'Whole source and virtual weight budgets')
    guards = slab_guards(domain)
    concentration_record = concentration(faces)
    head = bounded_heads()
    return encode({'schema': 'erdos7-broad-five-slot-tradeoff-v1', 'source_sha256': used,
        'actual_definitions': {'p': 'z-3/4', 'a': '1/4-alpha1', 'b': '1/4-(beta2+beta3+beta4)',
            'Delta': 'p+a+b', 'r': 'min_j(h/5-Lambda(F_j))', 'm': 'Lambda(F_H)=h/5-r',
            'E5': 'h/25-V5(1)', 'E15': 'h1/25-V15(1)', 'omega': '(V-delta)(1)',
            'S0': 'sum_c pi_c D_c(theta)', 'rho': 'S-S0', 'r1': 'h1/5-Lambda(root1 times F_H)'},
        'general_hypotheses': ['Actual first source labels5,15,45 are present, with15 on root1 and45 in a root1 cell.',
            'Their first-five slots P,A,B are pairwise distinct.',
            'r<min(h/5,h1/5,eta_star/5).', 'Every expression dividing byG additionally requiresG>0.'],
        'source_domain': domain, 'complete_tail_checks': tails, 'slab': guards,
        'concentration': concentration_record, 'bounded_head_interface': head,
        'shared_capacity_inequality': 'E5+E15+omega<=rho; these are actual measures and deficits, not independent probability parameters.',
        'single_slot_tradeoff': 'mu(F_J)<=m-[min(g0,A0-c0*(rho-r/5))]_+ whenDelta<=1/18 andr<1/12000.',
        'bounded_head_hypotheses': ['Delta<=1/18 and r<1/12000.',
            'B is the actual six-label test head with moduli1,3,9,5,15,45; missing labels contribute zero.',
            'phi=(B-t)_+ with t=4 or5; all measures and capacity defects are from the same actual source.'],
        'bounded_head_tradeoff': 'mu(phi)<=Lambda((1-(1_H+1_root1H)/5)*phi)-V3(phi)-V9(phi)+(6-t)*(800/397)*(rho-(r+r1)/5), phi=(B-t)_+,t=4or5.',
        'scope': 'Ordinary actual-source theorem on the broad deficit slab, with complete tails and one shared virtual-to-actual loss. It gives conditional slot and bounded-head constraints, not an added old m40 margin, global K improvement, actual covering construction, or Lean verification.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('broad_slot_writer', args.base/'certificate_io.py')
    rendered = json.dumps(result, indent=2)+'\n'
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical broad-slot certificate')
    elif args.write:
        io.write_certificate_text(args.base/CERTIFICATE, rendered)
    elif args.output is not None:
        args.output.write_text(rendered)
    else:
        print(rendered)
    print('PASS: full source-domain guards, complete5/7 tails, broad slab397/36000, concentration25/27,125000 bounded head columns.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
