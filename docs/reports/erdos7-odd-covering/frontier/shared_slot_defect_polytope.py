#!/usr/bin/env python3
"""Actual shared5/15 defect constraints and a stronger concentrated packing gap."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import combinations
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/shared_slot_defect_polytope.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/broad_five_slot_tradeoff.py': 'dba48afdad4ee19ec51ba02be78188b7301767fb01a8a9d0de2b7d12758f4fbd',
    'certificates/source_norms/broad_five_slot_tradeoff.json': '6bb50bb6265b7fa37549441bdf0bb530cb4e9dd30764e4f84b102dfd3a252462',
    'frontier/carrier_mass_residual_bound.py': '751484c1029980b93a5fc4bb7f6990108d40789f06b3b88723311f901cc48b7a',
    'certificates/source_norms/carrier_mass_residual_bound.json': '1ce320c2283c37f17c7c5fa09bcbc0692b67067f3296038c2034ded4eda3ac4b',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source: '+str(path))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def actual_gaps(h0, h1, eta_first_beta, Delta, r, r1):
    """Requires the actual source/first-label geometry proved in the note.

    The numeric guards make every displayed gap positive. They do not
    assert realization of arbitrary parameter tuples as actual sources.
    """
    h0, h1, eta, Delta, r, r1 = map(F, (h0, h1, eta_first_beta, Delta, r, r1))
    require(min(h0, h1, eta) > 0 and eta <= h1 and 0 <= Delta <= F(1, 18)
            and 0 <= r1 <= r, 'Actual positive source masses and broad-slab domain')
    base = h1*(F(1, 10)-Delta)
    five = ((h0+h1)/5-r, h1/5-r, eta/5-r, base-r-r1)
    fifteen = (h1/5-r1, (h1-h0)/5-r1, eta/5-r1, base-2*r1)
    require(min(five+fifteen) > 0, 'The actual best slot and root1 carrier are separated')
    result = {'five_guards': five, 'fifteen_guards': fifteen,
              'G5': min(five), 'G15': min(fifteen)}
    if h1-h0 >= eta:
        g = min(eta/5-r, base-r-r1)
        require(result['G5'] == g and result['G15'] == g+r-r1,
                'One strengthened gap and the retained root0 best-slot loss')
        result['shared_gap'] = g
    return result


def concentrated_guards(delta, rcut):
    """Uniform actual-source guards on qK>=1-delta, 0<=r<=rcut."""
    delta, rcut = F(delta), F(rcut)
    require(0 <= delta <= F(2, 27) and rcut >= 0, 'Concentration implies the broad source-budget slab')
    h1 = F(1, 3)-delta/18
    eta = F(1, 9)-delta/18
    h0 = F(1, 6)+delta/18
    Delta = 3*delta/4
    guards = {'pure5': F(1, 10)-rcut, 'alpha': h1/5-rcut,
              'beta': eta/5-rcut, 'remaining': h1*(F(1, 10)-Delta)-2*rcut}
    gap = min(guards.values())
    require(gap > 0 and h1-h0 > F(1, 9) and F(1, 4)-Delta-F(1, 20) > 0,
            'All first labels, distinct slots, root dominance and division guards')
    return {'delta': delta, 'r_upper_inclusive': rcut, 'Delta_upper': Delta,
            'root1_total_deficit_upper': delta/2, 'h1_lower': h1,
            'eta_first_beta_lower': eta, 'h0_upper': h0,
            'root_mass_difference_lower': h1-h0,
            'first_label_forcing_margin': F(1, 4)-Delta-F(1, 20),
            'four_gap_guards': guards, 'G_lower': gap,
            'best_slot_credit_lower': F(1, 50)-rcut/5}


def defect_polygon_vertices(G5, G15, residual):
    """Exact vertices of [0,1/5]^2 intersect {G5*q5+G15*q15<=residual}."""
    G5, G15, residual = map(F, (G5, G15, residual))
    require(G5 > 0 and G15 > 0 and residual >= 0, 'Positive certified gaps and a nonnegative shared budget')
    lines = [(F(1), F(0), F(0)), (F(1), F(0), F(1, 5)),
             (F(0), F(1), F(0)), (F(0), F(1), F(1, 5)), (G5, G15, residual)]
    vertices = set()
    for (a, b, c), (d, e, f) in combinations(lines, 2):
        det = a*e-b*d
        if det == 0:
            continue
        x, y = (c*e-b*f)/det, (a*f-c*d)/det
        if 0 <= x <= F(1, 5) and 0 <= y <= F(1, 5) and G5*x+G15*y <= residual:
            vertices.add((x, y))
    require(vertices, 'The shared defect polygon contains zero')
    return tuple(sorted(vertices))


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('slot_polytope_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    broad = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/broad_five_slot_tradeoff.json'))
    mass = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/carrier_mass_residual_bound.json'))
    for prior in (broad, mass):
        for path, pin in prior['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited source')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned inherited source: '+path)
            used[path] = pin
    g0, r0, Delta0 = F(397, 36000), F(1, 12000), F(1, 18)
    broad_guards = [F(1, 10)-r0, F(1, 18)-r0, F(1, 90)-r0,
                    F(5, 18)*(F(1, 10)-Delta0)-2*r0]
    require(min(broad_guards) == g0 == F(broad['slab']['source_slot_gap_lower'])
            and broad_guards[-1]-g0 == F(373, 324000), 'The original broad small-r constant is valid on its stated branch')
    # The shared-deficit simplex: selected root0 deficit >=(1-sigma)/2,
    # and total deficit <=1/2.  Affine extrema give these exact bounds.
    affine_checks = []
    for sigma in (F(0), F(1, 27), F(2, 27), F(1, 2)):
        lower_root0 = (1-sigma)/2
        max_root1 = F(1, 2)-lower_root0
        h1 = F(1, 3)-max_root1/9
        h0 = F(2, 9)-lower_root0/9
        require(max_root1 == sigma/2 and h1 == F(1, 3)-sigma/18
                and h0 == F(1, 6)+sigma/18 and h1-h0 == F(1, 6)-sigma/9,
                'Exact consequences of one shared source deficit budget')
        affine_checks.append({'sigma': sigma, 'root1_deficit_upper': max_root1,
                              'h1_lower': h1, 'h0_upper': h0, 'root_difference_lower': h1-h0})
    guards = concentrated_guards(F(1, 27), F(1, 520))
    require(guards['G_lower'] == F(2513, 126360)
            and guards['G_lower']-F(7499, 379080) == F(1, 9477),
            'The complete original103/107 rectangle has a strictly stronger uniform gap')
    conditional = actual_gaps(F(1, 6), F(1, 3), F(1, 9), F(0), F(1, 1000), F(1, 2000))
    require(conditional['G15']-conditional['G5'] == F(1, 2000), 'The retained root0 loss makes the15 gap stronger')
    polygon_checks = []
    G5, G15 = conditional['G5'], conditional['G15']
    for residual in (F(0), G5/10, G5/5, (G5+G15)/5, (G5+G15)/5+F(1, 1000)):
        vertices = defect_polygon_vertices(G5, G15, residual)
        require(all(0 <= x <= F(1, 5) and 0 <= y <= F(1, 5)
                    and G5*x+G15*y <= residual for x, y in vertices), 'Every exact clipping vertex is feasible')
        polygon_checks.append({'residual': residual, 'vertices': vertices,
                               'maximum_omega_at_vertices': [residual-G5*x-G15*y for x, y in vertices]})
    # Actual effective9 raw source with no5/15/45 source restriction.
    # Two forbidden cofactor5 labels use one non-H slot; all others absent.
    h = F(5, 9)
    virtual_mass = (F(6, 35)+F(6, 245))*h/5
    E5 = h/25-virtual_mass
    require(E5 == F(1, 2205) < g0/5, 'A positive uniform wrong-slot gap fails outside the source-packing branch')
    require((F(mass['S0_upper_constant']), F(mass['S0_upper_sigma_coefficient']), F(mass['E_upper_rho_coefficient']))
            == (F(53, 360), F(5, 9), F(1)), 'The actual denominator retains the same rho with coefficient one')
    raw_cap_upper = F(1, 18)+F(5, 36)+F(3, 36)+F(1, 36)+F(1, 72)
    require(raw_cap_upper == F(23, 72) and (F(4, 9)+raw_cap_upper)/5 == F(11, 72),
            'Complete actual carrier capacity has a global finite upper bound')
    return {'schema': 'erdos7-shared-slot-defect-polytope-v1', 'source_sha256': used,
            'broad_small_r': {'Delta_upper': Delta0, 'r_strict_upper': r0, 'G_lower': g0,
                              'four_gap_guards': broad_guards, 'wrong_root15_gap_lower': g0},
            'shared_deficit_affine_checks': affine_checks, 'concentrated_rectangle': guards,
            'improvement_over103_gap': F(1, 9477),
            'global_actual_residual_upper': F(11, 72),
            'shared_budget': 'G5*q5+G15*q15+omega <= rho-(r+r1)/5; 0<=q5,q15<=1/5; omega>=0.',
            'concentrated_shared_budget': 'Gbar*(q5+q15)+(r-r1)*q15+omega <= rho-(r+r1)/5, Gbar=min(eta_L/5-r,h1*(1/10-Delta)-r-r1)>0.',
            'conditional_gap_example': conditional, 'polygon_checks': polygon_checks,
            'stronger_Q_caps': {'root1': 'eta_l*min(1/5,1/10+Delta+r1/h1)',
                                'root0': 'eta_l*min(1/5,3/20+Delta+min(r/h,r1/h1,(r-r1)/h0))'},
            'outside_branch_counterexample': {'eta': [F(1, 9)]*5, 'Delta': F(3, 4), 'r': F(0),
                'present_cofactor5_seven_depths': [1, 2], 'q5': F(1, 5), 'E5': E5,
                'invalid_global_g0_charge': g0/5},
            'scope': 'Ordinary necessary constraints on actual shared source and deletion defects, not a realization theorem for the outer polytope. The stronger concentrated rectangle keeps all103/107 source guards and permits their original inclusive r cutoff. The broad g0 is not asserted outside its branch. No global K improvement, Lean verification or unrestricted Erdos7 resolution is claimed by this interface alone.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('slot_polytope_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact actual-defect and concentrated-packing certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: shared actual5/15 budget, broad397/36000 guards, stronger concentrated gap2513/126360 and exact defect vertices.')


if __name__ == '__main__':
    main()
