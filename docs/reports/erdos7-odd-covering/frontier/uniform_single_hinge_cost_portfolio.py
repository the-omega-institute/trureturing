#!/usr/bin/env python3
"""The adopted27 single-hinge costs and one affine cost on a whole K radius."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/uniform_single_hinge_cost_portfolio.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/uniform_k_neighborhood_cost.py': '2868fc48d2b02e889402f7c2cbf89cd4236d28a3d575b53cf3cbdf48cd2dd781',
    'frontier/complete_off_face_cost.py': '6ab17509f6946409cef6b431cdfb316cc35c9055d21de93eb2906c723d93e234',
    'frontier/finite_source_face_transport.py': 'aa4099317ddf1b7cca16df4916166b1399d0b6e44cbe6459dde081075db8d332',
    'frontier/shared_budget_affine_tail.py': '0b0a509626dda7f44ecccf56825c2a3027fce2e4269c64a0419e65da3bce1136',
    'frontier/joint_deep_mean_transport.py': 'a63225e637c6e926e80b04822ab8c83b79f8b99d3069b283375838df69ea4534',
    'frontier/broad_weighted_identity_source.py': 'e0a89669a6b8b6ff732391b4c27dddd21bf5517f8a37928120e75955349dd98f',
    'verify_joint_frontier.py': 'a40fce0a5cb6a713dc8cb569b874d284b8dd66fb3f0a5e48fc2c69cb8fe286fe',
    'frontier/uniform_ap_survival_denominator.py': '5d1da05fd2e805761d92bc2b0bdd698df9d463e782f299d0f5696fb73bd2d3a5',
    'certificates/source_norms/whole_face_stop_loss_generator.json': '51aef7270e9f585a5ae3b7d921326358053e2f076f03715f8b8631f820b84ecc',
    'certificates/source_norms/whole_cost_mean_stop_loss.json': 'd535a2f69617536a06655c61a1166813bfd2ce3e17416fc329dcead0ba3201da'}
EXCLUDED = (0, 1, 2, 7, 10, 16, 17, 18, 23, 26, 32, 33, 36)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def calculate(base):
    io = module('single_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    un = module('single_uniform', base/'frontier/uniform_k_neighborhood_cost.py')
    co = module('single_cost', base/'frontier/complete_off_face_cost.py')
    fi = module('single_finite', base/'frontier/finite_source_face_transport.py')
    af = module('single_affine', base/'frontier/shared_budget_affine_tail.py')
    me = module('single_mean', base/'frontier/joint_deep_mean_transport.py')
    ca = module('single_capacity', base/'frontier/broad_weighted_identity_source.py')
    de = module('single_denominator', base/'frontier/uniform_ap_survival_denominator.py')
    so = module('single_source', base/'verify_joint_frontier.py')
    face = co.face_case(fi, so)
    record = fi.prepare({2: F(1)})
    old = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/whole_face_stop_loss_generator.json'))
    adopted = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/whole_cost_mean_stop_loss.json'))
    indices = tuple(i for i in range(41) if i not in EXCLUDED)
    require(len(indices) == 28 and indices[-1] == 40, 'Exactly27 single-hinge rows and the one affine row')
    results = []
    for delta, rho in ((F(0), F(0)), (F(1, 10000), F(1, 100000))):
        par = un.parameters(delta, rho)
        upper_point, _ = un.enlarged_point(face['point'], par)
        rows = un.mean_rows(me, record, face, par)
        vertices = [un.exhaustive_vertex(co, fi, ca, record, face, upper_point, par, rows, q)
                    for q in fi.defect_vertices(par['gap'], par['gap'], rho)]
        if rho == delta == 0:
            tail = de.exact_zero_tail(af, record, par)
        else:
            errors = (par['kbar']*rho, rho+delta/240, rho, rho)
            cuts = tuple(un.crossing(p, start, H, error)
                         for p, start, H, error in zip((3, 5, 5, 5), (3, 2, 2, 2), par['H'], errors))
            tail = un.fixed_tail(af, record, par, cuts)
        H2 = un.apply_support(record, par, tail, vertices)
        H1 = de.uniform_H1(par)
        mass = F(53, 360)+5*delta/9+rho
        costs = []
        for i in indices:
            row = old['linear_cost_updates'][i]
            expansion = row['expansion']
            at_one, a1 = F(expansion['at_one']), F(expansion['first_difference'])
            curvature = {int(k): F(v) for k, v in expansion['curvatures'].items() if F(v)}
            if i == 40:
                require(at_one == a1 == 1 and not curvature, 'The exact original affine cost A')
            else:
                require(at_one == 0 and a1 >= 0 and tuple(curvature) == (2,) and curvature[2] > 0,
                        'One positive second hinge, no omitted affine or curvature term')
            a2 = curvature.get(2, F(0))
            face_value = at_one*F(53, 360)+a1*F(443, 900)+a2*F(3869, 10500)
            require(face_value == F(adopted['improved_cost_bounds'][i]) == F(expansion['cost_upper']),
                    'This is the exact adopted98 cost, not the unadopted109 combined objective')
            upper = at_one*mass+a1*H1['upper']+a2*H2['upper']
            costs.append({'index': i, 'name': row['name'], 'tuple': row['tuple'],
                          'weight': F(adopted['cost_weights'][i]),
                          'at_one': at_one, 'first_difference': a1, 'second_curvature': a2,
                          'face_upper': face_value, 'uniform_upper': upper, 'uniform_excess': upper-face_value})
        weighted = sum(row['weight']*row['uniform_upper'] for row in costs)
        coefficients = {name: sum(row['weight']*row[key] for row in costs)
                        for name, key in (('mass', 'at_one'), ('H1', 'first_difference'), ('H2', 'second_curvature'))}
        require(weighted == coefficients['mass']*mass+coefficients['H1']*H1['upper']+coefficients['H2']*H2['upper'],
                'The single scalar profile pays all original cost weights once')
        if not delta and not rho:
            require(H2['upper'] == F(3869, 10500) and all(row['uniform_excess'] == 0 for row in costs),
                    'Exact zero-radius recovery of every adopted controller')
        results.append({'parameters': par, 'H1': H1, 'H2': H2, 'H2_exhaustive_vertices': vertices,
                        'mass_upper': mass, 'weighted_coefficients': coefficients, 'cost_results': costs,
                        'weighted_upper': weighted,
                        'weighted_excess': sum(row['weight']*row['uniform_excess'] for row in costs)})
        print('Uniform H2 '+str(H2['upper'])+';28-cost weighted upper '+str(float(weighted)), flush=True)
    return un.encode({'schema': 'erdos7-uniform-single-hinge-cost-portfolio-v1',
                      'source_sha256': PINS, 'indices': indices, 'radii': results,
                      'original_head_evaluations': sum(v['original_head_evaluations'] for r in results for v in r['H2_exhaustive_vertices']),
                      'rational_comparisons': sum(v['rational_comparisons'] for r in results for v in r['H2_exhaustive_vertices']),
                      'scope': 'Ordinary continuum bound for exactly27 adopted98 single-second-hinge costs and the original affine cost, uniformly on134 actual K rectangle. Each original test keeps independent residues and every infinite tail. Uses139 complete H1 and134 fixed supports for H2, with exact zero-radius recovery. No new global K, Lean verification or unrestricted Erdos7 conclusion.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('single_write', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact single-hinge portfolio certificate')
    print('PASS: all28 adopted controllers, one uniform complete H1/H2 profile and exact face recovery.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
