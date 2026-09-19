#!/usr/bin/env python3
"""Exact constants for the whole K-neighborhood actual-mass residual bound.

The continuum result is proved in note106. This program verifies its
algebra, all 18 carrier coefficients, both affine beta-face bases and the
complete nonshallow cap. It does not infer a continuum bound from samples.
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
CERTIFICATE = 'certificates/source_norms/carrier_mass_residual_bound.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'verify_joint_frontier.py': 'a40fce0a5cb6a713dc8cb569b874d284b8dd66fb3f0a5e48fc2c69cb8fe286fe',
    'frontier/global_control_faces.py': '649e9c395ed07896ccc93064c8634e402e1a277b2a96c06a3688e8b566f85c93',
    'certificates/source_norms/global_control_faces.json': 'd99736841c20977095c5c397c5949dec20960a4ee1afd72a3f926f2e773b8817',
    'frontier/allocated_seven_thresholds.py': 'b467824a30899cd14ab35ab4a1383c4a3848e5c9dcbdaebd6f4074e9a1d8e78d',
    'certificates/source_norms/joint_survival_carriers.json': '9b8b6f5bfabed669cea810b759d2d02f19e47cce1999851dcd031cfa77115a72',
}
ROOT = (0, 0, 1, 1, 1)
CARRIERS = tuple(product((-1, 0, 1), (-1, 0, 1, 2, 3, 4)))
FACE_MASS = F(53, 360)
SIGMA_COEFFICIENT = F(5, 9)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input: '+str(path))
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


def boundS0(sigma):
    """Upper bound on S0 when qK >= 1-sigma and 0 <= sigma < 1/2."""
    sigma = F(sigma)
    require(0 <= sigma < F(1, 2), 'K concentration domain: 0 <= sigma < 1/2')
    return FACE_MASS+SIGMA_COEFFICIENT*sigma


def boundE(sigma, rho):
    """Upper bound on the original positive E <= S = S0+rho."""
    rho = F(rho)
    require(rho >= 0, 'The same actual common-carrier residual is nonnegative')
    return boundS0(sigma)+rho


def weights(carrier):
    root, cell = carrier
    return tuple(int(ROOT[j] == root)+int(j == cell) for j in range(5))


def mirror(carrier):
    root, cell = carrier
    return root, 1-cell if cell in (0, 1) else cell


def nonshallow(d, w):
    return (max(d)/18+sum(w)/36
            +max(sum(w[:2]), sum(w[2:]))/36+max(w)/36+F(1, 72))


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('mass_residual_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    controls = read('certificates/source_norms/global_control_faces.json')
    old = read('certificates/source_norms/joint_survival_carriers.json')
    rows = {row['index']: row for a in old['joint_survival']['row_blocks'] for b in a for row in b}
    source = module('mass_residual_source', base/'verify_joint_frontier.py')
    allocated = module('mass_residual_allocated', base/'frontier/allocated_seven_thresholds.py')
    require(source.ROOT == ROOT and allocated.CARRIERS == CARRIERS
            and tuple(map(tuple, controls['carriers'])) == CARRIERS, 'The same 18 original full and partial carriers')
    carrier_table = []
    for c in CARRIERS:
        w = weights(c)
        require(all(0 <= x <= 2 for x in w), 'Every carrier coefficient is nonnegative')
        require(weights(mirror(c)) == (w[1], w[0], *w[2:]), 'Exact covariance under the root0 cell exchange')
        carrier_table.append({'carrier': c, 'weights': w, 'mirror': mirror(c)})
    require(weights((1, 1)) == (0, 1, 1, 1, 1)
            and weights((1, 0)) == (1, 0, 1, 1, 1), 'Both distinguished carriers have only zero-one coefficients')

    vertices = list(source.vertices())
    face_rows = []
    for row in controls['targets']['K']['zero_controls']:
        index, selected = row['index'], row['factors'][0]-1
        require(selected in (0, 1), 'Only the two full beta-face orientations')
        deficit, alpha, beta, late, z = vertices[index]
        require(deficit == tuple(F(1, 2) if j == selected else F(0) for j in range(5))
                and alpha == (F(0), F(1, 4)) and z == F(3, 4)
                and beta[:2] == (0, 0) and sum(beta[2:]) == F(1, 4)
                and late == tuple(F(1, 72) if j == selected else F(0) for j in range(5)), 'Exact affine beta-face basis')
        d, n, eta, s, D = source.data(vertices[index])
        w = tuple(9*x for x in eta)
        expected = tuple(F(1, 36) if j == selected else F(1, 12) if j < 2 else (F(1, 2)-beta[j])/9 for j in range(5))
        require(n == expected and s == F(1, 4), 'All five affine face masses and the constant total')
        require(d[:2] == (F(3, 4),)*2 and all(F(1, 4) <= x <= F(1, 2) for x in d[2:]),
                'The max-d branch is fixed on the entire beta triangle')
        R = nonshallow(d, w)
        chosen = (1, 1-selected)
        marked = sum(a*b for a, b in zip(weights(chosen), n))
        require(R == F(7, 24) and marked == F(2, 9) and s-(marked+R)/5 == D == FACE_MASS,
                'Constant complete cap, distinguished mass and carrier lower mass')
        conditional = rows[index]['conditional']
        require(len(conditional) == 18, 'Every original partial carrier included')
        masses = []
        for c, inherited in zip(CARRIERS, conditional):
            Dc = s-(sum(a*b for a, b in zip(weights(c), n))+R)/5
            require(tuple(inherited['carrier']) == c and F(inherited['D_c']) == Dc,
                    'The complete carrier formula agrees with46, including absent labels')
            masses.append(Dc)
        face_rows.append({'index': index, 'selected_cell': selected, 'beta': beta, 'n': n,
                          's': s, 'R': R, 'distinguished_carrier': chosen,
                          'distinguished_mass': marked, 'all18_carrier_lower_masses': masses})
    require(len(face_rows) == 6 and {r['selected_cell'] for r in face_rows} == {0, 1}, 'Both full triangle bases')

    # Coefficients of the continuum norm estimate, not sampled sources.
    norm_terms = {'width': F(1), 'z_five_cells': F(5, 4),
                  'alpha_root_multiplicity': F(3, 2), 'beta': F(1, 2)}
    late_term = F(1, 36)
    norm_coefficient = sum(norm_terms.values())/9+late_term
    require(norm_coefficient == F(1, 2), 'The full L1 mass projection coefficient')
    require(F(1, 2)*F(1, 4)/9-F(1, 72) == 0, 'The full source domain implies every n_j >= 0')

    # Every listed line is a universal lower bound a-b*sigma, proved in note106.
    cap_terms = [
        {'term': 'max_d', 'intercept': F(3, 4), 'loss': F(1, 2), 'weight': F(1, 18)},
        {'term': 'sum_w', 'intercept': F(9, 2), 'loss': F(0), 'weight': F(1, 36)},
        {'term': 'rootmax_w', 'intercept': F(3), 'loss': F(1, 2), 'weight': F(1, 36)},
        {'term': 'max_w', 'intercept': F(1), 'loss': F(1, 2), 'weight': F(1, 36)},
        {'term': 'late_tail', 'intercept': F(1, 72), 'loss': F(0), 'weight': F(1)},
    ]
    cap_intercept = sum(r['intercept']*r['weight'] for r in cap_terms)
    cap_loss = sum(r['loss']*r['weight'] for r in cap_terms)
    require((cap_intercept, cap_loss) == (F(7, 24), F(1, 18)), 'All five complete-cap terms paid once')
    for c in ((1, 1), (1, 0)):
        for v in weights(c):
            # A_j is affine and nondecreasing on the entire sigma interval.
            require(F(v, 5) >= 0 and 0 <= 1-F(v, 5) <= 1-F(v, 10) <= 1,
                    'Every norm multiplier A_j = 1-(1-sigma)c_j/5 lies in [0,1]')
    carrier_loss = F(2, 9)/5
    total_loss = norm_coefficient+carrier_loss+cap_loss/5
    require(F(1, 4)-(F(2, 9)+cap_intercept)/5 == FACE_MASS
            and total_loss == SIGMA_COEFFICIENT, 'The entire S0 upper bound has the stated constant and slope')
    require(boundS0(0) == FACE_MASS and boundE(0, F(1, 7)) == FACE_MASS+F(1, 7), 'Consumer interfaces preserve the same additive residual')
    return encode({'schema': 'erdos7-carrier-mass-residual-bound-v1', 'source_sha256': PINS,
        'hypotheses': ['effective actual source', 'qK >= 1-sigma', '0 <= sigma < 1/2',
                       'rho = S-S0 >= 0', '0 < E <= S'],
        'carriers': carrier_table, 'affine_face_bases': face_rows,
        'face_basis_carrier_checks': 6*18, 'mass_projection_terms_before_division_by9': norm_terms,
        'late_projection_coefficient': late_term, 'mass_L1_projection_coefficient': norm_coefficient,
        'complete_cap_lower_terms': cap_terms, 'complete_cap_lower_constant': cap_intercept,
        'complete_cap_lower_loss': cap_loss, 'carrier_weight_loss': carrier_loss,
        'S0_upper_constant': FACE_MASS, 'S0_upper_sigma_coefficient': total_loss,
        'E_upper_rho_coefficient': F(1),
        'scope': 'Ordinary universal inequality on both whole K-face neighborhoods, with arbitrary beta mixtures and all18 carriers. The audit checks exact algebra and affine source bases; the continuum argument is in note106. No maximizing-carrier preservation, actual-family existence, global comparison improvement, unrestricted Erdos7 resolution or Lean verification is claimed.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('mass_residual_output_io', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact whole-neighborhood carrier-mass certificate')
    elif args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: both full K-face neighborhoods; all18 carriers; S0 <= 53/360 + 5*sigma/9; E <= S0 + rho.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
