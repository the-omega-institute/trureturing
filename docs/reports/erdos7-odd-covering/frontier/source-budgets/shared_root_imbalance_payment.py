#!/usr/bin/env python3
"""One root-imbalance charge reduces the actual deep-capacity penalty.

All root0 labels share one total mass coefficient. The source bridge,
independent layouts, complete infinite tails and one residual are those
of the tied-root theorem; only its deep-capacity coefficient decreases.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/shared_root_imbalance_payment.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/cover-geometry/tied_root_deep_payment.py': 'c2bf22b6d9ebb330574b0b0d0ed632583b6764f90d45a6ab9f784a926746b60c',
    'certificates/source_norms/cover-geometry/tied_root_deep_payment.json': '20095a3abe10441d0d5ae746df8beb246f4adbf7554ac6e46940fec3f86bfba2',
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


def penalty_coefficients(vmin, vmax):
    vmin, vmax = F(vmin), F(vmax)
    require(0 <= vmin <= vmax, 'Ordered nonnegative low increments')
    missing, root1 = F(36, 125)*vmax, F(36, 25)*(vmax-vmin)
    kappa = max(missing, root1)
    marked = max(vmax, kappa)
    require(marked == max(vmax, root1), 'The union coefficient dominates the missing-mass coefficient')
    return {'missing_mass_penalty': missing, 'root1_penalty': root1,
            'deep_capacity_penalty': kappa, 'marked_base_penalty': marked}


def uniform_coefficients(cost_rows, delta, rcut):
    """Inclusive r cutoff; lower g, reduced upper P and unchanged Q."""
    delta, rcut = F(delta), F(rcut)
    require(0 <= delta <= F(2, 27) and rcut >= 0, 'The concentrated region lies in the broad source slab')
    h1, eta_min = F(1, 3)-delta/6, F(1, 9)-delta/18
    guards = (F(1, 10)-rcut, h1/5-rcut, eta_min/5-rcut,
              h1*(F(1, 10)-3*delta/4)-2*rcut)
    gap = min(guards)
    require(gap > 0 and rcut < min(F(1, 10), h1/5, eta_min/5), 'All general source-packing and first-label guards')
    wdeep, best_credit = (1-delta)/5, F(1, 50)-rcut/5
    credit = min(wdeep*gap, best_credit)
    require(credit > 0, 'Uniform positive marked credit')
    rows = []
    for row in cost_rows:
        vmin, vmax, C = map(F, (row['vmin'], row['vmax'], row['barrier']))
        penalties = penalty_coefficients(vmin, vmax)
        require(C >= 3*vmax >= penalties['deep_capacity_penalty'], 'The refined bridge strengthens the original one')
        count = row['selected_cofactor_count']
        sigma = sum(F(1, 5*3**a) for a in range(3, count+1))
        if 'selected_deep_coefficient' in row:
            require(sigma == F(row['selected_deep_coefficient']), 'Unchanged complete selected label family')
        P = max(penalties['marked_base_penalty'], vmin/(9*gap))
        Pold, Q = max(C, vmin/(9*gap)), sigma*C
        require(P <= Pold and P >= max(vmax, penalties['deep_capacity_penalty']), 'One reduced penalty pays the union and deep defects')
        rows.append({'index': row['index'], 'name': row['name'], 'tuple': row['tuple'],
                     'weight': F(row['weight']), 'barrier': C, 'vmin': vmin, 'vmax': vmax,
                     'selected_cofactor_count': count, 'selected_deep_coefficient': sigma,
                     **penalties, 'g': vmin*credit, 'P': P, 'Q': Q,
                     'escape_charge_coefficient': Q/4,
                     'previous_P': Pold, 'penalty_reduction': Pold-P})
    return {'delta': delta, 'r_upper_inclusive': rcut, 'four_gap_guards': guards,
            'G_lower': gap, 'remaining_hole_coefficient': wdeep,
            'best_slot_credit_lower': best_credit, 'uniform_source_credit': credit,
            'cost_rows': rows,
            'weighted_g_sum': sum(row['weight']*row['g'] for row in rows),
            'weighted_P_sum': sum(row['weight']*row['P'] for row in rows),
            'weighted_Q_sum': sum(row['weight']*row['Q'] for row in rows),
            'strictly_reduced_penalty_count': sum(row['penalty_reduction'] > 0 for row in rows),
            'comparison': 'd_i>=m_i_old+[g_i-P_i*(rho-r/5)-Q_i*chi]_+; all root0 labels use one sigma_D*C*chi charge, chi<=sigma_escape/4.'}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('shared_root_io', base/'certificate_io.py')
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source: '+path)
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/cover-geometry/tied_root_deep_payment.json'))
    for path, pin in previous['source_sha256'].items():
        require(path not in used or used[path] == pin, 'Consistent inherited input')
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited source: '+path)
        used[path] = pin
    generic = module('shared_root_previous', base/'frontier/cover-geometry/tied_root_deep_payment.py')
    require(encode(generic.calculate(base)) == previous, 'All generic nonnested comparisons, original cost floors and complete tails revalidated')
    adapted = []
    for row in previous['cost_rows']:
        vmin, vmax, C = map(F, (row['vmin'], row['vmax'], row['barrier']))
        penalties = penalty_coefficients(vmin, vmax)
        require(penalties['missing_mass_penalty']*F(25, 36) == vmax/5,
                'Exact missing-mass payment against d_star>=25/36')
        require(penalties['root1_penalty']*F(5, 36) == (vmax-vmin)/5,
                'Exact root1 derivative-range payment against the root gap')
        require(penalties['deep_capacity_penalty'] <= C and penalties['marked_base_penalty'] <= C,
                'The old C penalty is replaced by a no-larger coefficient')
        sigma = F(row['selected_deep_coefficient'])
        tail = F(row['complete_remaining_mass_tail'])
        require(sigma+tail == F(1, 90), 'Every unselected pure3 depth remains in the original complete mass allocation')
        adapted.append({**row, **encode(penalties), 'root_imbalance_coefficient': sigma*C,
                        'root0_partition_mass_coefficient': sigma})
    require(len(adapted) == 46, 'The complete original cost inventory')
    default = uniform_coefficients(adapted, F(1, 44), F(1, 840))
    old_default = generic.uniform_coefficients(previous['cost_rows'], F(1, 44), F(1, 840))
    for new, old in zip(default['cost_rows'], old_default['cost_rows']):
        require(new['g'] == old['g'] and new['Q'] == old['Q'] and new['P'] <= old['P'],
                'Exactly the same positive credit and root imbalance, with a reduced residual coefficient')
    return {'schema': 'erdos7-shared-root-imbalance-payment-v1', 'source_sha256': used,
            'cost_rows': adapted,
            'generic_tied_root_layout_pairs': previous['generic_tied_root']['layout_pair_count'],
            'original_cost_layout_pair_checks': previous['total_original_layout_pair_checks'],
            'source_checks_reused': previous['source_checks_reused'],
            'deep_bridge': 'Q_D-P_D>=-kappa*E_D-sigma_D*C*chi',
            'capacity_penalty': 'kappa=max(36*vmax/125,36*(vmax-vmin)/25)',
            'root0_partition': 'Sum of u_e*eta(A) over BOTH root0 cells is at most sigma_D, not two copies of sigma_D.',
            'shared_budget': 'E_D+(E5-r/5)+omega<=rho-r/5',
            'general_residual_coefficient': 'P=max(vmax,36*(vmax-vmin)/25,vmin*m/G)',
            'uniform_default': default,
            'scope': 'Ordinary refinement of the generic deep-capacity bridge on Delta<=1/18. Uniform positive credit additionally requires the concentration and packing guards. Same actual measures, independent original labels, complete infinite tails, curvature and one residual. No new global K, optimality, Lean or unrestricted Erdos7 claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('shared_root_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact shared-root imbalance certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: all46 costs use one root0 imbalance charge, a smaller deep-capacity coefficient and the same actual residual.')
    print('Default strictly reduced P count: '+str(result['uniform_default']['strictly_reduced_penalty_count'])+'; no new global K is inferred.')


if __name__ == '__main__':
    main()
