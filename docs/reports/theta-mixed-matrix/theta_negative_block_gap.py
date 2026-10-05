"""Actual negative-edge block minorant on an existing FIB interval tiling."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

import flint
import numpy as np
from flint import acb, arb, arb_mat, ctx, fmpq


def load(path):
    spec = importlib.util.spec_from_file_location('actual_theta_block_supplier', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def add(a, b):
    return a[0]+b[0], a[1]+b[1]


def mul(a, b):
    # Exact existing ring relation phi^2=phi+1.
    return a[0]*b[0]+a[1]*b[1], a[0]*b[1]+a[1]*b[0]+a[1]*b[1]


def at(pair, phi):
    return arb(pair[0])+arb(pair[1])*phi


def endpoint(v):
    if not v.is_finite():
        raise ValueError('Finite directed block value required')
    return {'display': str(v),
            'lower_dyadic': [str(x) for x in v.lower().man_exp()],
            'upper_dyadic': [str(x) for x in v.upper().man_exp()]}


def partition(depth, radius, phi):
    if not isinstance(depth, int) or not 1 <= depth <= 4:
        raise ValueError('Use a bounded existing FIB tiling depth1..4')
    # Existing legal windows, in low-to-high address order.
    increments = {'null': (0, 0), '2': (1, 0), '3': (1, -1),
                  '2 5': (3, -1), '5': (2, -1)}
    graph = {0: [('null', 0), ('2', 0), ('3', 0), ('2 5', 1), ('5', 1)],
             1: [('null', 0), ('3', 0), ('5', 1)]}
    leaves = [((0, 0), (1, 0), 0, [])]
    for _ in range(depth):
        leaves = [(add(offset, mul(scale, increments[label])), mul(scale, (3, -2)),
                   next_state, address+[label])
                  for offset, scale, state, address in leaves
                  for label, next_state in graph[state]]
    transform = (2*radius, -radius)
    result = []
    for offset, scale, state, address in leaves:
        left = add(offset, mul(scale, (-1, 0)))
        right = add(offset, mul(scale, (0, 1) if state == 0 else (-1, 1)))
        if depth % 2:
            left, right = right, left
        left = mul(transform, add(left, (1, 0)))
        right = mul(transform, add(right, (1, 0)))
        result.append((left, right, address, state))
    result.sort(key=lambda cell: float(at(cell[0], phi).mid()))
    if result[0][0] != (0, 0) or result[-1][1] != (radius, 0):
        raise ValueError('Exact complete physical endpoint coverage required')
    for i, (left, right, _, _) in enumerate(result):
        if not at(right, phi)-at(left, phi) > 0:
            raise ValueError('Strictly positive true FIB interval width required')
        if i and result[i-1][1] != left:
            raise ValueError('Exact FIB seam adjacency required')
    return result


def conductance(distance, left, right):
    if not distance > 0:
        return arb(0)
    psi = (-distance/2).exp()/(1-(-2*distance).exp())
    value = 1-psi/(2*(left/2).cosh()*(right/2).cosh())
    if not value.is_finite():
        raise ValueError('Finite actual conductance minorant required')
    return max(arb(0), value.lower())


def produce(depth=2, target=fmpq(1, 100)):
    if not fmpq(0) < target < fmpq(1, 2):
        raise ValueError('Positive target below the ambient one-half upper bound required')
    ctx.prec = 192
    canonical = Path.cwd()/'docs/reports/theta-mixed-matrix'
    supplier_path = canonical/'theta_direct_action.py'
    supplier = load(supplier_path)
    radius = fmpq(3, 2)
    phi = (1+arb(5).sqrt())/2
    cells = partition(depth, radius, phi)
    bounds = [(at(lo, phi), at(hi, phi)) for lo, hi, _, _ in cells]
    masses = []
    callbacks, rejected = 0, 0
    def density(z, analytic):
        nonlocal callbacks, rejected
        callbacks += 1
        try:
            jets, factor = supplier.theta_jets(z, order=0)
            value = 4*factor*jets[0]*(z/2).cosh()
            if not value.is_finite():
                raise ValueError('Nonfinite actual folded density')
            return value
        except ValueError:
            rejected += 1
            return acb('nan')
    for i, (left, right) in enumerate(bounds):
        mass = acb.integral(density, acb(left), acb(right),
                            abs_tol=arb('1e-50'), rel_tol=arb('1e-48'),
                            eval_limit=20000, depth_limit=30).real
        if not mass.is_finite() or not mass.lower() > 0:
            raise ValueError('Strictly positive complete cell probability required')
        masses.append(mass)
        if i % 16 == 0:
            print(json.dumps({'cell': i, 'mass': str(mass)}), flush=True)
    exterior = 1-sum(masses, arb(0))
    if not exterior.is_finite() or not exterior.lower() > 0:
        raise ValueError('Strictly positive complete outside probability required')
    masses.append(exterior)
    bounds.append((arb(radius), None))
    size = len(masses)
    W = arb_mat(size, size)
    for i, (lo_i, hi_i) in enumerate(bounds):
        for j in range(i, size):
            lo_j, hi_j = bounds[j]
            left, right = lo_i.lower(), lo_j.lower()
            if not left >= 0 or not right >= 0:
                raise ValueError('Nonnegative actual radial minimum required')
            opposite = conductance(left+right, left, right)
            distance = max(arb(0), (lo_j-hi_i).lower()) if hi_i is not None else arb(0)
            same = conductance(distance, left, right)
            W[i, j] = W[j, i] = (opposite+same).lower()
    degrees = [sum((W[i, j]*masses[j] for j in range(size)), arb(0))/4 for i in range(size)]
    degree_lower = min(v.lower() for v in degrees)
    roots = [m.sqrt() for m in masses]
    L = arb_mat(size, size)
    for i in range(size):
        for j in range(size):
            L[i, j] = -W[i, j]*roots[i]*roots[j]/4
        L[i, i] += degrees[i]
    # A=L-cI+uu*, with actual ||u||=1, certifies L>=c on u-perp.
    A = arb_mat(size, size)
    for i in range(size):
        for j in range(size):
            A[i, j] = L[i, j]+roots[i]*roots[j]
        A[i, i] -= arb(target)
    center = np.array([[float(A[i, j].mid()) for j in range(size)] for i in range(size)])
    if not np.all(np.isfinite(center)):
        raise ValueError('Finite matrix acquisition midpoint required')
    approximate_eigen_min = float(np.linalg.eigvalsh(center)[0])
    chol = np.linalg.cholesky(center)
    P = arb_mat(size, size)
    for i in range(size):
        for j in range(i+1):
            P[i, j] = arb(fmpq(*float(chol[i, j]).as_integer_ratio()))
        if not P[i, i] > 0:
            raise ValueError('Positive point preconditioner diagonal required')
    inverse = P.solve(arb_mat(np.eye(size).astype(int).tolist()))
    R = inverse*A*inverse.transpose()
    margins = []
    for i in range(size):
        margin = R[i, i].lower()-sum((abs(R[i, j]).upper() for j in range(size) if j != i), arb(0))
        if not margin.is_finite():
            raise ValueError('Finite directed congruence margin required')
        margins.append(margin.lower())
    minimum_margin = min(margins)
    return {
        'scope': 'Conditional directed whole-space even negative-edge block minorant; no D/half-slack, original-form sign, Lean, Robin or RH certificate',
        'runtime': {'python': sys.version.split()[0], 'python_flint': flint.__version__, 'numpy': np.__version__, 'precision_bits': ctx.prec},
        'producer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'theta_supplier_sha256': hashlib.sha256(supplier_path.read_bytes()).hexdigest(),
        'derivative_supplier_sha256': hashlib.sha256((canonical/'derivative_bandwidth.py').read_bytes()).hexdigest(),
        'fib_depth': depth, 'physical_radius_exact': str(radius),
        'finite_cell_count': len(cells), 'complete_cell_count': size,
        'target_constant_exact': str(target),
        'density_callbacks': callbacks, 'invalid_density_boxes_rejected': rejected,
        'complete_mass_sum_interval': endpoint(sum(masses, arb(0))),
        'full_outside_mass_interval': endpoint(exterior),
        'within_cell_degree_lower': endpoint(degree_lower),
        'mean_block_gershgorin_margin_lower': endpoint(minimum_margin),
        'uncertified_rank_lifted_midpoint_eigen_min': approximate_eigen_min,
        'passes_whole_negative_edge_target': bool(degree_lower >= arb(target) and minimum_margin > 0),
        'cells': [{'index': i, 'address': addr, 'next_state': state,
                   'left_phi_coefficients': [str(q) for q in lo],
                   'right_phi_coefficients': [str(q) for q in hi],
                   'mass_interval': endpoint(masses[i]), 'degree_interval': endpoint(degrees[i])}
                  for i, (lo, hi, addr, state) in enumerate(cells)],
        'outside_degree_interval': endpoint(degrees[-1]),
        'conductance_lower_matrix': [[endpoint(W[i, j]) for j in range(size)] for i in range(size)],
        'point_preconditioner_lower_triangle': [[str(fmpq(*float(chol[i, j]).as_integer_ratio())) for j in range(i+1)] for i in range(size)],
        'congruence_margins_lower': [endpoint(m) for m in margins],
        'unpaid': ['Lean certification of this numerical/model interface', 'original half-bound and cofinal comparison', 'RH and Robin'],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--depth', type=int, default=2)
    parser.add_argument('--target', default='1/100')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = produce(args.depth, fmpq(args.target))
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('within_cell_degree_lower', 'mean_block_gershgorin_margin_lower', 'passes_whole_negative_edge_target')}, indent=2))


if __name__ == '__main__':
    main()
