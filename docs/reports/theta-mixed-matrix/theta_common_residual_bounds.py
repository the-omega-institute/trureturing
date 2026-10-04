"""Whole-space residual enclosure from direct action rows and local Lipschitz bounds."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

import flint
from flint import acb, arb, ctx, fmpq


HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('actual_theta_action', HERE/'theta_action_integral.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


def tail_integral(power, radius):
    return module.bounds.exponential_integral_upper(power, arb.pi(), (2*arb(radius)).exp())


def source_l1(action, radius, cells):
    interior = arb(0)
    for i in range(cells):
        lo, hi = radius*i/cells, radius*(i+1)/cells
        r = arb((lo+hi)/2, arb((hi-lo)/2).upper())
        _, weighted = action.weighted_source(acb(r))
        interior += 4*arb(hi-lo)*abs(weighted).upper()*(r/2).cosh().upper()
    c0, exterior = action.constants[0], arb(0)
    exterior += c0*tail_integral(3, radius)
    for k, c in enumerate(action.a, 1):
        exterior += abs(arb(c))*(action.constants[k]*tail_integral(2+2*k, radius)
                                 +c0*arb(fmpq(1, 4**k))*tail_integral(2, radius))
    total = interior+4*exterior
    if not total.is_finite():
        raise ValueError('Finite whole-space source L1 enclosure required')
    return total.upper()


def exterior_residual_squared(action, radius, l1):
    pi = arb.pi()
    lower_phi_constant = 4*pi*pi-6*pi
    if not lower_phi_constant > 0:
        raise ValueError('Positive original-theta lower envelope required')
    count = len(action.a)+2
    scalar = sum((abs(arb(c))*arb(fmpq(1, 4**k)) for k, c in enumerate(action.a, 1)), arb(0))
    f_squared = tail_integral(4, radius)+scalar**2*tail_integral(2, radius)
    for k, c in enumerate(action.a, 1):
        f_squared += (arb(c)*action.constants[k]/lower_phi_constant)**2*tail_integral(2+4*k, radius)
    f_squared *= 4*action.constants[0]*count
    mass = 4*action.constants[0]*tail_integral(2, radius)
    w_max = sum((abs(arb(c)) for c in action.b), arb(0))
    total = arb(fmpq(3, 4))*f_squared+(arb(fmpq(3, 4))*l1*l1+3*w_max*w_max)*mass
    if not total.is_finite():
        raise ValueError('Finite whole residual squared exterior bound required')
    return total.upper()


def produce(candidate_path, boxes=512, l1_cells=1024):
    ctx.prec = 192
    if boxes < 16 or boxes & (boxes-1) or l1_cells < 16 or l1_cells & (l1_cells-1):
        raise ValueError('Power-of-two box counts at least sixteen required')
    data = json.loads(candidate_path.read_text())
    action = module.Action(data)
    radius = fmpq(5, 2)
    l1 = source_l1(action, radius, l1_cells)
    exterior = exterior_residual_squared(action, radius, l1)
    total = arb(0)
    cells = []
    for i in range(boxes):
        lo, hi = radius*i/boxes, radius*(i+1)/boxes
        midpoint, half_width = (lo+hi)/2, (hi-lo)/2
        r = arb(midpoint, arb(half_width))
        started = time.monotonic()
        value, action_tail = action.value(acb(arb(midpoint)))
        point_error = abs(value-action.witness(acb(arb(midpoint))).real).upper()
        gaps = [module.support.positive_gap((sign*acb(r)).exp()) for sign in (1, -1)]
        gap_lower = min(g.real.lower() for g in gaps)
        if not gap_lower > 0:
            raise ValueError('Strictly positive uniform actual support gap required')
        coth = gap_lower.cosh()/gap_lower.sinh()
        f_max = abs(action.source(acb(r))).upper()
        derivative = abs(action.source_derivative(r)).upper()
        w_derivative = abs(action.witness_derivative(r)).upper()
        # |partial_r a| <= coth(gap_lower) wherever a is active.
        # The positive-part boundary has zero value, hence no boundary charge.
        local_lipschitz = derivative/2+coth*(f_max+l1)/2+w_derivative
        residual_max = point_error+arb(half_width)*local_lipschitz
        phi, _ = action.weighted_source(acb(r))
        density = 4*phi.real*(r/2).cosh()
        if not density.is_finite() or not density.lower() > 0:
            raise ValueError('Positive finite original folded density required')
        contribution = arb(hi-lo)*density.upper()*residual_max.upper()**2
        if not contribution.is_finite():
            raise ValueError('Finite common-residual cell contribution required')
        total += contribution
        cells.append({'index': i, 'midpoint_exact': str(midpoint),
                      'point_residual_abs_upper': module.endpoints(point_error),
                      'full_action_tail_upper': module.endpoints(action_tail),
                      'support_gap_lower': module.endpoints(gap_lower),
                      'source_derivative_abs_upper': module.endpoints(derivative),
                      'residual_lipschitz_upper': module.endpoints(local_lipschitz.upper()),
                      'residual_squared_cell_upper': module.endpoints(contribution.upper())})
        if i % 16 == 0:
            print(json.dumps({'cell': i, 'source_l1_upper': str(l1),
                              'partial_squared_upper': str(total.upper()),
                              'cell_duration_seconds': time.monotonic()-started}), flush=True)
    norm = (total+exterior).sqrt().upper()
    return {'scope': 'Directed whole-space common-source residual upper enclosure, pending independent mathematical review; no original-form sign, Lean, Robin or RH certificate',
            'target': data['target'],
            'candidate_source_sha256': hashlib.sha256(candidate_path.read_bytes()).hexdigest(),
            'producer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'runtime': {'python': sys.version.split()[0], 'python_flint': flint.__version__, 'precision_bits': ctx.prec},
            'radius_exact': str(radius), 'radial_boxes': boxes, 'source_l1_boxes': l1_cells,
            'quadrature_callbacks': action.calls,
            'nonanalytic_or_invalid_boxes_rejected': action.rejections,
            'whole_source_l1_upper': module.endpoints(l1),
            'interior_residual_squared_upper': module.endpoints(total.upper()),
            'exterior_residual_squared_upper': module.endpoints(exterior),
            'whole_residual_norm_upper': module.endpoints(norm),
            'passes_one_over_ten_thousand_upper_target': bool(norm < arb(fmpq(1, 10000))),
            'fixed_n_coefficients_exact': data['n_coefficients_exact_dyadic_rationals'],
            'fixed_w_coefficients_exact': data['w_coefficients_exact_dyadic_rationals'],
            'individually_certified_zero_balls': [str(g) for g in action.gammas],
            'cells': cells,
            'unpaid': ['independent direct-action and whole-space residual mathematical review',
                       'original half-bound and cofinal projected comparison', 'RH and Robin']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--boxes', type=int, default=512)
    parser.add_argument('--l1-cells', type=int, default=1024)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = produce(args.candidate, args.boxes, args.l1_cells)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('whole_residual_norm_upper', 'exterior_residual_squared_upper', 'passes_one_over_ten_thousand_upper_target')}, indent=2))


if __name__ == '__main__':
    main()
