"""Joint original-metric Gram acquisition for ideal J4 midpoint columns."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

import flint
from flint import acb, arb, ctx, fmpq


HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('profile_metric_action', HERE/'theta_action_integral.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class ProfileAction(module.Action):
    """B of G(|x|-R)/v0; B annihilates its removed constant exactly."""

    def __init__(self, center):
        super().__init__({'n_coefficients_exact_dyadic_rationals': [],
                          'w_coefficients_exact_dyadic_rationals': []})
        self.center = fmpq(center)
        if not self.center < 59:
            raise ValueError('This supplier covers the left J4 formula, R<R0=59')

    def radial(self, z, radial_sign=None):
        z = acb(z)
        if radial_sign in (1, -1):
            radial = radial_sign*z
        elif radial_sign == 0:
            raise ValueError('A definite original integration-piece chart is required')
        elif z.real >= 0:
            radial = z
        elif z.real <= 0:
            radial = -z
        else:
            raise ValueError('Source box needs one radial chart')
        if not radial.real > arb(fmpq(-1, 8)):
            raise ValueError('Original theta overlap chart required')
        return radial

    def profile(self, radial):
        y = radial-acb(self.center)
        return (acb(fmpq(5, 2))*y-acb(arb.pi()/2)*(2*y).exp()).exp()

    def weighted_source(self, z, radial_sign=None):
        radial = self.radial(z, radial_sign)
        jets, factor = module.support.theta_jets(radial, order=0)
        slow = jets[0]/(2*(radial/2).cosh())
        if not slow.real > 0:
            raise ValueError('Positive-real slow theta square-root chart required')
        half_factor = (acb(fmpq(5, 4))*radial-acb(arb.pi()/2)*(2*radial).exp()).exp()
        return factor*jets[0], half_factor*slow.sqrt()*self.profile(radial)

    def weighted_source_on_piece(self, z, radial_sign):
        return self.weighted_source(z, radial_sign)

    def source(self, z, radial_sign=None):
        radial = self.radial(z, radial_sign)
        jets, _ = module.support.theta_jets(radial, order=0)
        slow = 2*(radial/2).cosh()*jets[0]
        if not slow.real > 0:
            raise ValueError('Positive-real slow source denominator required')
        # Cancel the two super-exponential factors before interval evaluation.
        growth = (acb(arb.pi()/2)*(1-(-2*acb(self.center)).exp())*(2*radial).exp()
                  +acb(fmpq(5, 4))*radial-acb(fmpq(5, 2))*acb(self.center))
        return growth.exp()/slow.sqrt()

    def source_derivative(self, r):
        if not r > arb(fmpq(-1, 8)):
            raise ValueError('Real right-derivative overlap chart required')
        even, _ = module.support.theta_jets(acb(r), order=0)
        odd = self.normalized_odd_jets(r)[0]
        ratio = odd/even[0].real
        logarithmic = (arb(fmpq(5, 2))-arb.pi()*(2*(r-arb(self.center))).exp()
                       -ratio/2-(r/2).tanh()/4)
        value = self.source(acb(r), 1).real*logarithmic
        if not value.is_finite():
            raise ValueError('Finite profile source derivative required')
        return value

    def weighted_tail(self, start):
        decay = arb.pi()*(1+(-2*arb(self.center)).exp())/2
        return (self.constants[0].sqrt()*(-arb(fmpq(5, 2))*arb(self.center)).exp()
                *module.bounds.exponential_integral_upper(2, decay, start))

    def action_tail(self, real_r, cap, f_at_r):
        start = (2*(arb(cap)-abs(real_r).upper())).exp()
        if not start >= 1:
            raise ValueError('Positive full-action tail chart required')
        phi_tail = module.bounds.exponential_integral_upper(2, arb.pi(), start)
        return (2*(abs(f_at_r).upper()*self.constants[0]*phi_tail
                   +self.weighted_tail(start))).upper()

    def source_l1(self, radius, cells):
        interior = arb(0)
        for i in range(cells):
            lo, hi = radius*i/cells, radius*(i+1)/cells
            r = arb((lo+hi)/2, arb((hi-lo)/2).upper())
            _, weighted = self.weighted_source(acb(r), 1)
            interior += 4*arb(hi-lo)*abs(weighted).upper()*(r/2).cosh().upper()
        return (interior+4*self.weighted_tail((2*arb(radius)).exp())).upper()

    def exterior_residual_squared(self, radius, l1):
        start = (2*arb(radius)).exp()
        physical_tail = ((-5*arb(self.center)).exp()
                         *module.bounds.exponential_integral_upper(
                             2, arb.pi()*(-2*arb(self.center)).exp(), start))
        mass = 4*self.constants[0]*module.bounds.exponential_integral_upper(2, arb.pi(), start)
        # |Bh| <= (|h|+||h||_L1(nu))/2 and 2ab <= a²+b².
        # The folded nu integral of |h|² is 2 integral G(r-R)² dr.
        return (physical_tail+l1*l1*mass/2).upper()


def produce(centers, widths, radius, boxes, l1_cells, precision, tolerance):
    if precision < 128 or boxes < 16 or l1_cells < 16:
        raise ValueError('At least 128 bits and sixteen cells required')
    centers, widths = list(map(fmpq, centers)), list(map(fmpq, widths))
    radius = fmpq(radius)
    if not centers or len(centers) != len(widths) or any(w <= 0 for w in widths):
        raise ValueError('One positive exact width for each source center required')
    intervals = sorted((c-w/2, c+w/2) for c, w in zip(centers, widths))
    if intervals[-1][1] > 59 or any(left[1] > right[0]
                                    for left, right in zip(intervals, intervals[1:])):
        raise ValueError('Disjoint cells lying in the left J4 piece required')
    if not 0 < radius < 5:
        raise ValueError('Spatial radius must lie strictly between zero and action cutoff five')
    ctx.prec = precision
    actions = [ProfileAction(c) for c in centers]
    scales = [arb(w).sqrt() for w in widths]
    l1 = [action.source_l1(radius, l1_cells) for action in actions]
    exterior = [arb(w)*action.exterior_residual_squared(radius, bound)
                for w, action, bound in zip(widths, actions, l1)]
    count = len(actions)
    gram = [[arb(0) for _ in actions] for _ in actions]
    records = []
    for i in range(boxes):
        lo, hi = radius*i/boxes, radius*(i+1)/boxes
        midpoint, half_width = (lo+hi)/2, (hi-lo)/2
        r = arb(midpoint, arb(half_width).upper())
        gaps = [module.support.positive_gap((sign*acb(r)).exp()) for sign in (1, -1)]
        lower_gap = min(g.real.lower() for g in gaps)
        if not lower_gap > 0:
            raise ValueError('Strict positive whole-cell support gap required')
        coth = lower_gap.cosh()/lower_gap.sinh()
        residuals, point_records = [], []
        for action, scale, bound in zip(actions, scales, l1):
            point, tail = action.value(acb(midpoint), tolerance=tolerance)
            derivative = abs(action.source_derivative(r)).upper()
            source_max = abs(action.source(acb(r), 1)).upper()
            lipschitz = derivative/2+coth*(source_max+bound)/2
            residual = scale*(point+arb(0, (arb(half_width)*lipschitz).upper()))
            if not residual.is_finite():
                raise ValueError('Finite full-cell residual enclosure required')
            residuals.append(residual)
            point_records.append({'B_source': module.endpoints(point),
                                  'full_action_tail_upper': module.endpoints(tail),
                                  'source_derivative_abs_upper': module.endpoints(derivative),
                                  'residual_lipschitz_upper': module.endpoints(lipschitz.upper()),
                                  'scaled_full_cell_residual': module.endpoints(residual)})
        phi, _ = actions[0].weighted_source(acb(r), 1)
        density = 4*phi.real*(r/2).cosh()
        if not density.is_finite() or not density.upper() > 0:
            raise ValueError('Finite original folded density enclosure required')
        # Phi is strictly positive on the real line. A wide exponential ball
        # may have a negative lower endpoint even on this real chart.
        low, high = max(arb(0), density.lower()), density.upper()
        density = arb((low+high)/2, ((high-low)/2).upper())
        for j in range(count):
            for k in range(j, count):
                gram[j][k] += arb(hi-lo)*density*residuals[j]*residuals[k]
                if not gram[j][k].is_finite():
                    raise ValueError('Finite common cross-Gram enclosure required')
                gram[k][j] = gram[j][k]
        records.append({'index': i, 'midpoint_exact': str(midpoint),
                        'support_gap_lower': module.endpoints(lower_gap),
                        'folded_density': module.endpoints(density), 'columns': point_records})
        print(json.dumps({'cell': i, 'cells': boxes, 'interior_diagonal':
                          [str(gram[j][j]) for j in range(count)]}), flush=True)
    center_matrix = [[entry.mid() for entry in row] for row in gram]
    radii = [[max((gram[j][k].upper()-center_matrix[j][k]).upper(),
                   (center_matrix[j][k]-gram[j][k].lower()).upper())
              for k in range(count)] for j in range(count)]
    # Pay the outward serialized endpoints as well as the internal ball.
    error = max(sum(row, arb(0)).upper() for row in radii)
    exterior_trace = sum(exterior, arb(0)).upper()
    inflation = (error+exterior_trace).upper()
    # Round diagonal additions upward; off-diagonal midpoints are exact.
    upper = [[(center_matrix[j][k]+inflation).upper() if j == k else center_matrix[j][k]
              for k in range(count)] for j in range(count)]
    pivots, factor = [], [[arb(0) for _ in actions] for _ in actions]
    for j in range(count):
        pivot = upper[j][j]-sum((factor[j][k]**2*pivots[k] for k in range(j)), arb(0))
        if not pivot > 0:
            raise ValueError('Positive upper-Gram LDL pivot required')
        pivots.append(pivot)
        for k in range(j+1, count):
            factor[k][j] = (upper[k][j]-sum((factor[k][i]*factor[j][i]*pivots[i]
                                           for i in range(j)), arb(0)))/pivot
    norm_cap = max((upper[j][j]+sum((abs(upper[j][k]).upper()
                                    for k in range(count) if k != j), arb(0))).upper()
                   for j in range(count))
    if count == 2:
        a, b, c = upper[0][0], upper[0][1], upper[1][1]
        norm_cap = ((a+c)/2+((a-c)**2/4+b*b).sqrt()).upper()
    return {'scope': 'Conditional directed full-space simultaneous complex-coefficient Gram for the listed left J4 columns with zero primal/dual witnesses; no full family, convergence, signs, Lean, Robin or RH certificate',
            'runtime': {'python': sys.version.split()[0], 'python_flint': flint.__version__,
                        'precision_bits': ctx.prec},
            'centers_exact': list(map(str, centers)), 'cell_widths_exact': list(map(str, widths)),
            'primal_and_dual_witnesses': 'zero for every listed column',
            'spatial_radius_exact': str(radius), 'radial_boxes': boxes,
            'source_l1_boxes': l1_cells, 'action_cutoff': 5, 'nominal_tolerance': tolerance,
            'source_l1_upper': list(map(module.endpoints, l1)),
            'interior_cross_gram': [[module.endpoints(v) for v in row] for row in gram],
            'interior_center_matrix': [[module.endpoints(v) for v in row] for row in center_matrix],
            'interior_error_norm_upper': module.endpoints(error),
            'exterior_column_squared_upper': list(map(module.endpoints, exterior)),
            'exterior_gram_norm_upper': module.endpoints(exterior_trace),
            'positive_hermitian_upper_gram': [[module.endpoints(v) for v in row] for row in upper],
            'positive_ldl_pivots': list(map(module.endpoints, pivots)),
            'upper_gram_norm_upper': module.endpoints(norm_cap),
            'quadrature_callbacks': [a.calls for a in actions],
            'nonanalytic_or_invalid_boxes_rejected': [a.rejections for a in actions],
            'supplier_sha256': {name: hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                                for name in ['theta_action_integral.py', 'theta_direct_action.py',
                                             'theta_translation_bounds.py', 'derivative_bandwidth.py']},
            'producer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'old_quadratic_rows_or_grid_producers_used': False, 'cells': records}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--centers', nargs='+', default=['0', '1/2'])
    parser.add_argument('--widths', nargs='+', default=['1/2', '1/2'])
    parser.add_argument('--radius', default='5/2')
    parser.add_argument('--boxes', type=int, default=128)
    parser.add_argument('--l1-cells', type=int, default=128)
    parser.add_argument('--precision', type=int, default=192)
    parser.add_argument('--tolerance', default='1e-12')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = produce(args.centers, args.widths, args.radius, args.boxes,
                     args.l1_cells, args.precision, args.tolerance)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: result[key] for key in ['positive_hermitian_upper_gram',
                                                 'upper_gram_norm_upper']}, indent=2))


if __name__ == '__main__':
    main()
