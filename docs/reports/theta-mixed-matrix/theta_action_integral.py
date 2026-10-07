"""Direct B action acquisition for fixed even critical-source coefficients."""
import argparse
import importlib.util
import json
from pathlib import Path
import time

import flint
from flint import acb, arb, ctx, fmpq


HERE = Path(__file__).resolve().parent


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


support = load(HERE/'theta_direct_action.py', 'theta_action_support')
bounds = load(HERE/'theta_translation_bounds.py', 'theta_action_bounds')


def endpoints(v):
    if not v.is_finite():
        raise ValueError('Finite directed result required')
    return {'display': str(v),
            'lower_dyadic': [str(x) for x in v.lower().man_exp()],
            'upper_dyadic': [str(x) for x in v.upper().man_exp()]}


class Action:
    def __init__(self, candidate):
        self.a = [fmpq(int(p), int(q)) for p, q in candidate['n_coefficients_exact_dyadic_rationals']]
        self.b = [fmpq(int(p), int(q)) for p, q in candidate['w_coefficients_exact_dyadic_rationals']]
        self.gammas = [acb.zeta_zero(j).imag for j in range(1, len(self.b)+1)]
        self.order = 2*len(self.a)
        self.calls = 0
        self.rejections = 0
        self.constants = self.derivative_constants()

    def derivative_constants(self):
        pi, result = arb.pi(), []
        for j in range(0, self.order+1, 2):
            total = arb(0)
            for a, pref, degree in ((fmpq(9, 2), 4*pi*pi, 4), (fmpq(5, 2), 6*pi, 2)):
                for k, p in enumerate(support.POLYS(a, j)):
                    power = degree+2*k
                    ratio = arb(fmpq(10, 9))**power*(-19*pi).exp()
                    if not ratio < 1:
                        raise ValueError('Positive full derivative-tail denominator required')
                    series = sum((arb(n)**power*(-pi*(n*n-1)).exp() for n in range(1, 9)), arb(0))
                    series += arb(9)**power*(-80*pi).exp()/(1-ratio)
                    total += pref*abs(arb(p))*pi**k*series
            if not total.is_finite():
                raise ValueError('Finite derivative constant required')
            result.append(total.upper())
        return result

    def weighted_source(self, z):
        jets, factor = support.theta_jets(z, order=self.order)
        phi = factor*jets[0]
        weighted = z*z*phi
        for k, coefficient in enumerate(self.a, 1):
            weighted -= acb(coefficient)*factor*(jets[k]-acb(fmpq(1, 4**k))*jets[0])
        return phi, weighted

    def source(self, z):
        jets, _ = support.theta_jets(z, order=self.order)
        return z*z-sum((acb(c)*(jets[k]/jets[0]-acb(fmpq(1, 4**k)))
                       for k, c in enumerate(self.a, 1)), acb(0))

    def weighted_source_on_piece(self, z, radial_sign):
        """The original source is analytic across the two radial charts."""
        return self.weighted_source(z)

    def witness(self, z):
        return sum((acb(c)*(acb(g)*z).cos() for c, g in zip(self.b, self.gammas)), acb(0))/(z/2).cosh()

    def normalized_odd_jets(self, r):
        """Real-chart odd derivatives; reuse the exact derivative polynomials."""
        if not r.is_finite() or not r > arb(fmpq(-1, 8)):
            raise ValueError('Finite real source-derivative overlap chart required')
        pi, U = arb.pi(), (2*r).exp()
        lam, upperU = pi*(2*r.lower()).exp(), U.upper()
        values = []
        for j in range(1, self.order+2, 2):
            polynomials = {a: support.POLYS(a, j) for a in (fmpq(9, 2), fmpq(5, 2))}
            value = arb(0)
            for n in range(1, 9):
                v = pi*n*n*U
                ps = []
                for a in (fmpq(9, 2), fmpq(5, 2)):
                    ps.append(support.horner(polynomials[a], acb(v)).real)
                value += (4*pi*pi*n**4*U*ps[0]-6*pi*n*n*ps[1])*(-pi*(n*n-1)*U).exp()
            error = arb(0)
            for a, prefactor, degree in ((fmpq(9, 2), 4*pi*pi*upperU, 4),
                                         (fmpq(5, 2), 6*pi, 2)):
                for k, coefficient in enumerate(polynomials[a]):
                    power = degree+2*k
                    ratio = arb(fmpq(10, 9))**power*(-19*lam).exp()
                    if not ratio < 1:
                        raise ValueError('Odd derivative tail denominator required')
                    tail = arb(9)**power*(-80*lam).exp()/(1-ratio)
                    error += prefactor*abs(arb(coefficient))*(pi*upperU)**k*tail
            if not value.is_finite() or not error.is_finite():
                raise ValueError('Finite odd source-derivative enclosure required')
            values.append(value+arb(0, error.upper()))
        return values

    def source_derivative(self, r):
        even, _ = support.theta_jets(acb(r), order=self.order)
        odd = self.normalized_odd_jets(r)
        even = [v.real for v in even]
        phi_ratio = odd[0]/even[0]
        derivative = 2*r
        for k, coefficient in enumerate(self.a, 1):
            derivative -= arb(coefficient)*(odd[k]/even[0]-even[k]*phi_ratio/even[0])
        if not derivative.is_finite():
            raise ValueError('Finite actual source derivative required')
        return derivative

    def witness_derivative(self, r):
        cosine = sum((arb(c)*(g*r).cos() for c, g in zip(self.b, self.gammas)), arb(0))
        sine = sum((-arb(c)*g*(g*r).sin() for c, g in zip(self.b, self.gammas)), arb(0))
        return (sine-cosine*(r/2).tanh()/2)/(r/2).cosh()

    def action_tail(self, real_r, cap, f_at_r):
        start_s = arb(cap)-abs(real_r).upper()
        if not start_s >= 0:
            raise ValueError('Action cutoff must exceed the whole radial box')
        start, pi = (2*start_s).exp(), arb.pi()
        def integral(power):
            return bounds.exponential_integral_upper(power, pi, start)
        c0, scalar = self.constants[0], arb(0)
        for k, coefficient in enumerate(self.a, 1):
            scalar += abs(arb(coefficient))*(self.constants[k]*integral(2+2*k)
                                           +c0*arb(fmpq(1, 4**k))*integral(2))
        error = 2*(abs(f_at_r).upper()*c0*integral(2)+c0*integral(3)+scalar)
        if not error.is_finite():
            raise ValueError('Finite full action tail required')
        return error.upper()

    def value(self, r, cap=5, tolerance='1e-18'):
        r = acb(r)
        if not r.imag.is_zero() or not abs(r.real).upper() < cap:
            raise ValueError('Real radial box inside action cutoff required')
        f_at_r = self.source(r)
        total = acb(0)
        for sign in (1, -1):
            gap = support.positive_gap((sign*r).exp())
            def callback(t, analytic):
                self.calls += 1
                try:
                    s = r+sign*t
                    phi, weighted = self.weighted_source_on_piece(s, piece_sign)
                    psi = (-t/2).exp()/(1-(-2*t).exp())
                    edge = 1-psi/(2*(r/2).cosh()*(s/2).cosh())
                    v = edge*(f_at_r*phi-weighted)*(s/2).cosh()
                    if not v.is_finite():
                        self.rejections += 1
                        return acb('nan')
                    return v
                except ValueError:
                    self.rejections += 1
                    return acb('nan')
            # The chart split at s=0 shares the exact same r parameter.
            cuts = [gap]
            if sign == -1 and r.real > gap.real and r.real < cap:
                cuts.append(r)
            cuts.append(acb(cap))
            for left, right in zip(cuts, cuts[1:]):
                piece_center = r.real+sign*(left.real+right.real)/2
                piece_sign = 1 if piece_center > 0 else -1 if piece_center < 0 else 0
                value = acb.integral(callback, left, right,
                                     abs_tol=arb(tolerance), rel_tol=arb(tolerance),
                                     eval_limit=30000, depth_limit=30)
                if not value.is_finite():
                    raise ValueError('Finite actual action quadrature required')
                total += value
        tail = self.action_tail(r.real, cap, f_at_r)
        return total.real+arb(0, tail), tail


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--points', nargs='+', default=['0', '1/4', '3/4', '3/2', '5/2'])
    parser.add_argument('--radius', default='0')
    parser.add_argument('--tolerance', default='1e-18')
    args = parser.parse_args()
    ctx.prec = 192
    candidate = json.loads(args.candidate.read_text())
    action = Action(candidate)
    records = []
    for point in args.points:
        r = arb(fmpq(point), arb(fmpq(args.radius)))
        started = time.monotonic()
        value, tail = action.value(acb(r), tolerance=args.tolerance)
        residual = value-action.witness(acb(r)).real
        records.append({'r_exact': point, 'radial_radius_exact': args.radius,
                        'B_source_interval': endpoints(value), 'residual_interval': endpoints(residual),
                        'whole_action_tail_upper': endpoints(tail),
                        'duration_seconds': time.monotonic()-started})
        print(json.dumps(records[-1]), flush=True)
    result = {'scope': 'Unreviewed actual B point/box action acquisition with fixed coefficients; no whole-space residual or sign certificate',
              'runtime': {'python_flint': flint.__version__, 'precision_bits': ctx.prec},
              'quadrature_callbacks': action.calls, 'nonanalytic_or_invalid_boxes_rejected': action.rejections,
              'points': records,
              'unpaid': ['independent action and spatial-tail review', 'whole-space common-source residual norm', 'RH and Robin']}
    args.output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
