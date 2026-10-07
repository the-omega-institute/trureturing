"""Directed original-energy slack on the fixed quadratic/quartic source plane."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

import flint
from flint import acb, arb, ctx, fmpq


ROOT = Path.cwd()
REPORT = ROOT/'docs/reports/theta-mixed-matrix'


def load(name):
    path = REPORT/name
    spec = importlib.util.spec_from_file_location('poly_'+path.stem, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def endpoints(v):
    if not v.is_finite():
        raise ValueError('Finite directed value required')
    return {'display': str(v), 'lower_dyadic': [str(q) for q in v.lower().man_exp()],
            'upper_dyadic': [str(q) for q in v.upper().man_exp()]}


def matrix(v):
    return [[endpoints(q) for q in row] for row in v]


def ellipse(lo, hi, rho):
    half = (hi-lo)/2
    center = (lo+hi)/2
    return acb(arb(center.mid(), (abs(center-center.mid()).upper()+
                                half.upper()*(rho+1/rho)/2).upper()),
               arb(0, (half.upper()*(rho-1/rho)/2).upper()))


def produce(nodes=24):
    if nodes not in (24, 32):
        raise ValueError('Use the committed 24-node certificate or its one 32-node refinement')
    ctx.prec = 192
    supplier = load('theta_direct_action.py')
    tiling = load('theta_negative_block_gap.py')
    tails = load('theta_translation_bounds.py')
    _, constants, _ = tails.derivative_supplier(REPORT/'derivative_bandwidth.py')
    c0 = constants[0]
    radius = fmpq(3, 2)
    phi = (1+arb(5).sqrt())/2
    r_cells = tiling.partition(2, radius, phi)
    t_cells = tiling.partition(2, fmpq(1), phi)
    rb = [(tiling.at(a, phi), tiling.at(b, phi)) for a, b, _, _ in r_cells]
    tb = [(tiling.at(a, phi), tiling.at(b, phi)) for a, b, _, _ in t_cells]
    callbacks, rejected = 0, 0

    def theta(z):
        jet, factor = supplier.theta_jets(z, order=0)
        return factor*jet[0]

    def guarded(function):
        def callback(z, analytic):
            nonlocal callbacks, rejected
            callbacks += 1
            try:
                value = function(z)
                if not value.is_finite():
                    raise ValueError('Finite analytic integrand required')
                return value
            except ValueError:
                rejected += 1
                return acb('nan')
        return callback

    def integrate(function):
        value = acb.integral(guarded(function), acb(0), acb(radius),
                             abs_tol=arb('1e-48'), rel_tol=arb('1e-46'),
                             eval_limit=30000, depth_limit=30).real
        if not value.is_finite():
            raise ValueError('Finite validated retained integral required')
        return value

    moments, moment_tails = {}, {}
    for j in (2, 4, 6, 8):
        core = integrate(lambda z, j=j: 4*theta(z)*(z/2).cosh()*z**j)
        tail = (4*c0*tails.exponential_integral_upper(2+j//2, arb.pi(),
                                                    (2*arb(radius)).exp())).upper()
        if not tail.is_finite() or not tail >= 0:
            raise ValueError('Finite positive full covariance tail required')
        moments[j] = core+arb(tail/2, (tail/2).upper())
        moment_tails[j] = tail
    variance = [[moments[4]-moments[2]**2,
                 moments[6]-moments[2]*moments[4]],
                [moments[6]-moments[2]*moments[4],
                 moments[8]-moments[4]**2]]

    def gap_square_psi(z):
        # sinh(z)/z = 0F1(3/2; z^2/4), including the removable value at zero.
        denominator = (z*z/4).hypgeom_0f1(acb(fmpq(3, 2)))
        if denominator.contains(0):
            raise ValueError('Holomorphic cancelled Gamma denominator required')
        return z*(z/2).exp()/(2*denominator)

    def gamma_values(r, t, cached=None):
        s = r+(radius-r)*t
        d, u = s-r, s+r
        weight = (2*(radius-r)*(cached if cached is not None else theta(r))*theta(s)
                  *(u*u*gap_square_psi(d)+d*d*gap_square_psi(u)))
        b = r*r+s*s
        values = [weight, weight*b, weight*b*b]
        if not all(v.is_finite() for v in values):
            raise ValueError('Finite holomorphic joint Gamma box required')
        return values

    rho = arb(2)
    error_factor = 64/(15*(rho-1)*rho**(2*nodes-1))
    gauss = [arb.legendre_p_root(nodes, k, weight=True) for k in range(nodes)]
    gamma_sum, gamma_errors = [arb(0) for _ in range(3)], [arb(0) for _ in range(3)]
    for i, (rlo, rhi) in enumerate(rb):
        rmid, rhalf = (rlo+rhi)/2, (rhi-rlo)/2
        rvalues = [(acb(rmid+rhalf*x), w) for x, w in gauss]
        rphis = [theta(z) for z, _ in rvalues]
        re = ellipse(rlo, rhi, rho)
        for tlo, thi in tb:
            tmid, thalf = (tlo+thi)/2, (thi-tlo)/2
            te = ellipse(tlo, thi, rho)
            upper = [abs(v).upper() for v in gamma_values(re, te)]
            area = (rhi-rlo)*(thi-tlo)
            local = [acb(0) for _ in range(3)]
            for (r, rw), rphi in zip(rvalues, rphis):
                for x, tw in gauss:
                    vals = gamma_values(r, acb(tmid+thalf*x), cached=rphi)
                    for j in range(3):
                        local[j] += rw*tw*vals[j]
            for j in range(3):
                error = (area*upper[j]*error_factor).upper()
                gamma_sum[j] += (rhalf*thalf*local[j]).real+arb(0, error)
                gamma_errors[j] += error
        if i % 4 == 0:
            print(json.dumps({'Gamma_radial_row': i, 'error00': str(gamma_errors[0])}), flush=True)
    gamma = [[gamma_sum[0], gamma_sum[1]], [gamma_sum[1], gamma_sum[2]]]

    prime = [[arb(0), arb(0)], [arb(0), arb(0)]]
    atoms = []
    for p in (2, 3, 5, 7, 11, 13):
        n = p
        while n <= 16:
            t = arb(n).log()
            coefficient = 2*arb(p).log()/arb(n).sqrt()
            for j, (a, b) in enumerate(((0, 0), (0, 1), (1, 1))):
                def value(y, a=a, b=b, t=t):
                    scalar = 4*y*y*t*t*theta(y-t/2)*theta(y+t/2)
                    ratio = 2*y*y+t*t/2
                    return scalar*ratio**(a+b)
                prime[a][b] += coefficient*integrate(value)
            atoms.append(n)
            n *= p
    prime[1][0] = prime[0][1]
    slack = [[gamma[i][j]+prime[i][j]-variance[i][j]/2 for j in range(2)] for i in range(2)]
    target = fmpq(1, 10**12)
    shifted = [[slack[i][j]-(arb(target) if i == j else 0) for j in range(2)] for i in range(2)]
    determinant = shifted[0][0]*shifted[1][1]-shifted[0][1]**2
    passed = bool(shifted[0][0] > 0 and determinant > 0)
    return {
        'scope': 'Unreviewed conditional ORIGINAL polynomial-input energy minorant; no all-test/cofinal, Lean, Robin or RH certificate',
        'runtime': {'python': sys.version.split()[0], 'python_flint': flint.__version__, 'precision_bits': ctx.prec},
        'producer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'supplier_sha256': {name: hashlib.sha256((REPORT/name).read_bytes()).hexdigest() for name in
                            ('theta_direct_action.py', 'theta_negative_block_gap.py', 'theta_translation_bounds.py', 'derivative_bandwidth.py')},
        'source_basis': ['x^2', 'x^4'], 'radial_retention_exact': str(radius),
        'fib_depth': 2, 'radial_cells': len(rb), 'triangle_parameter_cells': len(tb),
        'tensor_gauss_nodes_each': nodes, 'ellipse_rho_exact': '2',
        'retained_prime_powers': sorted(atoms), 'target_coefficient_gap_exact': str(target),
        'density_or_prime_callbacks': callbacks, 'invalid_analytic_boxes_rejected': rejected,
        'full_nu_moments': {str(j): endpoints(v) for j, v in moments.items()},
        'nu_moment_tail_upper': {str(j): endpoints(v) for j, v in moment_tails.items()},
        'full_covariance_matrix': matrix(variance),
        'retained_Gamma_matrix': matrix(gamma), 'Gamma_tensor_error_allowances': [endpoints(v) for v in gamma_errors],
        'retained_prime_matrix': matrix(prime), 'retained_original_slack_matrix': matrix(slack),
        'target_shifted_first_minor': endpoints(shifted[0][0]), 'target_shifted_determinant': endpoints(determinant),
        'passes_fixed_polynomial_subspace_target': passed,
        'unpaid': ['independent mathematical/domain/tensor review', 'all remaining source directions and common/cofinal comparison', 'Lean/kernel interface certification', 'RH and Robin'],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--nodes', type=int, default=24)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = produce(args.nodes)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('target_shifted_first_minor', 'target_shifted_determinant', 'passes_fixed_polynomial_subspace_target')}, indent=2))


if __name__ == '__main__':
    main()
