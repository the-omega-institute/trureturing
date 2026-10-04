"""Directed small-window translation bounds; no Fredholm solve or RH sign."""
import argparse
import ast
import hashlib
import json
import math
import sys
from pathlib import Path

import flint
from flint import arb, ctx, fmpq


def endpoint(value):
    if not value.is_finite():
        raise ValueError('Finite bound required')
    value = value.upper()
    return {'display': str(value), 'dyadic': [str(v) for v in value.man_exp()]}


def derivative_supplier(path):
    """Reuse only the existing definitions, without executing its old grid."""
    data = path.read_bytes()
    tree = ast.parse(data)
    names = {'polys', 'scalar_constant', 'phi_derivatives'}
    nodes = [node for node in tree.body
             if isinstance(node, ast.FunctionDef) and node.name in names]
    if {node.name for node in nodes} != names or len(nodes) != len(names):
        raise ValueError('Existing derivative supplier definitions required')
    pi = arb.pi()
    scope = {'arb': arb, 'fmpq': fmpq, 'TERMS': 6, 'pi': pi}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(path), 'exec'), scope)
    scope['coeff'] = {(j, a): scope['polys'](a, j) for j in range(4)
                      for a in (fmpq(9, 2), fmpq(5, 2))}
    scope['rstar'] = arb(fmpq(3, 2))**10*(-5*pi).exp()
    if not scope['rstar'] < 1:
        raise ValueError('Existing theta derivative tail ratio is not certified')
    scope['CT'] = [scope['scalar_constant'](j, True) for j in range(4)]
    constants = {j: scope['scalar_constant'](j) for j in (0, 2)}
    return scope['phi_derivatives'], constants, hashlib.sha256(data).hexdigest()


def exponential_integral_upper(power, rate, start):
    """Half of integral_start^infty y^power exp(-rate*y)dy, divided by sqrt(start)."""
    if not rate > 0 or not start >= 1:
        raise ValueError('Positive tail rate and start at least one required')
    polynomial = sum((arb(math.factorial(power)//math.factorial(j))
                      *start**j/rate**(power-j+1) for j in range(power+1)), arb(0))
    return (-rate*start).exp()*polynomial/(2*start.sqrt())


def second_envelope(derivative, left, right, depth=0):
    x = arb((left+right)/2, arb((right-left)/2).upper())
    try:
        bound = abs(derivative(x)[2])
        if not bound.is_finite():
            raise ValueError('Nonfinite shifted second-derivative enclosure')
        return bound.upper(), 1
    except RuntimeError as error:
        if str(error) != 'Uncertified actual original-theta denominator' or depth >= 12:
            raise
        middle = (left+right)/2
        a, acount = second_envelope(derivative, left, middle, depth+1)
        b, bcount = second_envelope(derivative, middle, right, depth+1)
        return max(a, b), acount+bcount


def produce(canonical, precision=192, boxes=2048):
    if not isinstance(precision, int) or isinstance(precision, bool) or precision < 128:
        raise ValueError('At least 128-bit precision required')
    if not isinstance(boxes, int) or isinstance(boxes, bool) or boxes < 128:
        raise ValueError('At least 128 radial boxes required')
    ctx.prec = precision
    supplier = canonical/'derivative_bandwidth.py'
    derivative, constants, supplier_hash = derivative_supplier(supplier)
    r, radius = fmpq(1, 16), fmpq(2)
    k = (arb(r)/2).sinh()/2
    interior = arb(0)
    shifted_leaves = 0
    for index in range(boxes):
        left, right = radius*index/boxes, radius*(index+1)/boxes
        x = arb((left+right)/2, arb((right-left)/2).upper())
        p0 = derivative(x)[0]
        lo, hi = max(fmpq(0), left-r), right+r
        second = arb(0)
        for part in range(8):
            part_left = lo+(hi-lo)*part/8
            part_right = lo+(hi-lo)*(part+1)/8
            bound, leaves = second_envelope(derivative, part_left, part_right)
            shifted_leaves += leaves
            second = max(second, bound)
        # Phi is even. The mean value integral of Phi'' encloses the
        # difference of the two first derivatives uniformly for |t|<=r.
        slope = arb(r)*second/p0.lower()+k
        density = 4*p0*(x/2).cosh()
        interior += arb(right-left)*density.upper()*slope.upper()**2
        if not interior.is_finite():
            raise ValueError('Nonfinite interior derivative norm enclosure')

    pi, start = arb.pi(), (2*arb(radius)).exp()
    lower_coefficient = 4*pi*pi-6*pi
    rate = pi*(2*(-2*arb(r)).exp()-1)
    if not lower_coefficient > 0 or not rate > 0:
        raise ValueError('Positive actual-theta tail lower coefficient/rate required')
    c0, c2 = constants[0], constants[2]
    # WC1 gives |Phi''(x+s)| <= C2 exp(17(x+r)/2-pi exp(2(x-r))).
    # Divide by Phi(x)>= (4pi^2-6pi) exp(9x/2-pi exp(2x)).
    # The original folded nu density is at most 4 C0 exp(5x-pi exp(2x)).
    tail_second = (8*c0*arb(r)**2*c2**2*(17*arb(r)).exp()/lower_coefficient**2
                   *exponential_integral_upper(6, rate, start))
    tail_scalar = 8*c0*k*k*exponential_integral_upper(2, pi, start)
    total = interior+tail_second+tail_scalar
    lipschitz = total.sqrt()
    hs = (total*arb(2*r**3/3)).sqrt()
    if not lipschitz.is_finite() or not hs.is_finite():
        raise ValueError('Nonfinite translation derivative/HS bound')
    return {
        'scope': 'Actual theta translation derivative and Hilbert-Schmidt upper bounds; no regularization error, finite matrix, transfer sign, Lean or RH certificate',
        'runtime': {'python': sys.version.split()[0], 'python_flint': flint.__version__, 'precision_bits': precision},
        'supplier': 'derivative_bandwidth.py', 'supplier_sha256': supplier_hash,
        'producer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'window_radius_exact': str(r), 'spatial_radius_exact': str(radius), 'radial_boxes': boxes,
        'theta_derivative_terms': 6,
        'shifted_envelope_subcells': 8,
        'shifted_envelope_certified_leaves': shifted_leaves,
        'old_derivative_grid_executed': False,
        'interior_squared_Lw_upper': endpoint(interior),
        'exterior_squared_Lw_second_upper': endpoint(tail_second),
        'exterior_squared_Lw_scalar_upper': endpoint(tail_scalar),
        'whole_squared_Lw_upper': endpoint(total),
        'Lw_upper': endpoint(lipschitz),
        'MF_upper': endpoint(hs),
        'midpoint_delta_bound': 'Lw * sqrt(2*r^3/3) / m',
        'unpaid': ['actual Fredholm kernel entries', 'regularization low-spectral error on required inputs', 'whole-space complementary residual', 'projected reconstruction/norm comparison', 'original half-bound', 'Robin and RH'],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--canonical', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--precision', type=int, default=192)
    parser.add_argument('--boxes', type=int, default=2048)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = produce(args.canonical.resolve(), args.precision, args.boxes)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('radial_boxes', 'Lw_upper', 'MF_upper', 'exterior_squared_Lw_second_upper')}, indent=2))


if __name__ == '__main__':
    main()
