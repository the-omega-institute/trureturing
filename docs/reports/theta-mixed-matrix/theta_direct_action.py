"""Prototype complex theta jets and isolated positive support gap."""
import ast
import json
from pathlib import Path

from flint import acb, arb, ctx, fmpq


CANONICAL = Path.cwd()/'docs/reports/theta-mixed-matrix'
namespace = {'fmpq': fmpq}
nodes = [node for node in ast.parse((CANONICAL/'derivative_bandwidth.py').read_bytes()).body
         if isinstance(node, ast.FunctionDef) and node.name == 'polys']
if len(nodes) != 1:
    raise ValueError('Existing derivative polynomial helper required')
exec(compile(ast.Module(body=nodes, type_ignores=[]), 'derivative_polys', 'exec'), namespace)
POLYS = namespace['polys']


def horner(coefficients, z):
    value = acb(0)
    for c in reversed(coefficients):
        value = value*z+acb(c)
    return value


def theta_jets(z, order=14, terms=8):
    """Return normalized even jets and Phi's common exponential factor."""
    z = acb(z)
    if not z.is_finite() or not abs(z.imag) < arb(fmpq(1, 6)):
        raise ValueError('Actual theta physical strip required')
    if not z.real > arb(fmpq(-1, 8)):
        z = -z
    if not z.real > arb(fmpq(-1, 8)):
        raise ValueError('Whole theta box must lie in an overlap chart')
    U = (2*z).exp()
    pi = arb.pi()
    lam = pi*(2*z.real.lower()).exp()*(2*abs(z.imag).upper()).cos()
    upperU = abs(U).upper()
    if not lam > 0:
        raise ValueError('Positive complex theta decay rate required')

    def tail(power):
        start = terms+1
        ratio = arb(fmpq(start+1, start))**power*(-lam*(2*start+1)).exp()
        if not ratio < 1:
            raise ValueError('Derivative-series tail ratio failed')
        return arb(start)**power*(-lam*(start*start-1)).exp()/(1-ratio)

    jets = []
    for j in range(0, order+1, 2):
        p = {a: POLYS(a, j) for a in (fmpq(9, 2), fmpq(5, 2))}
        value = acb(0)
        for n in range(1, terms+1):
            v = pi*n*n*U
            value += (4*pi*pi*n**4*U*horner(p[fmpq(9, 2)], v)
                      -6*pi*n*n*horner(p[fmpq(5, 2)], v))*(-pi*(n*n-1)*U).exp()
        error = arb(0)
        for k, c in enumerate(p[fmpq(9, 2)]):
            error += 4*pi*pi*upperU*abs(arb(c))*(pi*upperU)**k*tail(4+2*k)
        for k, c in enumerate(p[fmpq(5, 2)]):
            error += 6*pi*abs(arb(c))*(pi*upperU)**k*tail(2+2*k)
        if not error.is_finite():
            raise ValueError('Finite actual derivative-series remainder required')
        jets.append(value+acb(arb(0, error.upper()), arb(0, error.upper())))
    if jets[0].contains(0):
        raise ValueError('Nonzero normalized theta denominator required')
    prefactor = (arb(fmpq(5, 2))*z-pi*U).exp()
    return jets, prefactor


def positive_gap(u):
    """Rouche-enclosed b>0 root; negative-root collisions are irrelevant."""
    u = acb(u)
    if not u.is_finite() or not u.real > 0 or not u.imag.contains(0):
        raise ValueError('A right-half-plane parameter box meeting the real axis is required')
    uc = acb(u.real.mid())
    b = uc/(uc*uc+1)
    for _ in range(16):
        f = uc*(uc+1)*b**3+(3*uc*uc+2*uc+1)*b*b+2*(uc*uc+1)*b-2*uc
        d = 3*uc*(uc+1)*b*b+2*(3*uc*uc+2*uc+1)*b+2*(uc*uc+1)
        trial = b-f/d
        b = acb(trial.real.mid(), trial.imag.mid())
    a3, a2, a1, a0 = u*(u+1), 3*u*u+2*u+1, 2*(u*u+1), -2*u
    center_residual = ((a3*b+a2)*b+a1)*b+a0
    derivative = (3*a3*b+2*a2)*b+a1
    dc = (3*uc*(uc+1)*b+2*(3*uc*uc+2*uc+1))*b+2*(uc*uc+1)
    d0 = acb(dc.real.mid(), dc.imag.mid())
    lower_d = abs(d0).lower()
    if not lower_d > 0:
        raise ValueError('Nonzero root linearization required')
    radius = max(arb(2)**(-ctx.prec//2), (2*abs(center_residual).upper()/lower_d).upper())
    for _ in range(20):
        remainder = (abs(center_residual).upper()+abs(derivative-d0).upper()*radius
                     +abs(a2+3*a3*b).upper()*radius**2+abs(a3).upper()*radius**3)
        if b.real > radius and remainder < lower_d*radius:
            enclosed = acb(arb(b.real, radius), arb(b.imag, radius))
            return (1+enclosed).log()
        radius = 2*radius
    raise ValueError('Positive support branch not isolated; subdivide parameter box')


def main():
    ctx.prec = 192
    data = []
    for r in (fmpq(0), fmpq(1, 4), fmpq(3, 4), fmpq(3, 2), fmpq(5, 2)):
        z = acb(arb(r, arb(fmpq(1, 1024))), arb(0, arb(fmpq(1, 1024))))
        right = positive_gap(z.exp())
        left = positive_gap((-z).exp())
        jets, prefactor = theta_jets(z)
        ratios = [str(v/jets[0]-acb(fmpq(1, 4**k))) for k, v in enumerate(jets[1:], 1)]
        data.append({'r_exact': str(r), 'real_and_imaginary_radius': '1/1024',
                     'right_gap_box': str(right), 'left_gap_box': str(left),
                     'v1_through_v7_boxes': ratios, 'Phi_box': str(prefactor*jets[0])})
    result = {'scope': 'Unreviewed analytic-support and theta-jet acquisition prototype; no action integral or residual certificate',
              'precision_bits': ctx.prec, 'boxes': data,
              'unpaid': ['independent support/jet proof review', 'actual B action quadrature', 'whole-space residual and all spatial tails', 'RH and Robin']}
    output = Path(__file__).with_name('theta-direct-action-probe-result.json')
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
