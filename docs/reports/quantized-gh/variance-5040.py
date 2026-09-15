from fractions import Fraction
from importlib.metadata import version
from math import prod
import platform
from flint import arb, ctx

assert version('python-flint') == '0.8.0'
ctx.prec = 256
pa = ((2, 4), (3, 2), (5, 1), (7, 1))
n = prod(p**a for p, a in pa)
sigma = prod((p**(a + 1) - 1) // (p - 1) for p, a in pa)
ratio = Fraction(sigma, n)
assert n == 5040 and sigma == 19344 and ratio == Fraction(403, 105)
k = len(pa)
x = [arb(p**(a + 1)).log() for p, a in pa]
mu = sum(x, arb(0)) / k
V = sum(((t - mu)**2 for t in x), arb(0))
B = mu.exp()
r = (V / (k * (k - 1))).sqrt()
L, H = mu - r, mu + (k - 1) * r
assert V > 0 and L > 0
E = prod((Fraction(p, p - 1) for p, a in pa), start=Fraction(1))
Eball = arb(E.numerator) / E.denominator
exact = arb(ratio.numerator) / ratio.denominator
jensen = Eball * (1 - 1 / B)**k
quadratic = jensen * (-B * V / (2 * k * (B - 1)**2)).exp()
sharp = Eball * (1 - (-H).exp()) * (1 - (-L).exp())**(k - 1)
assert exact < sharp and sharp < quadratic and quadratic < jensen
values = {'mu': mu, 'V': V, 'L': L, 'H': H, 'exact': exact,
          'sharp': sharp, 'quadratic': quadratic, 'jensen': jensen}
d = 10**50
bounds = {}
for name, value in values.items():
    a = (value * d).floor().unique_fmpz()
    assert a is not None
    a = int(a)
    assert arb(a) / d < value and value < arb(a + 1) / d
    bounds[name] = (Fraction(a, d), Fraction(a + 1, d))
    print(name, a, a + 1)
assert ratio < bounds['sharp'][0]
assert bounds['sharp'][1] < bounds['quadratic'][0]
assert bounds['quadratic'][1] < bounds['jensen'][0]
print('n=', n, 'sigma=', sigma, 'sigma/n=', ratio, 'E_S=', E)
print('python=', platform.python_version(), 'python-flint=', version('python-flint'),
      'precision_bits=', ctx.prec, 'denominator=', d)
print('PASS: exact < sharp < quadratic < Jensen; Arb and rational endpoint checks')
