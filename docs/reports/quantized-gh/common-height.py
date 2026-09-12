from fractions import Fraction as F
import json
import math

import sympy as sp

checks = []


def check(name, condition):
    assert condition, name
    checks.append(name)


def exponential_partial(x, degree):
    return sum((x**j / math.factorial(j) for j in range(degree + 1)), F(0))


check("exp(7/10) > 2 through degree four", exponential_partial(F(7, 10), 4) > 2)
check("exp(11/10) > 3 through degree five", exponential_partial(F(11, 10), 5) > 3)
log5_lower = 2 * sum((F(2, 3) ** (2*j+1) / (2*j+1) for j in range(4)), F(0))
check("four-term log5 lower bound", log5_lower == F(8, 5) + F(4, 15309))
check("theta < 7/8 by integer powers", F(5, 2)**8 < 3**7)
check("exp(3/10) > 4/3", exponential_partial(F(3, 10), 3) > F(4, 3))
check("exp(9/10) > 12/5", exponential_partial(F(9, 10), 4) > F(12, 5))
check("strict positive m from two strict exponential bounds", 2*F(3, 4)+F(5, 12) == F(23, 12))
rho2_upper = (F(1, 2)**2 + 2*F(11, 10)**2) / 54
check("rho squared upper constant", rho2_upper == F(89, 1800) < F(7, 30)**2)
check("rho squared lower bound implies eta > 9/10", F(1, 27) > ((F(9, 10)-F(8, 15))/2)**2)
check("lambda lower constant", F(8, 15)-F(7, 30) == F(3, 10))
check("second-moment envelope bound", 2*F(3, 4)**2+F(5, 12)**2 == F(187, 144))
check("second-moment mixture bound", F(9, 8)+F(1, 4)+F(7, 8)*F(1, 9) == F(53, 36))
check("strict second-moment sign", F(187, 144) < F(53, 36))
check("geometric envelope tail from n=3", 2*F(3, 4)**3+F(5, 12)**3 == F(1583, 1728) < F(9, 8))
check("scaled-gap neighborhood margin", F(32, 3)*F(3, 64) == F(1, 2))
check("first-moment neighborhood margin", F(16, 3)*F(3, 64) == F(1, 4))

width, middle = sp.symbols("width middle", nonnegative=True)
v = sp.Matrix([0, middle, width])
projection = v - sp.ones(3, 1)*(middle+width)/3
norm2 = sp.expand(projection.dot(projection))
check("shape-projection identity", sp.simplify(norm2-sp.Rational(2, 3)*(width**2-width*middle+middle**2)) == 0)
check("shape-projection remainder on 0<=middle<=width", sp.simplify(2*width**2/3-norm2-2*middle*(width-middle)/3) == 0)

order, magnitude = sp.symbols("order magnitude", positive=True)
cutoff = (order+1)*magnitude/(3*order+(order+1)*magnitude)
check("leading-term strict-tail cutoff boundary", sp.simplify(3*cutoff/((order+1)*(1-cutoff))-magnitude/order) == 0)

z = sp.symbols("z")
atoms = sp.symbols("a0:8", positive=True)
masses = sp.symbols("s0:8")
numerator = sum(masses[j]*atoms[j]*sp.prod(1-z*atoms[l] for l in range(8) if l != j) for j in range(8))
highest = sp.Poly(numerator, z).coeff_monomial(z**7)
check("eight-atom derivative highest coefficient", sp.simplify(highest+sp.prod(atoms)*sum(masses)) == 0)
check("mass-zero derivative degree at most six", sp.simplify(highest.subs(masses[-1], -sum(masses[:-1]))) == 0)

print(json.dumps({"exact_fixed_checks": len(checks), "checks": checks, "sympy": sp.__version__, "CPU_candidate_search": False, "GPU_dispatches": 0}, ensure_ascii=False, indent=2))
