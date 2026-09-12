from fractions import Fraction as F
import json

def add(*polys):
    out = {}
    for p in polys:
        for monomial, coefficient in p.items():
            out[monomial] = out.get(monomial, F(0)) + coefficient
    return {m: c for m, c in out.items() if c}

def scale(c, p):
    return add({m: F(c) * v for m, v in p.items()})

def mul(p, q):
    return add(*[{(a[0] + b[0], a[1] + b[1]): u * v}
                 for a, u in p.items() for b, v in q.items()])

one = {(0, 0): F(1)}
x, y = {(1, 0): F(1)}, {(0, 1): F(1)}
checks = []

def check(name, actual, expected):
    assert actual == expected, name
    checks.append(name)

km1 = add(x, scale(-1, one))
check('projection_norm_cross_multiplied',
      add(mul(km1, km1), km1), mul(x, km1))
disc = add(mul(x, x), scale(-1, mul(x, y)), mul(y, y))
mean = scale(F(1, 3), add(x, y))
centered = [scale(-1, mean), add(x, scale(-1, mean)),
            add(y, scale(-1, mean))]
norm2 = add(*(mul(v, v) for v in centered))
check('ordered_triple_norm_squared', norm2, scale(F(2, 3), disc))
check('ordered_triple_radius_squared', scale(F(1, 6), norm2),
      scale(F(1, 9), disc))
check('geometric_squared_difference', add(mul(y, y), scale(-1, disc)),
      mul(x, add(y, scale(-1, x))))
omx = add(one, scale(-1, x))
check('strict_bernoulli_k3_remainder',
      add(mul(mul(omx, omx), omx), scale(-1, one), scale(3, x)),
      mul(mul(x, x), add(scale(3, one), scale(-1, x))))
check('threshold_geometric_sum_k3', mul(omx, add(one, x, mul(x, x))),
      add(one, scale(-1, mul(mul(x, x), x))))
check('prime_factor_27', 3 ** 3, 27)
carry_value = 255 * 255 + 255 + 255
check('corrected_multiply_carry', (carry_value, divmod(carry_value, 256)),
      (65535, (255, 255)))
bits = 5 + (19).bit_length() * (15 + 4)
limbs = (bits + 7) // 8
check('fixed_window_capacity',
      (bits, limbs, 19 ** 16 < 2 ** bits,
       27 * 19 ** 19 < 2 ** bits <= 256 ** limbs), (100, 13, True, True))
decoded = [(1 + r // 3, r % 3) for r in range(18)]
expected = [(j, i) for j in range(1, 7) for i in range(3)]
check('stable_reflected_layout',
      (decoded == expected, len(set(decoded)),
       [7 + 3 * (j - 1) + i for j, i in decoded],
       7 + 3 * (2 - 1) + 0, 7 + 6 * (1 - 1) + (2 - 1)),
      (True, 18, list(range(7, 25)), 10, 8))
print(json.dumps({'status': 'passed', 'check_count': len(checks),
                  'checks': checks, 'candidate_search': False,
                  'kernel_execution': False}, sort_keys=True))
