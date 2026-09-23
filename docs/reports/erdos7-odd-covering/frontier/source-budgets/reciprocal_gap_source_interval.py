#!/usr/bin/env python3
"""Exactly enclose Filaseta–Kalogirou arXiv:2407.15280v1 equation (24).

The original fixed N is evaluated at Delta=1/12 and, for all-odd nonunit
original moduli, at Delta=1/2. A separate N=1000000000 calculation uses
the odd-only prefix coefficient M_p/2, its square-root comparison with
the full prefix product, and removal of the q=2 fourth-moment factor 150
from the published tail proof.

The source Lemmas 1–2 and prime bound (23) are external inputs. Their
large finite prime products are not reproduced here. The source page-24
Euler-product bound <94 is another explicit input to the final rational
bridge. This program neither verifies the generalized leakage recurrence
nor constitutes a Lean proof of an unrestricted covering theorem.

Logarithms use the atanh series with a geometric remainder; exponentials
use a range-reduced Taylor series with a uniform remainder. Every interval
operation rounds outward to a fixed dyadic grid using integer arithmetic.
Decimal strings are display only. The fixed computation writes JSON to
standard output and creates no files.
"""

from fractions import Fraction as F
from math import factorial
from decimal import Decimal, localcontext
import json
from functools import lru_cache


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


BITS = 384
SCALE = 1 << BITS
LN_TERMS = 120
EXP_TERMS = 80


def down(x):
    return F((x.numerator * SCALE) // x.denominator, SCALE)


def up(x):
    return F(-((-x.numerator * SCALE) // x.denominator), SCALE)


class Interval:
    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = self.lo if hi is None else F(hi)
        require(self.lo <= self.hi, 'Failed exact check: self.lo <= self.hi')

    def rounded(self):
        return Interval(down(self.lo), up(self.hi))

    @staticmethod
    def coerce(other):
        return other if isinstance(other, Interval) else Interval(other)

    def __add__(self, other):
        other = self.coerce(other)
        return Interval(self.lo + other.lo, self.hi + other.hi).rounded()

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        ends = [a * b for a in (self.lo, self.hi)
                for b in (other.lo, other.hi)]
        return Interval(min(ends), max(ends)).rounded()

    __rmul__ = __mul__

    def reciprocal(self):
        require(self.lo * self.hi > 0, 'Failed exact check: self.lo * self.hi > 0')
        return Interval(1 / self.hi, 1 / self.lo).rounded()

    def __truediv__(self, other):
        return self * self.coerce(other).reciprocal()

    def __rtruediv__(self, other):
        return self.coerce(other) / self

    def __pow__(self, power):
        require(isinstance(power, int) and power >= 0, 'Failed exact check: isinstance(power, int) and power >= 0')
        out = Interval(1)
        for _ in range(power):
            out = out * self
        return out


def small_log(y):
    """ln(y), 1 <= y <= 2, by the atanh series and a geometric tail."""
    y = F(y)
    require(1 <= y <= 2, 'Failed exact check: 1 <= y <= 2')
    z = Interval((y - 1) / (y + 1)).rounded()
    z2 = z * z
    power = z
    total = Interval(0)
    for k in range(LN_TERMS):
        total = total + power / (2 * k + 1)
        power = power * z2
    # Exact z <= 1/3. The tail begins at exponent 2*LN_TERMS+1.
    tail = 2 * F(1, 3) ** (2 * LN_TERMS + 1)
    tail /= (2 * LN_TERMS + 1) * (1 - F(1, 9))
    return 2 * total + Interval(0, tail)


@lru_cache(None)
def log_two():
    return small_log(2)


def log_scalar(x):
    x = F(x)
    require(x > 0, 'Failed exact check: x > 0')
    k = x.numerator.bit_length() - x.denominator.bit_length()
    unit = F(2) ** k
    while x < unit:
        k -= 1
        unit /= 2
    while x >= 2 * unit:
        k += 1
        unit *= 2
    return k * log_two() + small_log(x / unit)


def log_interval(x):
    x = Interval.coerce(x)
    return Interval(log_scalar(x.lo).lo, log_scalar(x.hi).hi)


def exp_scalar(x):
    x = F(x)
    if x < 0:
        return exp_scalar(-x).reciprocal()
    divisions = 0
    while x > F(1, 2):
        x /= 2
        divisions += 1
    term = total = Interval(1)
    for k in range(1, EXP_TERMS + 1):
        term = term * x / k
        total = total + term
    # e^(1/2) < 2 gives this uniform Taylor remainder bound.
    tail = 2 * F(1, 2) ** (EXP_TERMS + 1) / factorial(EXP_TERMS + 1)
    total = total + Interval(0, tail)
    for _ in range(divisions):
        total = total * total
    return total


def exp_interval(x):
    x = Interval.coerce(x)
    return Interval(exp_scalar(x.lo).lo, exp_scalar(x.hi).hi)


def decimal(x):
    with localcontext() as ctx:
        ctx.prec = 55
        return str(Decimal(x.numerator) / Decimal(x.denominator))


def encode(x):
    return {'lower': str(x.lo), 'upper': str(x.hi),
            'lower_decimal_display_only': decimal(x.lo),
            'upper_decimal_display_only': decimal(x.hi)}


def odd_only_prefix_reserve():
    """Enclose the odd-only prefix reserve using source Lemmas 1 and 2.

    The lower prefix bound decreases with p, as does the tail upper bound
    once log(p)>16/3. Thus they use the upper and lower prime bounds,
    respectively. The coefficient 46 follows from half of the cited
    full Euler product <94, minus one; it is valid at this smaller N.
    """
    N = 1000000000
    source_product_N = 1532030200000000000000
    require(10**9 <= N <= source_product_N,
            'Odd-only N satisfies both published source ranges')
    ln_N = log_interval(N)
    ln_ln_N = log_interval(ln_N)
    prime_lower = N * (ln_N + ln_ln_N - F(3, 2))
    prime_upper = N * (ln_N + ln_ln_N - F(1, 2))
    log_lower = log_interval(prime_lower)
    log_upper = log_interval(prime_upper)
    require(log_lower.lo > F(16, 3), 'Tail envelope is decreasing')
    a, b = F('0.8913191'), F('1.7826381')
    require(b - a / log_lower.lo**2 > 0,
            'Prefix envelope is decreasing')
    prefix = F(1, 2) * exp_interval(
        (log_interval(F('3.84636486599'))
         - b * log_upper - a / log_upper) / 2)
    # FK (6)--(9) on odd cofactors omits the q=2=p_1 factor. With delta_1=0
    # that factor is exactly 150; its removal propagates through (18)--(21)
    # and the positive tail summation. This is a proof input, not an
    # inference obtained by dividing the conclusion of Lemma 1 alone.
    factor_two = 1 + F(15*2**3 + 5*2**2 + 5*2 - 1, (2-1)**4)
    require(factor_two == 150, 'Omitted even-prime fourth-moment factor')
    tail = F('0.657743') * log_lower**16 / (factor_two * prime_lower**3)
    reserve = prefix - tail
    overlap_lower = reserve.lo / 46
    union_lower = overlap_lower / (N - 3)
    require(reserve.lo > 0, 'Odd-only prefix reserve exceeds the odd-only tail')
    require(overlap_lower > F(1, 10**11),
            'Minimal-bucket overlap is strictly greater than 1e-11')
    require(union_lower > F(1, 10**20),
            'Union of these original overlaps has mass greater than 1e-20')
    require(prime_upper.hi < 25 * 10**9,
            'Every prime in the localized overlap lies below 25000000000')
    return {
        'N': N,
        'source_product_N': source_product_N,
        'omitted_fourth_moment_factor': str(factor_two),
        'prime_lower': encode(prime_lower),
        'prime_upper': encode(prime_upper),
        'prefix_reserve_lower_envelope': encode(prefix),
        'tail_upper_envelope': encode(tail),
        'reserve_minus_tail': encode(reserve),
        'overlap_coefficient_strict_upper': 46,
        'minimal_bucket_overlap_strict_lower': str(overlap_lower),
        'minimal_bucket_overlap_lower_decimal_display_only': decimal(overlap_lower),
        'minimal_bucket_overlap_exceeds_10_to_minus_11': True,
        'original_overlap_union_strict_lower': str(union_lower),
        'original_overlap_union_lower_decimal_display_only': decimal(union_lower),
        'original_overlap_union_exceeds_10_to_minus_20': True,
        'localized_prime_strict_upper': 25 * 10**9,
    }


def main():
    N = 1532030200000000000000
    require(N == F('1.5320302') * 10 ** 21 and N >= 10 ** 9, "Failed exact check: N == F('1.5320302') * 10 ** 21 and N >= 10 ** 9")
    delta = F(95007347, 1520117553)
    require(0 < delta <= F(1, 2), 'Failed exact check: 0 < delta <= F(1, 2)')

    # Source equation (23), valid for every integer n >= 20.
    ln_N = log_interval(N)
    ln_ln_N = log_interval(ln_N)
    tau1 = N * (ln_N + ln_ln_N - F(3, 2))
    tau2 = N * (ln_N + ln_ln_N - F(1, 2))
    ln_tau1 = log_interval(tau1)
    ln_tau2 = log_interval(tau2)
    f_tau1 = (F('5.8478233') / 12
              * exp_interval(F('1.2173619') * ln_tau1)
              * exp_interval(-F('0.8913191') / ln_tau1)
              / ln_tau1 ** 16)
    prefactor = F('0.657743') * ln_tau2 ** 16 / tau2 ** 3
    equation24 = prefactor * (f_tau1 - 1)
    source_margin = F('4.7596769') / 10 ** 50
    require(equation24.lo > source_margin, 'Failed exact check: equation24.lo > source_margin')

    # Section 6 starts with arbitrary Delta>0. Its f is linear in Delta;
    # odd distinct nonunit moduli have actual Delta>1/2. N stays fixed.
    odd_equation24 = prefactor * (6 * f_tau1 - 1)
    odd_Hcov_lower = odd_equation24.lo / 93
    require(odd_Hcov_lower > F(2, 10 ** 43),
            'Failed exact check: odd_Hcov_lower > 2e-43')

    # Independent rational witnesses for the coarse prime bound.
    exp50_partial = sum((F(50) ** k / factorial(k) for k in range(51)), F(0))
    exp4_partial = sum((F(4) ** k / factorial(k) for k in range(8)), F(0))
    require(exp50_partial > N, 'Failed exact check: exp50_partial > N')
    require(exp4_partial > 50, 'Failed exact check: exp4_partial > 50')
    prime_upper = F(107, 2) * N
    require(prime_upper < 10 ** 23, 'Failed exact check: prime_upper < 10 ** 23')
    require(source_margin / 10 ** 23 > F(1, 10 ** 73), 'Failed exact check: source_margin / 10 ** 23 > F(1, 10 ** 73)')
    require(source_margin / 93 > F(5, 10 ** 52), 'Failed exact check: source_margin / 93 > F(5, 10 ** 52)')

    report = {
        'scope': 'Exact rational validation of FK v1 equation (24), the odd-only prefix/tail comparison, and arithmetic bridges. Conditional on source Lemmas 1–2, the odd restriction of the fourth-moment proof (6)–(21), equation (23), and the page-24 Euler-product bound <94. The leakage recurrences and source prime products are not checked here.',
        'N': N,
        'distortion_delta': str(delta),
        'dyadic_bits': BITS,
        'log_series_terms': LN_TERMS,
        'exp_series_terms': EXP_TERMS,
        'log_N': encode(ln_N),
        'log_log_N': encode(ln_ln_N),
        'tau1': encode(tau1),
        'tau2': encode(tau2),
        'f_tau1': encode(f_tau1),
        'equation24': encode(equation24),
        'odd_equation24_Delta_one_half': encode(odd_equation24),
        'source_lemma3_margin': str(source_margin),
        'equation24_exceeds_source_margin': True,
        'exp50_partial': str(exp50_partial),
        'exp4_partial': str(exp4_partial),
        'prime_upper_from_log_bounds': str(prime_upper),
        'prime_upper_below_10_to_23': True,
        'conditional_Hcov_strict_lower_bound': str(source_margin / 10 ** 23),
        'conditional_Hcov_exceeds_10_to_minus_73': True,
        'source_page24_Euler_product_strict_upper': 94,
        'conditional_Hcov_with_source_Euler_bound': str(source_margin / 93),
        'conditional_Hcov_exceeds_5_times_10_to_minus_52': True,
        'conditional_odd_Hcov_strict_lower_bound': str(odd_Hcov_lower),
        'conditional_odd_Hcov_lower_decimal_display_only': decimal(odd_Hcov_lower),
        'conditional_odd_Hcov_exceeds_2_times_10_to_minus_43': True,
        'odd_only_prefix': odd_only_prefix_reserve(),
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
