#!/usr/bin/env python3
"""Exact certificate retaining one original-five test/deletion event.

Python 3.9+; standard library only. Run with -I -O. This checks the
finite arithmetic in the accompanying ordinary proof, not a Lean proof
or an enumeration of actual congruence families. All infinite tails
in the bounding formulae are evaluated by exact geometric identities.

The commit identifies the mathematical predecessor of the original eight inputs;
SHA-256 pins identify their current complete bytes. Two additional pins identify the uniform three-prime source,
which was not present at that predecessor commit. Mathematical validity
is imported from the corresponding ordinary proofs; hashes check source
identity, not those proofs.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from itertools import product
from functools import lru_cache
from math import prod, isqrt
from pathlib import Path
import argparse
import hashlib
import json
import sys


# shared_hinge mathematical operators.
ROOT = (0, 0, 1, 1, 1)
BASES = tuple((tuple((1 + int(ROOT[i] == r) + int(i == j) for i in range(5))) for r in range(2) for j in range(5)))
def ceilq(t):
    return -(-t.numerator // t.denominator)

def geom(p, n):
    z = F(1, p)
    m = z ** n / (1 - z)
    return (m, m * (n + z / (1 - z)), m * (n * n + 2 * n * z / (1 - z) + z * (1 + z) / (1 - z) ** 2))

def vertices():

    def sx(n, cap):
        return [(F(0),) * n] + [tuple((cap if k == j else F(0) for k in range(n))) for j in range(n)]
    return product(sx(5, F(1, 2)), sx(2, F(1, 4)), sx(5, F(1, 4)), sx(5, F(1, 72)), (F(3, 4), F(1)))

def data(par):
    deficit, al, be, late, z = par
    widths = tuple((1 - a for a in deficit))
    avail = tuple((z - al[ROOT[j]] - be[j] for j in range(5)))
    masses = tuple((widths[j] * avail[j] / 9 - late[j] for j in range(5)))
    pure = tuple((w / 9 for w in widths))
    rootmax = lambda a: max((sum((a[i] for i in range(5) if ROOT[i] == r)) for r in range(2)))
    s = sum(masses)
    cap = rootmax(masses) + max(masses) + max(avail) / 18 + sum(widths) / 36 + rootmax(widths) / 36 + max(widths) / 36 + F(1, 72)
    return (avail, masses, pure, s, s - cap / 5)

def cost(t, kind, n, x):
    h = lambda y: max(F(y) - t, F(0))
    if kind == 'h':
        return h(x)
    if kind == 'g':
        return h(n * x) / n - h(x)
    if kind == 'hn':
        return h(n * x)
    if kind == 'min':
        return min(F(x), t)
    if kind == 'id':
        return F(x)
    raise ValueError(kind)

@lru_cache(None)
def affine_terms(t, kind, n, b):
    initial = tuple((cost(t, kind, n, x) for x in b))
    cutoff = max(4, ceilq(t) + 4)
    terms = []
    for depth in range(3, cutoff):
        increments = tuple((max((cost(t, kind, n, k + 1) - cost(t, kind, n, k) for k in range(x, x + depth - 2))) for x in b))
        terms.append((F(1, 3 ** depth), increments))
    last = tuple((max((cost(t, kind, n, k + 1) - cost(t, kind, n, k) for k in range(x, x + cutoff - 2))) for x in b))
    following = tuple((max((cost(t, kind, n, k + 1) - cost(t, kind, n, k) for k in range(x, x + cutoff - 1))) for x in b))
    if last != following:
        raise ValueError('unstabilized affine increments')
    terms.append((geom(3, cutoff)[0], last))
    return (initial, tuple(terms))

@lru_cache(None)
def affine_deep(t, kind, n, b, avail):
    terms = affine_terms(t, kind, n, b)[1]
    return max(avail[j] * sum(w * row[j] for w, row in terms) for j in range(5))

def affine(t, kind, n, b, mass, avail):
    init, _ = affine_terms(t, kind, n, b)
    return sum((m * x for m, x in zip(mass, init))) + affine_deep(t, kind, n, b, avail)

ONES = (F(1),) * 5
@lru_cache(None)
def raw35(t, dat):
    return zero5_raw(('h', t), dat)

@lru_cache(None)
def raw357(t, dat):
    if t < 0:
        raise ValueError('negative hinge threshold')
    return zero7_raw(('h', t), dat)

@lru_cache(None)
def pmf(caps, cut):
    d = {1: F(1)}
    for p, c in caps:
        nxt = {}
        for a, m in d.items():
            for k in range(1, (cut - 1) // a + 1):
                prob = 1 - c / p if k == 1 else c * F(p - 1, p ** k)
                nxt[a * k] = nxt.get(a * k, F(0)) + m * prob
        d = nxt
    return d

@lru_cache(None)
def raw_ap_hinge(h, caps, dat):
    return ap_original_blocks_raw(('h', h), caps, dat)

def delta(dat):
    D = dat[4]
    return F(131, 132) * D - raw357(F(4), dat) / 6 - F(14, 99) * raw357(F(6), dat) - F(7, 132) * raw357(F(3), dat)


# joint_weighted mathematical operators.
G357 = F(5761, 159)
def rootceil(t):
    n = isqrt(t.numerator // t.denominator)
    return n + int(n * n < t)

def sh(t, v):
    return max(F(v * v) - t, F(0))

@lru_cache(None)
def sq_deep(t, b, avail):
    cut = max(3, rootceil(t) + 3)
    m0, m1, _ = geom(3, cut)
    return max(v * (sum(F(1, 3 ** a) *
        (sh(t, x + a - 2) - sh(t, x + a - 3)) for a in range(3, cut))
        + 2 * m1 + (2 * x - 5) * m0) for x, v in zip(b, avail))

def sq_value(t, b, mass, avail):
    return sum((m * sh(t, x) for m, x in zip(mass, b))) + sq_deep(t, b, avail)

@lru_cache(None)
def square35(t, dat):
    return zero5_raw(('s', t), dat)

@lru_cache(None)
def square357(t, dat):
    return zero7_raw(('s', t), dat)

CAP13 = ((11, F(5, 3)), (13, F(2)))
CAP17 = CAP13 + ((17, F(2)),)
PR16 = pmf(CAP13, 4)
TAIL0 = 1 - sum(PR16.values())
TAIL2 = F(253, 108) - sum((n * n * p for n, p in PR16.items()))
DCOEF = G357 * TAIL2 - 16 * TAIL0 + PR16[3] * 9 * (G357 - 1)
def square16num(dat):
    return DCOEF * dat[4] + sum((p * n * n * square357(F(16, n * n), dat) for n, p in PR16.items() if n != 3))


# row_potential mathematical operators.
W = F(403)
K = F(16)
def row_constants(p):
    a = F(3 * p - 1, (p - 1) ** 2)
    d = p - 9
    c = F(p - 1, d)
    k1 = F(p - 1, p - 2)
    return (a, d, c, k1)

@lru_cache(None)
def knots(p):
    a, d, c, k1 = row_constants(p)
    q = tuple((K * a * (F(p - 1, p - 1 - k) - k1) for k in range(1, 9)))
    slopes = [q[j + 1] - q[j] for j in range(7)] + [W / d]
    if not all((0 <= slopes[j] <= slopes[j + 1] for j in range(7))):
        raise ValueError('potential convexity')
    return q

def P(p, x):
    q = knots(p)
    d = p - 9
    if x >= 8:
        return q[-1] + W / d * (x - 8)
    k = x.numerator // x.denominator if isinstance(x, F) else int(x)
    if k < 1:
        raise ValueError('load below one')
    return q[k - 1] + (x - k) * (q[k] - q[k - 1])

P17 = F(15, 17)
GROW17 = F(89, 64)
PR17 = pmf(((17, F(2)),), 4)
CLOSS17 = sum((n * n * w for n, w in PR17.items() if n >= 2)) + 16 * (1 - sum(PR17.values()))
a17, d17, c17, k117 = row_constants(17)
a19, d19, c19, k119 = row_constants(19)
AC = a17 * c17 + a19 * c19 * GROW17
CONST = 16 * a17 * k117 + 16 * a19 * k119 * GROW17 + a19 * (c19 - k119) * (16 * (GROW17 - P17) - CLOSS17)

# whole_weighted mathematical operators.
def integer_features(p, n):
    cut = max(2, ceilq(F(8, n)))
    v = {j: P(p, n * j) for j in range(1, cut + 2)}
    co = {1: v[2] - v[1]}
    for j in range(2, cut + 1):
        co[j] = v[j + 1] - 2 * v[j] + v[j - 1]
    if min(co.values()) < 0:
        raise ValueError('positive integer feature coefficients')
    return (v[1], co)

def anchored(p):
    c, co = integer_features(p, 1)
    c += sum((co[j] * (5 - j) for j in range(1, 5)))
    co[5] += sum((co[j] for j in range(1, 5)))
    return (c, tuple(((j, co[j]) for j in range(5, 9))))

@lru_cache(None)
def wf(weights, x):
    return sum((c * max(F(x) - h, F(0)) for h, c in weights))

def wc(weights, n, kind, k, x):
    f = lambda v: wf(weights, n * v)
    a = sum((c for h, c in weights)) * n
    if kind == 'f':
        return f(x)
    if kind == 'g':
        return f(k * x) / k - f(x)
    if kind == 'scaled':
        return f(k * x)
    if kind == 'rest':
        return a * x - f(x)
    raise ValueError(kind)

@lru_cache(None)
def wt(weights, n, kind, k, b):
    f = lambda x: wc(weights, n, kind, k, x)
    initial = tuple((f(x) for x in b))
    cut = max(4, ceilq(F(max((h for h, c in weights)), n)) + 4)
    out = []
    for depth in range(3, cut):
        inc = tuple((max((f(j + 1) - f(j) for j in range(x, x + depth - 2))) for x in b))
        out.append((F(1, 3 ** depth), inc))
    inc = tuple((max((f(j + 1) - f(j) for j in range(x, x + cut - 2))) for x in b))
    inc2 = tuple((max((f(j + 1) - f(j) for j in range(x, x + cut - 1))) for x in b))
    if inc != inc2:
        raise ValueError('nonstabilized running increment')
    out.append((geom(3, cut)[0], inc))
    return (initial, tuple(out))

@lru_cache(None)
def wd(weights, n, kind, k, b, avail):
    terms = wt(weights,n,kind,k,b)[1]
    return max(avail[j] * sum(p*inc[j] for p,inc in terms) for j in range(5))

def wv(weights, n, kind, k, b, mass, avail):
    return sum((m * x for m, x in zip(mass, wt(weights, n, kind, k, b)[0]))) + wd(weights, n, kind, k, b, avail)

# The raw complete35 and pure3 measures see the same original zero-five
# ternary layout. On cell l their density ratio is at most avail[l].
# Centering at f(n) cancels the 1/n constants before summing all 5-depths.
@lru_cache(None)
def zero5_cost_metadata(tag):
    """Return degree, leading coefficient, constant, and polynomial cutoff."""
    kind, arg = tag
    if kind == 'h':
        return 1, F(1), -arg, max(2, ceilq(arg))
    if kind == 's':
        return 2, F(1), -arg, max(2, rootceil(arg))
    if kind == 'w':
        weights, dilation = arg
        return (1, sum(c for _, c in weights) * dilation,
                -sum(c * h for h, c in weights),
                max(2, ceilq(F(max(h for h, _ in weights), dilation))))
    if kind == 'scale':
        inner, dilation = arg
        degree, a, b, cutoff = zero5_cost_metadata(inner)
        return degree, a * dilation ** degree, b, cutoff
    if kind == 'zero7':
        degree, a, b, cutoff = zero5_cost_metadata(arg)
        tail = F(36, 5) * geom(7, cutoff)[degree - 1]
        leading = a * (sum(zero7_probability(n) * n ** (degree - 1)
                           for n in range(1, cutoff)) + tail)
        constant = (sum(zero7_probability(n) * (b - zero5_cost(arg, n)) / n
                        for n in range(1, cutoff)) - a * tail)
        return degree, leading, constant, cutoff
    if kind == 'seven_block':
        inner, block = arg
        degree, a, b, cutoff = zero5_cost_metadata(inner)
        tail = F(36, 5) * geom(7, cutoff)[degree - 1]
        leading = a * (sum(zero7_probability(n) * n ** (degree - 1)
                           for n in range(block + 1, cutoff)) + tail)
        constant = (sum(zero7_probability(n) * (b - zero5_cost(inner, n)) / n
                        for n in range(block + 1, cutoff)) - a * tail)
        return degree, leading, constant, cutoff
    if kind == 'zeroap':
        inner, caps = arg
        degree, a, b, cutoff = zero5_cost_metadata(inner)
        finite, tails = ap_product_distribution(caps, cutoff)
        leading = a * (sum(p * n ** (degree - 1) for n, p in finite.items())
                       + tails[degree - 1])
        constant = (sum(p * (b - zero5_cost(inner, n)) / n for n, p in finite.items())
                    - a * tails[degree - 1])
        return degree, leading, constant, cutoff
    if kind == 'ap_block':
        inner, caps, e, f = arg
        degree, a, b, cutoff = zero5_cost_metadata(inner)
        finite, active, tail = ap_block_record(caps, cutoff, degree, e, f)
        return (degree, a * active,
                sum(p * (b - zero5_cost(inner, n)) / n for n, p in finite) - a * tail,
                cutoff)
    raise ValueError('Unknown zero-five cost: ' + kind)

@lru_cache(None)
def zero5_cost(tag, v):
    kind, arg = tag
    if kind == 'h':
        return max(F(v) - arg, F(0))
    if kind == 's':
        return max(F(v * v) - arg, F(0))
    if kind == 'w':
        weights, dilation = arg
        return sum(c * max(F(dilation * v) - h, F(0)) for h, c in weights)
    if kind == 'scale':
        inner, dilation = arg
        return zero5_cost(inner, dilation * v)
    if kind == 'zero7':
        degree, a, _, cutoff = zero5_cost_metadata(arg)
        tail = F(36, 5) * geom(7, cutoff)[degree - 1]
        return (sum(zero7_probability(n) * (zero5_cost(arg, n * v) - zero5_cost(arg, n)) / n
                    for n in range(1, cutoff)) + a * tail * (v ** degree - 1))
    if kind == 'seven_block':
        inner, block = arg
        degree, a, _, cutoff = zero5_cost_metadata(inner)
        tail = F(36, 5) * geom(7, cutoff)[degree - 1]
        return (sum(zero7_probability(n) * (zero5_cost(inner, n * v) - zero5_cost(inner, n)) / n
                    for n in range(block + 1, cutoff)) + a * tail * (v ** degree - 1))
    if kind == 'zeroap':
        inner, caps = arg
        degree, a, _, cutoff = zero5_cost_metadata(inner)
        finite, tails = ap_product_distribution(caps, cutoff)
        return (sum(p * (zero5_cost(inner, n * v) - zero5_cost(inner, n)) / n
                    for n, p in finite.items()) + a * tails[degree - 1] * (v ** degree - 1))
    if kind == 'ap_block':
        inner, caps, e, f = arg
        degree, a, _, cutoff = zero5_cost_metadata(inner)
        finite, _, tail = ap_block_record(caps, cutoff, degree, e, f)
        return (sum(p * (zero5_cost(inner, n * v) - zero5_cost(inner, n)) / n
                    for n, p in finite) + a * tail * (v ** degree - 1))
    raise ValueError('Unknown zero-five cost: ' + kind)

@lru_cache(None)
def zero5_centered_correction(tag, v):
    degree, a, _, cutoff = zero5_cost_metadata(tag)
    tails = tuple(4 * z for z in geom(5, cutoff))
    return (sum(F(4, 5 ** n) * (zero5_cost(tag, n * v) - zero5_cost(tag, n)) / n
                for n in range(2, cutoff))
            + a * tails[degree - 1] * (v ** degree - 1) - zero5_cost(tag, v) / 5)

@lru_cache(None)
def zero5_common_deep(tag, baseline, availability):
    """One running increment maximum for both measures and every 5-depth."""
    degree, a, _, cutoff = zero5_cost_metadata(tag)
    current = F(0)
    total = F(0)
    i = 0
    def h(v):
        return availability * zero5_cost(tag, v) + zero5_centered_correction(tag, v)
    while True:
        increment = h(baseline + i + 1) - h(baseline + i)
        require(increment >= 0, 'Nonnegative common zero-five increment')
        current = max(current, increment)
        if baseline + i >= cutoff:
            if degree == 1:
                require(h(baseline + i + 2) - h(baseline + i + 1) == increment,
                        'Common zero-five affine tail')
                return total + current * geom(3, i + 3)[0]
            if current == increment:
                coefficient = a * (availability + F(1, 4))
                require(increment == coefficient * (2 * (baseline + i) + 1),
                        'Common zero-five square tail')
                z0, z1, _ = geom(3, i + 3)
                return total + coefficient * (2 * z1 + (2 * baseline - 5) * z0)
        total += F(1, 3 ** (i + 3)) * current
        i += 1
        # This guard refuses a result if the exact infinite-tail entry has
        # not been proved; it never substitutes a truncated depth sum.
        require(i <= 200, 'No proved common zero-five tail')

@lru_cache(None)
def zero5_convex_pure_deep(tag, n, baseline):
    """Full ternary tail for a new convex composite cost under pure3."""
    degree, a, _, cutoff = zero5_cost_metadata(tag)
    entry = max(0, ceilq(F(cutoff, n)) - baseline)
    total = sum(F(1, 3 ** (k + 3)) *
                (zero5_cost(tag, n * (baseline + k + 1)) - zero5_cost(tag, n * (baseline + k)))
                for k in range(entry))
    v = baseline + entry
    require(zero5_cost(tag, n * (v + 1)) - zero5_cost(tag, n * v)
            == a * n ** degree * ((v + 1) ** degree - v ** degree),
            'Composite convex pure-cost polynomial tail')
    z0, z1, _ = geom(3, entry + 3)
    if degree == 1:
        return total + a * n * z0
    return total + a * n * n * (2 * z1 + (2 * baseline - 5) * z0)

def zero5_scaled_pure(tag, n, baseline, pure):
    kind, arg = tag
    if kind == 'h':
        return affine(arg, 'hn', n, baseline, pure, ONES)
    if kind == 's':
        return n * n * sq_value(arg / (n * n), baseline, pure, ONES)
    if kind == 'w':
        weights, dilation = arg
        return wv(weights, dilation, 'scaled', n, baseline, pure, ONES)
    if kind == 'scale':
        inner, dilation = arg
        return zero5_scaled_pure(inner, n * dilation, baseline, pure)
    if kind in ('zero7', 'seven_block', 'zeroap', 'ap_block'):
        return (sum(w * zero5_cost(tag, n * b) for w, b in zip(pure, baseline))
                + max(zero5_convex_pure_deep(tag, n, b) for b in baseline))
    raise ValueError('Unknown zero-five cost: ' + kind)

@lru_cache(None)
def zero5_positive_with_constant(tag, pure):
    """The original positive-five comparison plus the exact x*J_f term."""
    degree, a, b, cutoff = zero5_cost_metadata(tag)
    x = sum(pure)
    answer = F(0)
    for n in range(2, cutoff):
        maximum = max((zero5_scaled_pure(tag, n, baseline, pure) - zero5_cost(tag, n) * x) / n
                      for baseline in BASES)
        answer += F(4 * (n - 1), 5 ** n) * maximum
    tails = tuple(4 * z for z in geom(5, cutoff))
    maximum = max((affine(F(0), 'id', 1, baseline, pure, ONES)
                   if degree == 1 else sq_value(F(0), baseline, pure, ONES))
                  for baseline in BASES)
    answer += a * (tails[degree] - tails[degree - 1]) * (maximum - x)
    constant = (sum(F(4, 5 ** n) * zero5_cost(tag, n) for n in range(2, cutoff))
                + a * tails[degree] + b * tails[0])
    return answer + x * constant

@lru_cache(None)
def zero5_raw(tag, dat):
    available, masses, pure, _, _ = dat
    answer = max(
        sum(masses[j] * zero5_cost(tag, baseline[j])
            + pure[j] * zero5_centered_correction(tag, baseline[j]) for j in range(5))
        + max(zero5_common_deep(tag, baseline[j], available[j]) for j in range(5))
        for baseline in BASES)
    return answer + zero5_positive_with_constant(tag, pure)

def zero7_probability(n):
    return F(29, 35) if n == 1 else F(36, 5 * 7 ** n)

@lru_cache(None)
def zero7_raw(tag, dat):
    """Retain every original seven block through its entire Jensen mixture.

    Q_e(v) = sum_(n>e) p_n [f(nv)-f(n)]/n is evaluated once per
    original block e. The complete e>=cutoff-1 tail is one exact
    nonnegative multiple of the monomial-minus-one source cost.
    """
    degree, a, b, cutoff = zero5_cost_metadata(tag)
    s = dat[3]
    tails = tuple(F(36, 5) * z for z in geom(7, cutoff))
    expectation = (sum(zero7_probability(n) * zero5_cost(tag, n) for n in range(1, cutoff))
                   + a * tails[degree] + b * tails[0])
    finite = sum(zero5_raw(('seven_block', (tag, e)), dat) for e in range(cutoff - 1))
    monomial = ('h', F(0)) if degree == 1 else ('s', F(0))
    tail_coefficient = a * (tails[degree] - (cutoff - 1) * tails[degree - 1])
    require(tail_coefficient >= 0, 'Nonnegative complete original-seven-block tail')
    return s * expectation + finite + tail_coefficient * (zero5_raw(monomial, dat) - s)

@lru_cache(None)
def ap_product_distribution(caps, cutoff):
    finite = pmf(caps, cutoff)
    full = (F(1), moment(caps, 1), moment(caps, 2))
    tails = tuple(full[j] - sum(p * n ** j for n, p in finite.items()) for j in range(3))
    require(min(tails) >= 0, 'Complete AP product-count moments')
    return finite, tails

@lru_cache(None)
def ap_active_moment(prime, cap, exponent, order):
    """E[1_(N>exponent) N^order], for order zero or one, without cutoff."""
    require(order in (0, 1), 'Original AP block uses moment zero or one')
    if exponent == 0:
        return F(1) if order == 0 else 1 + cap / F(prime - 1)
    probability = cap / prime ** exponent
    return probability if order == 0 else probability * (exponent + 1 + F(1, prime - 1))

def ap_count_probability(prime, cap, n):
    return 1 - cap / prime if n == 1 else cap / prime ** (n - 1) - cap / prime ** n

@lru_cache(None)
def ap_original_block_inputs(caps, cutoff, degree):
    require(caps == CAP13 and degree in (1, 2), 'Original AP11/13 source and polynomial degree')
    (p, cp), (q, cq) = caps
    records = []
    for e in range(cutoff - 1):
        for f in range(cutoff - 1):
            if (e + 1) * (f + 1) >= cutoff:
                continue
            finite = []
            for n in range(1, cutoff):
                probability = sum((ap_count_probability(p, cp, u) * ap_count_probability(q, cq, n // u)
                                   for u in range(1, n + 1)
                                   if n % u == 0 and u > e and n // u > f), F(0))
                if probability:
                    finite.append((n, probability))
            active = ap_active_moment(p, cp, e, degree - 1) * ap_active_moment(q, cq, f, degree - 1)
            tail = active - sum(probability * n ** (degree - 1) for n, probability in finite)
            require(tail >= 0, 'Complete active original AP block tail')
            records.append(((e, f), tuple(finite), active, tail))
    outside = moment(caps, degree) - sum(active for _, _, active, _ in records)
    require(outside >= 0, 'Complete complement of finite original AP block set')
    return tuple(records), outside

@lru_cache(None)
def ap_block_record(caps, cutoff, degree, e, f):
    for pair, finite, active, tail in ap_original_block_inputs(caps, cutoff, degree)[0]:
        if pair == (e, f):
            return finite, active, tail
    raise ValueError('AP block is outside the finite exceptional set')

@lru_cache(None)
def ap_original_blocks_raw(tag, caps, dat):
    """Collect each original (11,13) exponent tuple before its source maximum."""
    degree, a, b, cutoff = zero5_cost_metadata(tag)
    records, outside = ap_original_block_inputs(caps, cutoff, degree)
    finite, tails = ap_product_distribution(caps, cutoff)
    s = dat[3]
    expectation = (sum(p * zero5_cost(tag, n) for n, p in finite.items())
                   + a * tails[degree] + b * tails[0])
    common = sum(zero7_raw(('ap_block', (tag, caps, e, f)), dat)
                 for (e, f), _, _, _ in records)
    monomial = ('h', F(0)) if degree == 1 else ('s', F(0))
    return s * expectation + common + a * outside * (zero7_raw(monomial, dat) - s)

@lru_cache(None)
def w35(weights, n, dat):
    return zero5_raw(('w', (weights, n)), dat)

@lru_cache(None)
def w357(weights, n, dat):
    return zero7_raw(('w', (weights, n)), dat)

@lru_cache(None)
def w_ap_base(weights, caps):
    cut = max(2, max((h for h, c in weights)))
    pr = pmf(caps, cut)
    t0 = 1 - sum(pr.values())
    t1 = prod((1 + c / F(p - 1) for p, c in caps)) - sum((n * w for n, w in pr.items()))
    a = sum((c for h, c in weights))
    b = -sum((h * c for h, c in weights))
    return sum((w * wf(weights, n) for n, w in pr.items())) + a * t1 + b * t0

@lru_cache(None)
def w_ap(weights, caps, dat):
    raw = ap_original_blocks_raw(('w', (weights, 1)), caps, dat)
    floor = w_ap_base(weights, caps)
    require(raw >= floor * dat[3], 'Same-source AP centered remainder is nonnegative')
    return raw - floor * (dat[3] - dat[4])

ANCH17, WEIGHT17 = anchored(17)
ANCH19, WEIGHT19 = anchored(19)
EXTRA5 = F(403, 10) * (F(9, 8) - P17)
WHOLE_CONST = CONST + ANCH17 + P17 * ANCH19 + F(403, 10) * 5 * (F(9, 8) - P17) + (knots(19)[-1] - F(403 * 8, 10)) * (1 - P17)
W5 = ((5, F(1)),)


COMMIT = "343e9dcbdd69550d23c465807064738bbcf31a6f"
ORIGINAL_SOURCE_PINS = {'verify_shared_cell_hinges.py': 'f8ba06810c4552e5f6ec022d3762d615751407551ef6f4412bbb0490bb09ece9', 'verify_shared_cell_square.py': '9627bf255470676aec922813c031f2488c9433c7fa1326e735b4965d2ba89ca5', 'verify_joint_source_normalization.py': 'c52ef571da5dc9e6310d4081b85e6fca2786d7ca066cee8b1906abd01e6b3631', 'certificates/pure_root_profile_certificate.json': '64cca3231e75e3356eac5202196db65ecc03beca27bbe9d290d21c89b3960751', 'certificates/shared_cell_hinges_certificate.json': 'e5661edc37f4c133dd72f1ba51563908e8f02cc9cefa1ca15d319188591fc6ae', 'certificates/shared_cell_square_certificate.json': '100041c9cd4b668071ffb0c188aa622c1b59f1849481daab40d4b1349e50deef', 'certificates/shared_square_continuation_certificate.json': '1444a9203af13cee800c132187692747d5d29e30d46345fea367b803738be48e', 'certificates/joint_source_normalization_certificate.json': 'd0d5759ec857bdbe8376c593711c2f5f3273d115b134e87d0dc9be64ce5f01f1'}
SOURCE_PINS = {
    **ORIGINAL_SOURCE_PINS,
    'verify_uniform_gamma_cofactor_coupling.py': 'dee641ea80f6e3e94a18c1d57494381feb86ea93d275c070134b97a213a2843d',
    'certificates/uniform_gamma_cofactor_certificate.json': 'c443ac33dab710c3651c7785135e8b47f69511c3418727afec446b07934fff48',
}
TARGET=F(135235148346191272912644779662034152101019,301013392900945745723455169136921801600)
TARGET_GAMMA=F(2759803303859498317,17626016683279862)
TARGET_T81=F(40328059447468124566268231594828117,407273507000616495667817513124000)
BASELINE=F(118570862466538358475198684157361643465353,248352178520459750383083052623940732800)
OLD_CELL_BOUND=F(2322308771011317404407279020690922380203,4883651784640915381663610335586092800)
OLD_ZERO5_BOUND=F(12962561422729019748540463097645271562217,28539940401461137428522682187907859200)
OLD_ZERO7_BOUND=F(5323534511332833048109272786522049864207,11791742854906074667157193240441043200)
OLD_COMBINED_ZERO_AP_BOUND=F(20841391090341979866125382429441856802801,46309752753991653188223872174911046400)
OLD_ALL_AP_BOUND=F(270521516350366644094844875118567294436413,602026785801891491446910338273843603200)
OLD_YOUNG_BOUND=F(1081947977203541447444658369092299900073777,2408107143207565965787641353095374412800)
HC_TARGETS={3:F(1318076,584325),4:F(94745926,61354125),6:F(578163435166,676429228125)}
FALLBACK_INPUTS = (
    ('3-absent/5-absent/7-absent', (F(1), F(1), F(1)), F(756,373)),
    ('3-absent/5-absent/7-present', (F(1), F(1), F(6,7)), F(108,43)),
    ('3-absent/5-present/7-absent', (F(1), F(4,5), F(1)), F(1008,373)),
    ('3-absent/5-present/7-present', (F(1), F(4,5), F(6,7)), F(144,43)),
    ('9-absent-or-ineffective/5-absent/7-absent',
     (F(2,3), F(1), F(1)), F(18144,5371)),
    ('9-absent-or-ineffective/5-absent/7-present',
     (F(2,3), F(1), F(6,7)), F(12960,2993)),
    ('9-absent-or-ineffective/5-present/7-absent',
     (F(2,3), F(4,5), F(1)), F(3024,655)),
    ('9-absent-or-ineffective/5-present/7-present',
     (F(2,3), F(4,5), F(6,7)), F(432,73)),
)


def require(condition: bool, message: str) -> None:
    """Guards deliberately survive python -O."""
    if not condition:
        raise ValueError(message)


def encode(value):
    """Canonical JSON uses rational strings, never floating-point evidence."""
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def unique_json(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def moment(caps, order: int) -> F:
    if order == 1:
        return prod(1+c/F(p-1) for p,c in caps)
    if order == 2:
        return prod(1+c*F(3*p-1,(p-1)**2) for p,c in caps)
    raise ValueError('Only moments 1 and 2 are used.')


def product_hinge(caps, threshold: F) -> F:
    below = pmf(caps, max(2, ceilq(threshold)))
    return moment(caps,1)-threshold+sum(
        probability*max(threshold-n,F(0))
        for n,probability in below.items())


def product_square_hinge(caps, threshold: F) -> F:
    below = pmf(caps, max(2, rootceil(threshold)))
    return moment(caps,2)-threshold+sum(
        probability*max(threshold-n*n,F(0))
        for n,probability in below.items())


def arithmetic_self_checks() -> dict:
    for p in (3,5,7,11,13,17,19):
        for n in range(1,10):
            now, later = geom(p,n), geom(p,n+1)
            for order in (0,1,2):
                require(now[order]-later[order] == F(n**order,p**n),
                        'Geometric tail recurrence')
    require(moment(CAP13,1)==F(49,36), 'Complete AP13 mean')
    require(moment(CAP13,2)==F(253,108), 'Complete AP13 square')
    require(moment(((17,F(2)),),1)==F(9,8), 'Complete AP17 mean')
    require(moment(((17,F(2)),),2)==F(89,64), 'Complete AP17 square')
    require(AC==F(2371,2880), 'Joint square coefficient')
    require(CLOSS17==F(2496,4913), 'Full 17 tail unit-floor loss')
    require(CONST==F(63006107,7516890), 'Square-potential constant')
    require(EXTRA5==F(13299,1360), 'Complete positive-17 tail coefficient')
    require(WHOLE_CONST==F(185694867601,8599322160), 'Anchored constant')
    require(WEIGHT17==((5,F(5,11)),(6,F(10,99)),(7,F(5,36)),(8,F(3577,72))),
            'Whole 17 weighted cost')
    require(WEIGHT19==((5,F(112,351)),(6,F(224,3861)),
                       (7,F(112,1485)),(8,F(39449,990))),
            'Whole 19 weighted cost')
    for p,anchor,weights in ((17,ANCH17,WEIGHT17),(19,ANCH19,WEIGHT19)):
        require(all(c>=0 for _,c in weights), 'Convex weighted hinge cost')
        knots(p)  # Checks every exact slope, including the infinite affine tail.
        for x in range(1,11):
            require(P(p,x)<=anchor+wf(weights,x),'Integer anchor inequality')
        require(P(p,10)-P(p,9)==sum(c for _,c in weights),'Anchor tail slopes')
    for n in range(2,9):
        for x in range(1,10):
            require(P(19,n*x)<=P(19,5*n)+F(403*n,10)*max(x-5,0),
                    'Positive-17 multiplier anchor')
    return {'geometric_recurrences':7*9*3,
            'AP13_mean':moment(CAP13,1),'AP13_square':moment(CAP13,2),
            'AP17_mean':F(9,8),'AP17_square':GROW17,
            'unit_floor_loss17':CLOSS17,
            'potential_knots':{17:knots(17),19:knots(19)},
            'integer_anchors':{17:ANCH17,19:ANCH19}}



PR81=pmf(CAP13,9)
TAIL81_0=1-sum(PR81.values())
TAIL81_2=F(253,108)-sum(n*n*p for n,p in PR81.items())
CAP81_N={7,8}
DCOEF81=G357*TAIL81_2-81*TAIL81_0+sum(p*n*n*(G357-1) for n,p in PR81.items() if n in CAP81_N)
def square81num(dat):
    return DCOEF81*dat[4]+sum(p*n*n*square357(F(81,n*n),dat)
                             for n,p in PR81.items() if n not in CAP81_N)

def source_pins(directory):
    for name,pin in SOURCE_PINS.items():
        require(hashlib.sha256(read_artifact_bytes(directory/name)).hexdigest()==pin,
                'Pinned canonical mathematical input '+name)

def fallback_checks():
    rows=[]
    for name,u,density in FALLBACK_INPUTS:
        oldcaps=tuple((p,1/v) for p,v in zip((3,5,7),u))
        factor=density*prod(u)
        hs={h:factor*product_hinge(oldcaps,F(h)) for h in (3,4,6)}
        rho=F(131,132)-hs[4]/6-F(14,99)*hs[6]-F(7,132)*hs[3]
        require(rho>0,'Other branch actual surviving-mass bound')
        caps=oldcaps+CAP13
        hinges={h:factor*product_hinge(caps,F(h))/rho for h in (5,6,7,8)}
        # The global strengthened Gamma is valid on the other branches as checked below.
        value=WHOLE_CONST+AC*(TARGET_GAMMA-16)+sum(c*hinges[h] for h,c in WEIGHT17)
        value+=P17*sum(c*hinges[h] for h,c in WEIGHT19)+EXTRA5*hinges[5]
        source_square=lambda t:factor*product_square_hinge(oldcaps,t)
        u16=G357*TAIL2-16*TAIL0+sum(p*n*n*min(source_square(F(16,n*n)),G357-1) for n,p in PR16.items())
        u81=G357*TAIL81_2-81*TAIL81_0+sum(p*n*n*min(source_square(F(81,n*n)),G357-1) for n,p in PR81.items())
        require(16+u16/rho<=TARGET_GAMMA,'Other branch strengthened complete square')
        require(u81/rho<=TARGET_T81,'Other branch strengthened square hinge81')
        require(value<=TARGET,'Other branch strengthened joint frontier')
        rows.append({'branch':name,'reference_pure_masses':u,'Haar_density':density,
                     'source_hinges':hs,'survival_lower':rho,'supported_hinges':hinges,
                     'Gamma_upper':16+u16/rho,'T81_upper':u81/rho,'joint_upper':value,
                     'joint_margin':TARGET-value,'Gamma_margin':TARGET_GAMMA-16-u16/rho,
                     'T81_margin':TARGET_T81-u81/rho})
    require(len(rows)==8,'All other eight original branches')
    return rows

def reconstruct():
    checks=arithmetic_self_checks()
    rows=[];hcmax={h:F(0) for h in (3,4,6)}
    kZ=AC*DCOEF+w_ap_base(WEIGHT17,CAP13)+P17*w_ap_base(WEIGHT19,CAP13)+EXTRA5*w_ap_base(W5,CAP13)
    ef=kZ-AC*DCOEF
    for index,par in enumerate(vertices()):
        dat=data(par);available,masses,pure,s,D=dat;de=delta(dat)
        require(min(available)>=F(1,4) and min(masses)>=0 and D>0 and de>0,'Positive full source domain')
        hinges={h:raw357(F(h),dat)/D for h in (3,4,6)}
        for h in hcmax:hcmax[h]=max(hcmax[h],hinges[h])
        u16=square16num(dat);u81=square81num(dat)
        r17=w_ap(WEIGHT17,CAP13,dat);r19=w_ap(WEIGHT19,CAP13,dat);r5=w_ap(W5,CAP13,dat)
        require(r5==raw_ap_hinge(F(5),CAP13,dat)-w_ap_base(W5,CAP13)*(s-D),'Scalar versus weighted hinge identity')
        z=AC*u16+r17+P17*r19+EXTRA5*r5
        scalar={h:w_ap(((h,F(1)),),CAP13,dat) for h in (5,6,7,8)}
        split17=sum(c*scalar[h] for h,c in WEIGHT17);split19=sum(c*scalar[h] for h,c in WEIGHT19)
        require(split17>=r17 and split19>=r19,'Whole original-label weighted optimization')
        split=WHOLE_CONST+(AC*u16+split17+P17*split19+EXTRA5*r5)/de
        nofloor=WHOLE_CONST+(z+ef*(s-D))/de
        value=WHOLE_CONST+z/de;gamma=16+u16/de;t81=u81/de
        margin=(TARGET-WHOLE_CONST)*de-z
        mg=(TARGET_GAMMA-16)*de-u16;mt=TARGET_T81*de-u81
        require(min(margin,mg,mt)>=0,'All three exact vertex target margins at '+str(index))
        rows.append({'index':index,'parameters':par,'D':D,'Delta':de,'hinges':hinges,
                     'U16':u16,'U81':u81,'Gamma':gamma,'T81':t81,
                     'R17':r17,'R19':r19,'R5':r5,'Z':z,'value':value,'margin':margin,
                     'Gamma_margin':mg,'T81_margin':mt,'split_value':split,
                     'same_law_no_floor_value':nofloor,'raw_weighted_gain17':split17-r17,
                     'raw_weighted_gain19':split19-r19})
    require(len(rows)==1296,'Every product vertex')
    require(max(r['value'] for r in rows)==TARGET,'Attained exact strengthened frontier')
    require(max(r['Gamma'] for r in rows)==TARGET_GAMMA,'Attained exact strengthened square')
    require(max(r['T81'] for r in rows)==TARGET_T81,'Attained exact strengthened hinge81')
    require(rows[398]['value']==TARGET and rows[398]['Gamma']==TARGET_GAMMA,
            'Joint and complete-square maxima at vertex398')
    require(rows[386]['T81']==TARGET_T81 and rows[398]['T81']<TARGET_T81,
            'Threshold81 maximum at vertex386, distinct from vertex398')
    require(all(hcmax[h]<=HC_TARGETS[h] for h in hcmax),'Improved same-source HC observations')
    splitmax=max(r['split_value'] for r in rows);nofloormax=max(r['same_law_no_floor_value'] for r in rows)
    coeff=(TARGET-WHOLE_CONST)*F(131,132)-kZ
    cg=(TARGET_GAMMA-16)*F(131,132)-DCOEF;ct=TARGET_T81*F(131,132)-DCOEF81
    splitcoef=(splitmax-WHOLE_CONST)*F(131,132)-kZ
    nofloorcoef=(nofloormax-WHOLE_CONST)*F(131,132)-AC*DCOEF
    require(min(coeff,cg,ct,splitcoef,nofloorcoef)>0,'All continuous-domain coefficient conditions')
    branches=fallback_checks()
    require(all(r['joint_upper']<=splitmax and r['joint_upper']<=nofloormax for r in branches),'Comparison envelopes cover other branches')
    return encode({'schema':'erdos7-original-five-strip-deletion-frontier-v1','source_commit':COMMIT,
        'source_commit_scope':list(ORIGINAL_SOURCE_PINS),
        'source_provenance':'source_commit records the mathematical predecessor of source_commit_scope, not the current source bytes. source_sha256 binds every current Python source or fully reconstructed certificate byte sequence; certificate manifests additionally validate every part hash.',
        'source_sha256':SOURCE_PINS,'input19':'physical mu17=nu13 K17, distinct from killed xi',
        'bound':TARGET,'Gamma13':TARGET_GAMMA,'T13_81':TARGET_T81,
        'C0':WHOLE_CONST,'KZ':kZ,'continuous_coefficient':coeff,'Gamma_coefficient':cg,'T81_coefficient':ct,
        'DCOEF16':DCOEF,'DCOEF81':DCOEF81,'vertex_count':1296,'branch_count':12,'HC_maxima':hcmax,
        'maximizer_indices':{
            'bound':[r['index'] for r in rows if r['value']==TARGET],
            'Gamma13':[r['index'] for r in rows if r['Gamma']==TARGET_GAMMA],
            'T13_81':[r['index'] for r in rows if r['T81']==TARGET_T81]},
        'minimum_D':min(r['D'] for r in rows),'minimum_Delta':min(r['Delta'] for r in rows),
        'minimum_margin':min(r['margin'] for r in rows),'minimum_Gamma_margin':min(r['Gamma_margin'] for r in rows),
        'minimum_T81_margin':min(r['T81_margin'] for r in rows),
        'baseline_whole_bound':BASELINE,'old_cell_bound':OLD_CELL_BOUND,
        'gain_from_cell_consistency':BASELINE-OLD_CELL_BOUND,'common_zero5_gain':OLD_CELL_BOUND-OLD_ZERO5_BOUND,
        'old_zero5_bound':OLD_ZERO5_BOUND,'common_zero7_gain':OLD_ZERO5_BOUND-OLD_ZERO7_BOUND,
        'old_zero7_bound':OLD_ZERO7_BOUND,'common_seven_blocks_ap_gain':OLD_ZERO7_BOUND-OLD_COMBINED_ZERO_AP_BOUND,
        'old_combined_zero_ap_bound':OLD_COMBINED_ZERO_AP_BOUND,
        'common_ap_original_blocks_gain':OLD_COMBINED_ZERO_AP_BOUND-OLD_ALL_AP_BOUND,
        'old_all_ap_bound':OLD_ALL_AP_BOUND,'source_gain':OLD_ALL_AP_BOUND-OLD_YOUNG_BOUND,
        'old_young_bound':OLD_YOUNG_BOUND,'original5_strip_gain':OLD_YOUNG_BOUND-TARGET,'source_G357':G357,
        'same_cell_split_bound':splitmax,'same_cell_whole_weighted_gain':splitmax-TARGET,
        'same_cell_no_floor_bound':nofloormax,'same_law_floor_gain':nofloormax-TARGET,
        'split_continuous_coefficient':splitcoef,'no_floor_continuous_coefficient':nofloorcoef,
        'frontier_unequal':403-TARGET_T81-F(263,1000),
        'frontier_box20':403-TARGET_T81-F(667,1000000),
        'remaining_signed_upper':TARGET_T81-403+TARGET,
        'checks':checks,'other_eight_branches':branches,'rows':rows,
        'scope':'All original finite heights/residues/missing classes through19 on unchanged actual AP law; ordinary proof and exact certificates, not Lean or unrestricted resolution'})

def main():
    base=Path(__file__).resolve().parent
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-directory',type=Path,default=(base/'sources' if (base/'sources').is_dir() else base))
    parser.add_argument('--certificate',type=Path,default=base/'certificates/joint_frontier_certificate.json')
    mode=parser.add_mutually_exclusive_group()
    mode.add_argument('--write',action='store_true',help='Regenerate the single complete exact certificate.')
    mode.add_argument('--check',action='store_true',help='Reconstruct and compare; this is also the default.')
    args=parser.parse_args();source_pins(args.source_directory);result=reconstruct()
    if args.write:write_certificate_text(args.certificate, json.dumps(result,indent=2)+'\n', encoding='utf-8')
    else:require(json.loads(read_artifact_text(args.certificate),object_pairs_hook=unique_json)==result,'Entire single certificate, all1296 case records and8 branches')
    print('PASS: independently reconstructed1296 vertices, all12 branches, complete tails and source pins.')
    print('Joint bound '+str(TARGET)+' = '+str(float(TARGET)))
    print('Gamma13 '+str(float(TARGET_GAMMA))+'; T13(81) '+str(float(TARGET_T81)))
    print('Unrestricted endpoint and later-prime continuation remain open.')
if __name__=='__main__':
    try:main()
    except (ValueError,OSError,json.JSONDecodeError) as error:
        print('FAIL: '+str(error),file=sys.stderr);sys.exit(1)
