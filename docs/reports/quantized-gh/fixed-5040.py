"""Fixed S21 proof inputs, one box and 71 theorem slots; no candidate search."""
import hashlib
import importlib.metadata
import json
import platform
import sys
from collections import Counter
from fractions import Fraction
from math import prod
from pathlib import Path

import flint
from flint import arb, ctx, fmpq

ctx.prec = 256
checks = Counter()


def require(category, condition):
    if not condition:
        raise AssertionError(category)
    checks[category] += 1


def q(value):
    value = Fraction(value)
    return arb(fmpq(value.numerator, value.denominator))


def f(value):
    return (1 - (-value).exp()).log()


def enclosed(category, value, lower, upper):
    require(category, q(Fraction(lower, SCALE)) < value < q(Fraction(upper, SCALE)))


PRIMES = (2, 3, 5, 7)
EXPONENTS = (4, 2, 1, 1)
LOWER = (32, 27, 25, 49)
UPPER = (64, 81, 125, 343)
A_PRODUCT = 1058400
SCALE = 10**12
CORNERS = ((1, 0), (2, 1), (3, 2), (5, 4), (6, 3), (7, 8),
           (10, 5), (14, 9), (15, 6), (21, 10), (30, 7), (35, 12),
           (42, 11), (70, 13), (105, 14), (210, 15))
CAPACITIES = (1, 2, 6, 30, 210)
DENSITY_BINS = ((23083613113, 23083613114), (23045261959, 23045261960),
                (20373462417, 20373462418), (9095783332, 9095783333))
# slot, D lower/upper, Psi lower/upper, G lower/upper, all divided by SCALE.
NODE_BINS = (
    (1, -105585917043, -105585917042, -99815050712, -99815050711, -5770866331, -5770866330),
    (2, -93813806727, -93813806726, -89539949332, -89539949331, -4273857395, -4273857394),
    (3, -89612158690, -89612158689, -86872489407, -86872489406, -2739669284, -2739669283),
    (4, -86471575608, -86471575607, -83626367313, -83626367312, -2845208295, -2845208294),
    (5, -79204872042, -79204872041, -76118124932, -76118124931, -3086747110, -3086747109),
    (6, -72349767575, -72349767574, -69265007491, -69265007490, -3084760085, -3084760084),
    (7, -70944143900, -70944143899, -68063358972, -68063358971, -2880784928, -2880784927),
    (8, -64089039433, -64089039432, -61684687124, -61684687123, -2404352309, -2404352308),
    (9, -56822335867, -56822335866, -56001298703, -56001298702, -821037164, -821037163),
    (10, -55420214683, -55420214682, -54127825653, -54127825652, -1292389030, -1292389029),
    (11, -53761857306, -53761857305, -51730182731, -51730182730, -2031674576, -2031674575),
    (12, -49115498111, -49115498110, -45360861267, -45360861266, -3754636845, -3754636844),
    (13, -45427475339, -45427475338, -41767225027, -41767225026, -3660250313, -3660250312),
    (14, -39122758768, -39122758767, -35851557046, -35851557045, -3271201722, -3271201721),
    (23, -92756306669, -92756306668, -88503048096, -88503048095, -4253258574, -4253258573),
    (37, -75217271566, -75217271565, -72158981090, -72158981089, -3058290477, -3058290476),
)
FIRST_FAILED = {
    1: (15, 16, 17, 18),
    2: (22, 26, 30),
    3: (27, 28, 31, 32, 35, 36, 39, 40, 41, 43, 44, 45, 47, 48, 49,
        51, 52, 53, 55, 56, 57, 59, 60, 61, 63, 64, 65, 67, 68, 69),
    4: (),
    5: (19, 20, 21, 24, 25, 29, 33, 34, 38, 42, 46, 50, 54, 58, 62, 66, 70),
}
require('runtime_pin', importlib.metadata.version('python-flint') == '0.8.0')
require('runtime_pin', ctx.prec == 256)
require('fixed_box_identity', prod(p**b for p, b in zip(PRIMES, EXPONENTS)) == 5040)
require('fixed_box_identity', prod(PRIMES) == 210)
require('fixed_box_identity', tuple(p**(b+1) for p, b in zip(PRIMES, EXPONENTS)) == LOWER)
require('fixed_box_identity', tuple(p**(b+2) for p, b in zip(PRIMES, EXPONENTS)) == UPPER)
require('fixed_box_identity', prod(LOWER) == A_PRODUCT == 5040 * 210)
require('fixed_box_identity', CAPACITIES == tuple(prod(PRIMES[:i]) for i in range(5)))
for multiplier, mask in CORNERS:
    require('corner_identity', multiplier == prod(PRIMES[i] for i in range(4) if mask >> i & 1))
require('corner_order', len({m for _, m in CORNERS}) == 16)
require('corner_order', all(CORNERS[i][0] < CORNERS[i+1][0] for i in range(15)))

integers = [5040 * multiplier for multiplier, _ in CORNERS]
nodes = {}
raw = []
for slot in range(15):
    active = integers[slot] > 5040
    require('adjacent_eligibility', active == (slot > 0))
    raw.append((slot, [active]))
    if active:
        nodes[slot] = (Fraction(210 * integers[slot]), Fraction(210 * integers[slot+1]))
failed = {slot: guard for guard, slots in FIRST_FAILED.items() for slot in slots}
require('reflection_partition', len(failed) == sum(map(len, FIRST_FAILED.values())) == 54)
for j in range(1, 15):
    a, middle, upper = integers[j-1:j+2]
    X = 210 * a
    for i, (p, b) in enumerate(zip(PRIMES, EXPONENTS)):
        slot = 15 + 4 * (j-1) + i
        E = p**(4 * (2*b+3))
        guards = (a > 5040, p**(4*(b+1)) < X, X*X < E,
                  210**2 * a * middle < E, E < 210**2 * a * upper)
        first = next((g for g, ok in enumerate(guards, 1) if not ok), 0)
        require('reflected_eligibility', first == failed.get(slot, 0))
        raw.append((slot, guards))
        if all(guards):
            nodes[slot] = (Fraction(X), Fraction(E, X))
require('complete_raw_partition', [s for s, _ in raw] == list(range(71)))
require('complete_raw_partition', list(nodes) == list(range(1, 15)) + [23, 37])
require('reflected_endpoint_link', nodes[23] == (3175200, Fraction(17592186044416, 3175200)))
require('reflected_endpoint_link', nodes[37] == (7408800, Fraction(95367431640625, 7408800)))
require('reflected_endpoint_link', nodes[23][1]/210 == Fraction(274877906944, 10418625))
require('reflected_endpoint_link', nodes[37][1]/210 == Fraction(762939453125, 12446784))

h = [arb(p).log() for p in PRIMES]
c = [(b+1)*hi for b, hi in zip(EXPONENTS, h)]
d = [(b+2)*hi for b, hi in zip(EXPONENTS, h)]
fc = [q(Fraction(n-1, n)).log() for n in LOWER]
fd = [q(Fraction(n-1, n)).log() for n in UPPER]
gain = [upper-lower for lower, upper in zip(fc, fd)]
density = [v/hi for v, hi in zip(gain, h)]
for value, (lower, upper) in zip(density, DENSITY_BINS):
    enclosed('density_enclosure', value, lower, upper)
require('density_order', density[0] > density[1] > density[2] > density[3] > 0)
expected = {row[0]: row[1:] for row in NODE_BINS}
require('node_table_identity', set(expected) == set(nodes) and len(NODE_BINS) == 16)
values = {}
rows = []
for slot, (lower_product, upper_product) in nodes.items():
    lo, hi = q(lower_product).log(), q(upper_product).log()
    mu = hi/4
    distances = [(ci-mu).max(lo/4-ci).max(0).min((di-mu).max(lo/4-di).max(0))
                 for ci, di in zip(c, d)]
    radius = (sum(delta*delta for delta in distances)/12).sqrt()
    L, H = mu-radius, mu+3*radius
    require('fixed_support_range', 0 < L < 16)
    require('fixed_support_range', 0 < H < 16)
    psi = f(H) + 3*f(L)
    t = upper_product/A_PRODUCT
    if t == 210:
        D, price, y = sum(fd), arb(0), [arb(1)]*4
    else:
        index = next(i for i in range(4) if CAPACITIES[i] <= t < CAPACITIES[i+1])
        y = [arb(1) if i < index else q(t/CAPACITIES[index]).log()/h[index]
             if i == index else arb(0) for i in range(4)]
        D = sum(fc) + sum(v*yi for v, yi in zip(gain, y))
        price = density[index]
    dual = sum(fc) + price*q(t).log() + sum((v-price*hi_).max(0) for v, hi_ in zip(gain, h))
    require('primal_dual_overlap', (D-dual).contains(0))
    require('capacity_identity_overlap', (sum(hi_*yi for hi_, yi in zip(h, y))-q(t).log()).contains(0))
    G = D-psi
    for value, lower, upper in zip((D, psi, G), expected[slot][::2], expected[slot][1::2]):
        enclosed('node_enclosure', value, lower, upper)
    require('fixed_node_margin', G < -q(Fraction(1, 1250)))
    values[slot] = (D, psi, G, distances)
    rows.append({'slot': slot, 'shifted_endpoint_products': [str(lower_product), str(upper_product)],
                 'closed_mesh_enclosures': expected[slot]})

for slot in nodes:
    if slot != 9:
        require('unique_retained_maximizer', values[9][2] > values[slot][2])
X, Y = 22226400, 31752000
require('maximizer_branch_integer_link', X > 64**4)
for i in (1, 2, 3):
    require('maximizer_branch_integer_link', LOWER[i]**4 < X)
    require('maximizer_branch_integer_link', Y < UPPER[i]**4)
    switch_product = (LOWER[i]*UPPER[i])**4
    require('maximizer_branch_integer_link', X*Y > switch_product if i in (1, 2) else X*Y < switch_product)
alpha, omega = arb(X).log(), arb(Y).log()
branches = [(alpha-24*h[0])/4, (16*h[1]-omega)/4,
            (12*h[2]-omega)/4, (alpha-8*h[3])/4]
for a, b in zip(branches, values[9][3]):
    require('maximizer_branch_positive', a > 0)
    require('maximizer_branch_overlap', (a-b).contains(0))
require('exact_greedy_value', prod(Fraction(n-1, n) for n in (64, 81, 125, 49)) == Fraction(496, 525))
require('exact_greedy_value_overlap', (values[9][0]-q(Fraction(496, 525)).log()).contains(0))
require('legacy_budget_shift', Fraction(X, 210) == 105840)
require('legacy_budget_shift', Fraction(Y, 210) == 151200)
require('rational_margin', Fraction(-821037163, SCALE) < Fraction(-1, 1250))
require('erratum_rational_identity', Fraction(2, 129*3**129)/Fraction(8, 9) == Fraction(9, 4*129*3**129))
program = Path(__file__).read_bytes()
print(json.dumps({
    'status': 'passed', 'python_version': platform.python_version(), 'sys_version': sys.version,
    'python_implementation': platform.python_implementation(), 'python_executable': sys.executable,
    'python_flint_version': importlib.metadata.version('python-flint'),
    'flint_module_version': flint.__version__,
    'flint_library_version': getattr(flint, '__FLINT_VERSION__', getattr(flint, '__flint_version__', None)),
    'precision_bits': ctx.prec,
    'program_sha256': hashlib.sha256(program).hexdigest(), 'program_bytes': len(program),
    'program_lf': program.count(b'\n'), 'checks_by_category': dict(checks),
    'checks_total': sum(checks.values()), 'fixed_boxes': 1, 'raw_slots': 71,
    'active_adjacent_slots': list(range(1, 15)), 'active_reflected_slots': [23, 37],
    'inactive_slots': 55, 'inactive_reflected_by_first_failed_guard': FIRST_FAILED,
    'density_interval_numerators': DENSITY_BINS, 'density_intervals_verified': 4,
    'node_intervals_verified': 48, 'interval_denominator': SCALE, 'rows': rows,
    'unique_retained_maximizer': 9, 'maximum_interval_numerators': [-821037164, -821037163],
    'candidate_boxes_generated': 0, 'GPU_dispatches': 0, 'original_program_executions': 0,
    'proof_boundary': 'Fixed input and rounding certificate only. Continuous-domain coverage, exact primal/price equality and all-real uniqueness require the paper proof; interval overlap alone proves no identity.'
}, sort_keys=True, indent=2))
