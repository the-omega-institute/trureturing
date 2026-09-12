# S19_FIXED_CERTIFICATE_V1
"""Self-contained fixed (2,3,5) proof certificate; no candidate inputs."""
from fractions import Fraction as F
from math import factorial
import json
import platform
import sys

if len(sys.argv) != 1:
    raise SystemExit("This fixed certificate accepts no candidate parameters")
checks = []


def check(name, result):
    checks.append({"name": name, "passed": bool(result)})
    if not result:
        raise AssertionError(name)


proof = {'atom_bound_certificate': {'exponential_certificates': {'rule': 'Write P_N(x)=sum from k=0 to N '
                                                                 'of x^k/k!. For x>0, '
                                                                 'exp(x)>P_N(x). Each following '
                                                                 'triple (x,N,target) satisfies '
                                                                 'the exact rational inequality '
                                                                 'P_N(x)>target.',
                                                         'triples': [['19/100', 2, '6/5'],
                                                                     ['2/3', 2, '15/8'],
                                                                     ['3/10', 3, '4/3'],
                                                                     ['19/20', 3, '5/2'],
                                                                     ['29/100', 3, '4/3'],
                                                                     ['7/6', 5, '16/5'],
                                                                     ['12/25', 3, '8/5'],
                                                                     ['13/10', 4, '7/2'],
                                                                     ['3/5', 3, '9/5'],
                                                                     ['3/2', 5, '40/9'],
                                                                     ['23/25', 4, '5/2'],
                                                                     ['31/20', 5, '14/3'],
                                                                     ['3/4', 3, '2']]}},
 'rational_majorization_certificate': {'rows': [{'node': 'j=1',
                                                 'l': '4/5',
                                                 'h': '4/5',
                                                 'w': '5/2',
                                                 'k': '2',
                                                 'w_minus_2l_minus_h': '1/10'},
                                                {'node': 'j=2',
                                                 'l': '5/6',
                                                 'h': '8/15',
                                                 'w': '67/30',
                                                 'k': '9/5',
                                                 'w_minus_2l_minus_h': '1/30'},
                                                {'node': 'j=3',
                                                 'l': '3/4',
                                                 'h': '2/5',
                                                 'w': '23/12',
                                                 'k': '25/16',
                                                 'w_minus_2l_minus_h': '1/60'},
                                                {'node': 'j=4',
                                                 'l': '3/4',
                                                 'h': '5/16',
                                                 'w': '11/6',
                                                 'k': '3/2',
                                                 'w_minus_2l_minus_h': '1/48'},
                                                {'node': 'j=5',
                                                 'l': '5/8',
                                                 'h': '2/7',
                                                 'w': '47/30',
                                                 'k': '23/18',
                                                 'w_minus_2l_minus_h': '13/420'},
                                                {'node': 'j=6',
                                                 'l': '5/9',
                                                 'h': '9/40',
                                                 'w': '289/210',
                                                 'k': '47/42',
                                                 'w_minus_2l_minus_h': '101/2520'},
                                                {'node': 'j=7',
                                                 'l': '2/5',
                                                 'h': '3/14',
                                                 'w': '31/30',
                                                 'k': '5/6',
                                                 'w_minus_2l_minus_h': '2/105'},
                                                {'node': 'slot 10',
                                                 'l': '3/4',
                                                 'h': '1/2',
                                                 'w': '37/18',
                                                 'k': '5/3',
                                                 'w_minus_2l_minus_h': '1/18'}]}}

log_bounds = [(F(693, 1000), F(694, 1000)),
              (F(1098, 1000), F(1099, 1000)),
              (F(1609, 1000), F(1610, 1000))]
for p, (lower, upper) in zip((2, 3, 5), log_bounds):
    y = F(p - 1, p + 1)
    partial = 2 * sum((y ** (2*k+1) / (2*k+1) for k in range(20)), F(0))
    remainder = 2 * y**41 / (41 * (1-y*y))
    check(f'log {p}: strict rational enclosure', lower < partial < partial + remainder < upper)

for x, degree, target in proof['atom_bound_certificate']['exponential_certificates']['triples']:
    x = F(x)
    polynomial = sum((x**k / factorial(k) for k in range(degree+1)), F(0))
    check(f'exp lower polynomial x={x}, degree={degree}', polynomial > F(target))

r_bounds = [(480, 500), (660, 664), (900, 910), (830, 840),
            (902, 904), (635, 638)]
q_scaled_bounds = [([469, 1098, 1098], [473, 1099, 1099]),
                   ([287, 1502, 1609], [290, 1505, 1610]),
                   ([0, 990, 1791], [0, 995, 1793]),
                   ([221, 586, 2119], [224, 589, 2122]),
                   ([625, 0, 1425], [630, 0, 1429])]
for node, (ql, qu), (rl, ru) in zip(range(3, 8), q_scaled_bounds, r_bounds[1:]):
    check(f'j={node}: lower squared R bound', 6*rl*rl < sum(q*q for q in ql))
    check(f'j={node}: upper squared R bound', sum(q*q for q in qu) < 6*ru*ru)

for row in proof['rational_majorization_certificate']['rows']:
    low_atom, high_atom, w, k = map(F, (row['l'], row['h'], row['w'], row['k']))
    margin = w - 2*low_atom - high_atom
    check(row['node'] + ': all-moment majorization and margin',
          0 <= high_atom <= low_atom <= 1 and k >= 2*low_atom
          and margin == F(row['w_minus_2l_minus_h']) and margin >= F(1, 60))
base_certificate_checks = len(checks)
check('primary 34-certificate accounting', base_certificate_checks == 34)

# Independently select distance branches using certified logarithm intervals.
zero, a, b, c = (0,0,0), (1,0,0), (0,1,0), (0,0,1)


def add(v, w):
    return tuple(x+y for x, y in zip(v, w))


def mul(k, v):
    return tuple(k*x for x in v)


def sub(v, w):
    return add(v, mul(-1, w))


def interval(v):
    lower = sum((x*(lo if x >= 0 else hi) for x, (lo, hi) in zip(v, log_bounds)), F(0))
    upper = sum((x*(hi if x >= 0 else lo) for x, (lo, hi) in zip(v, log_bounds)), F(0))
    return lower, upper


def sign(v):
    if v == zero:
        return 0
    lo, hi = interval(v)
    if lo > 0:
        return 1
    if hi < 0:
        return -1
    raise AssertionError(('unresolved fixed linear-log comparison', v, lo, hi))


corners = [zero, a, b, c, add(a,b), add(a,c), add(b,c), add(add(a,b),c)]
pairs = list(zip(corners, corners[1:])) + [(a, mul(2,a))]
expected_q = [(zero,zero,zero), (a,a,a), (sub(mul(3,a),c),b,b),
              (sub(mul(2,a),b),sub(mul(2,b),a),c),
              (zero,sub(sub(mul(3,b),a),c),add(a,b)),
              (sub(c,mul(2,a)),sub(mul(2,b),c),sub(mul(2,c),b)),
              (sub(add(b,c),mul(3,a)),zero,sub(sub(mul(2,c),a),b)), (a,a,a)]
for index, ((u,v), expected) in enumerate(zip(pairs, expected_q), 1):
    actual = []
    for step in (a,b,c):
        endpoint = mul(3,step)
        if sign(sub(endpoint,u)) < 0:
            q = sub(u,endpoint)
        elif sign(sub(endpoint,v)) <= 0:
            q = zero
        else:
            other = sub(endpoint,v)
            q = u if sign(sub(u,other)) <= 0 else other
        actual.append(q)
    check(f'node {index}: exact nearest-endpoint branches', tuple(actual) == expected)

products = [1,2,3,5,6,10,15,30]
retained = []
for j in range(1,7):
    p0, p1, p2 = products[j-1:j+2]
    for i, p in enumerate((2,3,5)):
        if p0 > 1 and p0*p0 < p**3 and p1*p0 < p**3 < p2*p0:
            retained.append(7 + 3*(j-1) + i)
check('all 18 fixed reflected eligibility tests retain only slot 10', retained == [10])

check('log-ratio weight bounds from integer powers',
      2**5 > 3**3 and 2**3 < 3**2 and 5**8 < 2**8 * 3**7
      and 3**3 > 5**2 and 2**7 > 5**3)
check('j=1 strict atom cube bound', 125 < 128)
check('j=2 and slot 10 squared R bounds',
      2*F(480,1000)**2 < log_bounds[0][0]**2
      and log_bounds[0][1]**2 < 2*F(500,1000)**2)

offset_lower = [('19/100','2/3'), ('3/10','19/20'), ('29/100','7/6'),
                ('12/25','13/10'), ('3/5','3/2'), ('23/25','31/20'), ('29/100','3/4')]
for node, ((u,v), (rl,ru), (lambda_floor,eta_floor)) in enumerate(
        zip(pairs[1:], r_bounds + [r_bounds[0]], offset_lower), 2):
    v_lower = interval(v)[0]
    check(f'node {node}: lambda and eta strict floors',
          (v_lower-F(ru,1000))/3 > F(lambda_floor)
          and (v_lower+2*F(rl,1000))/3 > F(eta_floor))

# The lower w/k values use the exact log-ratio certificates above.
weight_lowers = [(F(5,2),F(2)),
                 (F(11,6)+F(2,3)*F(3,5), F(3,2)+F(3,10)),
                 (F(5,2)-F(2,3)*F(7,8), F(2)-F(7,16)),
                 (F(11,6),F(3,2)),
                 (F(31,30)+F(4,5)*F(2,3), F(5,6)+F(2,3)*F(2,3)),
                 (F(31,30)+F(4,5)*F(3,7), F(5,6)+F(2,3)*F(3,7)),
                 (F(31,30),F(5,6)),
                 (F(5,2)-F(2,3)*F(2,3),F(2)-F(1,2)*F(2,3))]
for row, (w_lower,k_lower) in zip(proof['rational_majorization_certificate']['rows'], weight_lowers):
    check(row['node'] + ': endpoint first moment / largest-two-mass certificate',
          w_lower == F(row['w']) and k_lower == F(row['k']))

check('radius and uniform strict negative margin', -F(1,60) + 4*F(1,480) == -F(1,120))
check('previous conservative neighborhood radius', 3*F(1,60)/64 == F(1,1280))

# The caller's 64 checks are preserved above. Bind the five outward q boxes
# to the already checked exact linear-log node formulas, using rational intervals.
caller_equivalent_checks = len(checks)
if caller_equivalent_checks != 64:
    raise AssertionError("64-check adaptation accounting")
for node, (ql, qu) in zip(range(3, 8), q_scaled_bounds):
    exact_q = expected_q[node - 1]
    bounds = [interval(q) for q in exact_q]
    check(f"j={node}: outward q bounds linked to exact node formula",
          all(F(lo, 1000) <= lower <= upper <= F(hi, 1000)
              for lo, hi, (lower, upper) in zip(ql, qu, bounds)))
if len(checks) != 69:
    raise AssertionError("69-check fixed certificate accounting")
print(json.dumps({
    "certificate_version": "s19-235-fixed-v1",
    "python_version": platform.python_version(),
    "arithmetic": "Python standard-library fractions.Fraction; exact integers",
    "primary_reported_checks": 34,
    "caller_historical_checks": 64,
    "adapted_caller_equivalent_checks": caller_equivalent_checks,
    "additional_fixed_link_checks": 5,
    "fixed_checks": len(checks), "all_passed": True,
    "retained_reflected_slots": retained,
    "adjacent_paper_nodes": list(range(1, 8)),
    "adjacent_raw_slots": list(range(7)),
    "CPU_candidate_generation": False, "GPU_dispatches": 0,
    "sampled_heights": 0, "sampled_moments": 0,
    "scope": "Fixed proof constants and eight prescribed nodes only; the paper integral argument proves every positive integer moment",
    "checks": checks
}, ensure_ascii=False, sort_keys=True))
