"""Independent exact certificate: coherent star mode0 and a full-gate regression.

Usage: python3 -I -S -B -O coherent_star_mode0_independent.py
         --directory INPUT_DIRECTORY --output RESULT_JSON

Inputs are the pinned Report640 coefficients and one actual101-original family.
No optimizer, producer import, temporary-source import, or Lean claim.
"""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import lcm, prod
from pathlib import Path
import json


PINS = {
    'remaining33_global_root_exclusion_certificate.json':
        'dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4',
    'clustered_global_phase_fixture.json':
        '4bc215b032c910224a3a23ed76edaf1e32dc8e243fe5ba474e129a1cee63e6b6',
}
HERE = Path(__file__).resolve().parent
parser = ArgumentParser(description=__doc__)
parser.add_argument('--directory', type=Path, default=HERE)
parser.add_argument('--output', type=Path,
                    default=HERE/'coherent_star_mode0_independent.json')
args = parser.parse_args()
checks = Counter()
failures = []


def check(category, condition, address=None):
    checks[category] += 1
    if not condition:
        failures.append({'category': category, 'address': address})


inputs = {}
for filename, digest in PINS.items():
    raw = (args.directory/filename).read_bytes()
    check('input_sha256', sha256(raw).hexdigest() == digest, filename)
    if failures:
        raise SystemExit('Input digest mismatch: '+filename)
    inputs[filename] = json.loads(raw)

C = [F(x) for x in inputs[
    'remaining33_global_root_exclusion_certificate.json']['combined512_coefficients']]
check('coefficient_count', len(C) == 512)
check('nonnegative_complete_coefficients', all(c >= 0 for c in C))
Q = (7, 11, 13, 17, 19)
divisors = (3, 5, 15, 9, 25, 45, 75, 225)
g = F(200163067, 201247200)
r = [F(1, q-1) for q in Q]
a = [F(1, q*(q-2)) for q in Q]
B = [F(1)-r[i]-(3 if i == 0 else 2)*a[i] for i in range(5)]
den = [lcm(b.denominator, rr.denominator, aa.denominator)
       for b, rr, aa in zip(B, r, a)]
z = [[int(den[i]*max(F(), B[i]-n*r[i])) for n in range(9)]
     for i in range(5)]
edges = []
for i, j in combinations(range(5), 2):
    weight = (a[i]*r[j]+r[i]*a[j]+2*r[i]*r[j])*den[i]*den[j]
    check('integer_edge_weights', weight.denominator == 1, [i, j])
    edges.append(((1 << i) | (1 << j), int(weight)))

# Literal enumeration, independent of a vertex-deletion recurrence.
matchings = [(0, 1)]+[(mask, -weight) for mask, weight in edges]
matchings += [(m1 | m2, w1*w2)
              for (m1, w1), (m2, w2) in combinations(edges, 2)
              if not(m1 & m2)]
check('literal_matching_count', len(matchings) == 26)
terms = [[(mask ^ covered, weight) for covered, weight in matchings
          if mask & covered == covered] for mask in range(32)]
den_mask = [prod(den[i] for i in range(5) if mask >> i & 1)
            for mask in range(32)]
net_den = lcm((g/den_mask[31]).denominator,
              *[(C[t]/den_mask[31 ^ t]).denominator for t in range(32)])
mass_multiplier = int(g*net_den/den_mask[31])
fee_multiplier = [int(C[t]*net_den/den_mask[31 ^ t]) for t in range(32)]


def responses(counts):
    values = [z[i][counts[i]] for i in range(5)]
    monomials = [prod(values[i] for i in range(5) if mask >> i & 1)
                 for mask in range(32)]
    return [sum(weight*monomials[remaining] for remaining, weight in ts)
            for ts in terms]


def net_numerator(h):
    return mass_multiplier*h[31]-sum(
        fee_multiplier[t]*h[31 ^ t] for t in range(32))


slopes = (35110, 17555, 10551, 4824, 4138)
positive = 0
minimum_positive = None
equalities = []
constant_three = None
for counts in product(range(9), repeat=5):
    h = responses(counts)
    net = net_numerator(h)
    affine = 140440-sum(s*n for s, n in zip(slopes, counts))
    gap = max(net, 0)*1000000-affine*net_den
    check('affine_minorant', gap >= 0, counts)
    if gap == 0:
        equalities.append(list(counts))
    if net > 0:
        positive += 1
        for mask, value in enumerate(h):
            check('retained_response_positive', value > 0, [counts, mask])
            rational = F(value, den_mask[mask])
            if minimum_positive is None or rational < minimum_positive[0]:
                minimum_positive = (rational, list(counts), mask)
    if counts == (3, 3, 3, 3, 3):
        constant_three = F(net, net_den)
check('positive_vector_count', positive == 15894)
check('affine_equalities', equalities == [[0, 8, 0, 0, 0], [4, 0, 0, 0, 0]])
check('minimum_positive_response', minimum_positive[0] ==
      F(28028831665337, 8462661375168000))
check('constant_three_net', constant_three ==
      F(8482754828806680432735281, 3678667717609532583936000000))

# Physical residues and a literal CRT table independently recover the80 cells.
thirds = [x for x in range(9) if x % 3 != 2 and x != 1]
fifths = [x for x in range(25) if x % 5 != 4 and x != 1]
cells = [(x, y) for x, y in product(thirds, fifths)
         if not(x % 3 == 0 and y % 5 == 0)]
crt = {(x % 9, x % 25): x for x in range(225)}
check('live_cell_count', len(cells) == 80)
check('crt_table_bijection', len(crt) == 225)
corners = []
mode0_lower = F(64121, 3125000)
gamma = F(193, 100000)
remainder_target = mode0_lower-gamma
for weak3, weak5 in product(thirds, fifths):
    weights = {(x, y): (1 if x == weak3 else 2)*(3 if y == weak5 else 4)
               for x, y in cells}
    maxima = []
    for d in divisors:
        bins = [0]*d
        for cell, weight in weights.items():
            bins[crt[cell] % d] += weight
        maxima.append(F(max(bins), 675))
    mass = F(sum(weights.values()), 675)
    bound = F(3511, 25000)*mass-F(36089, 500000)*sum(maxima, F())
    check('corner_mode0_lower', bound >= mode0_lower, [weak3, weak5])
    corners.append({
        'physical_corner': [weak3, weak5],
        'root_major_corner': [3*(weak3 % 3)+weak3//3,
                              5*(weak5 % 5)+weak5//5],
        'mass': str(mass), 'class_maxima': list(map(str, maxima)),
        'mode0_lower': str(bound),
    })
check('corner_count', len(corners) == 95)
check('sharp_corner_lower', min(F(c['mode0_lower']) for c in corners) == mode0_lower)

# One actual global family, not merely a consistent central-count table.
originals = inputs['clustered_global_phase_fixture.json']['actual_originals']
by_modulus = {item['modulus']: item for item in originals}
check('fixture101_unique', len(originals) == len(by_modulus) == 101)
for original in originals:
    m, residue = original['modulus'], original['residue']
    check('fixture_odd_modulus', m > 1 and m % 2 == 1, m)
    check('fixture_reduced_residue', 0 <= residue < m, m)
for m, residue in ((3, 2), (9, 1), (5, 4), (25, 1), (15, 0)):
    check('fixture_central_nulls', by_modulus[m]['residue'] == residue, m)
for q in Q:
    check('fixture_outside_pure', by_modulus[q]['residue'] == 0, q)
stars = []
for q, d in product(Q, divisors):
    original = by_modulus[d*q]
    phase = original['residue'] % d
    check('fixture_star_phase81', phase == 81 % d, d*q)
    stars.append({'modulus': d*q, 'residue': original['residue'],
                  'outside_prime': q, 'central_divisor': d,
                  'central_phase': phase})
counts_by_cell = {cell: tuple(sum(crt[cell] % d == by_modulus[q*d]['residue'] % d
                                 for d in divisors) for q in Q)
                  for cell in cells}
h_by_cell = {cell: responses(counts) for cell, counts in counts_by_cell.items()}
retained = [cell for cell in cells if net_numerator(h_by_cell[cell]) > 0]
check('fixture_retained_cells', len(retained) == 74)

# Full mode8 residual additions; no guarded mode9 shortcut is used.
full_C = C[:]
additions = []
for index, q in enumerate(Q[1:], start=1):
    delta = g*a[index]
    full_C[8*32+(1 << index)] += delta
    additions.append({'mode': 8, 'support': 1 << index,
                      'original_modulus': 9*q*q, 'coefficient': str(delta)})


def menus(values, prime, weak, deep):
    normal = {x: ((1 if prime == 3 else 3) if x == weak
                  else (2 if prime == 3 else 4)) for x in values}
    return [
        [normal],
        [{x: normal[x] if x % prime == root else 0 for x in values}
         for root in range(prime-1)],
        [{x: normal[x] if x == leaf else 0 for x in values} for leaf in values],
        [{x: deep if x == leaf else 0 for x in values} for leaf in values],
    ]


# Root-major corner(4,10) corresponds to physical residues(4,2).
weak3, weak5 = 4, 2
menu3 = menus(thirds, 3, weak3, 9)
menu5 = menus(fifths, 5, weak5, 60)
source_term = g*sum((F(menu3[0][0][cell[0]]*menu5[0][0][cell[1]]*
                         h_by_cell[cell][31], 675*den_mask[31])
                      for cell in retained), F())
fees = []
literal_selectors = 0
screen_count = 0
for ex, ey in product(range(4), repeat=2):
    profiles = [[x[cell[0]]*y[cell[1]] for cell in retained]
                for x, y in product(menu3[ex], menu5[ey])]
    literal_selectors += len(profiles)
    fee = F()
    for queried in range(32):
        unqueried = 31 ^ queried
        screen = max(sum(weight*h_by_cell[cell][unqueried]
                         for weight, cell in zip(profile, retained))
                     for profile in profiles)
        screen_count += len(profiles)
        fee += full_C[(4*ex+ey)*32+queried]*F(
            screen, 675*den_mask[unqueried])
    fees.append(fee)
check('literal_selector_count', literal_selectors == 559)
check('literal_support_selector_evaluations', screen_count == 17888)
mode0 = source_term-fees[0]
rest = sum(fees[1:], F())
gate = source_term-sum(fees, F())
check('fixture_exact_mode0', mode0 ==
      F(31840305005954603376439854827, 206925059115536207846400000000))
check('fixture_exact_rest', rest ==
      F(231413335724929518222451571471, 827700236462144831385600000000))
check('fixture_exact_gate', gate ==
      -F(34684038567037034905564050721, 275900078820714943795200000000))
check('fixture_negative_gate', gate < 0)
check('fixture_remainder_claim_refuted', rest > remainder_target)
check('fixture_mode1_alone_refutes', fees[1] > remainder_target)
check('fixture_exact_mode1', fees[1] ==
      F(41957988958888040447123383, 1724375492629468398720000000))

result = {
    'schema': 'coherent-star-mode0-independent-v1',
    'status': 'PASS' if not failures else 'FAIL',
    'optimizer_used': False, 'new_lean_verification': False,
    'input_sha256': PINS,
    'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
    'check_count': sum(checks.values()), 'checks': dict(sorted(checks.items())),
    'failures': failures,
    'count_vectors': 9**5, 'positive_vectors': positive,
    'literal_matchings': len(matchings),
    'affine_minorant': {'denominator': 1000000, 'constant': 140440,
                       'slopes_in_Q_order': list(slopes), 'equalities': equalities},
    'minimum_positive_response': {
        'value': str(minimum_positive[0]), 'counts': minimum_positive[1],
        'unqueried_mask': minimum_positive[2]},
    'constant_three_mode0': str(constant_three),
    'mode0_lower': str(mode0_lower), 'gamma': str(gamma),
    'proposed_remainder_target': str(remainder_target),
    'corners': corners,
    'actual_fixture_regression': {
        'actual_original_count': len(originals), 'global_stars': stars,
        'root_major_corner': [4, 10], 'physical_corner': [weak3, weak5],
        'retained_cells': len(retained),
        'counts': [{'physical_cell': list(cell), 'counts': list(counts_by_cell[cell]),
                    'retained': cell in retained} for cell in cells],
        'full_residual_additions': additions,
        'literal_selectors': literal_selectors,
        'support_selector_evaluations': screen_count,
        'source_term': str(source_term), 'fees_by_central_mode': list(map(str, fees)),
        'mode0': str(mode0), 'remaining_debit': str(rest), 'full_gate': str(gate),
        'mode1_minus_proposed_remainder': str(fees[1]-remainder_target),
    },
    'scope': ('Exact mode0 affine minorant and95-corner bound; one actual coherent '
              'phase81 fixture refutes the proposed uniform remainder bound for '
              'chi=1[F>0] with fullmode8 residual fees. No upper obstruction to '
              'all fields or sources, no complete positive gate, no unrestricted '
              'odd-covering resolution. All finite-height source claims use the '
              'ordinary source proof, not these finite checks.'),
}
args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
print(json.dumps({'status': result['status'], 'check_count': result['check_count'],
                  'mode0_lower': str(mode0_lower), 'fixture_full_gate': str(gate),
                  'failure_count': len(failures)}, sort_keys=True))
if failures:
    raise SystemExit(1)
