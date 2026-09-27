#!/usr/bin/env python3
"""Exact two-centre star profile for the complete height-three mixed tail.

The companion C++17 program enumerates exactly 16^5 layouts and both ternary
endpoints.  This driver constructs every rational coefficient, proves a
finite signed-integer accumulation bound, compiles the companion, and checks
its extremal layouts by a separate direct Fraction calculation.  JSON stores
only endpoint extrema and the corresponding witness summaries, not all rows.

Source contract: on the ternary coordinate discard the actual pure-3 root,
or choose a root if modulus 3 is absent, then condition Haar on the complete
actual pure survivor in the two remaining roots.  Their masses are t,1-t,
with 1/3 <= t <= 2/3; depth e>=2 cylinders have mass <=2/3^e.  For each
p>=5 in P use equal masses on p-1 retained roots and actual pure-survivor
Haar inside each root.  The product source has density <=3458/405 times Haar.

The auxiliary block contains 3*5 and 3*q,5*q for q=7,11,13,17,19. Retain
all actual rho-active originals in these slots and fill the other slots
with additional retained-root cylinders.  Normalize 3*5 to the grid cell
(0,0).  The actual submeasure is

    eta = rho * ALL_actual_mixed_survivors * auxiliary_block_survivors.

One q-coordinate has a row, a column, and a bit indicating whether the two
q-roots agree.  Its cell avoidance is 1-(row_hit+column_hit-equal*both)/(q-1).
For a tested support, drop its own q-coordinate avoidance factors.  The
remaining grid gives an upper screen for the original or query cylinder.

For supports containing 3, KEEP the first-layer and deeper contributions
separate: max_j(t_j*f_j) and (1/3)*max_j(f_j).  Complete H-height tails use
all other-coordinate heights and the exact residual factor 3^(2-H) on
the deeper screen.  The gate G*mass-R, G=566/49, is concave in t; checking
the two endpoints therefore covers its entire permitted interval.

The declared H=3 original family includes all pure originals, all squarefree
mixed originals, and every mixed original with some exponent >=3, with
arbitrary fixed phases.  Originals involving 23 or29 are unrestricted.
Continuation uses Report569 SD15--SD16's raw mass/query count, with THIS
source's density: Haar(full survivor) >=49*(G*mass-R)/(616*(3458/405)).

The H=2 control is one exact negative envelope case, not an exhaustive scan
and not an actual covering counterexample.  This program supplies finite
arithmetic for ordinary proofs; it is not Lean verification.
"""

import argparse
from fractions import Fraction
from functools import reduce
import hashlib
import json
from math import lcm
from operator import mul
from pathlib import Path
import shutil
import subprocess
import tempfile

F = Fraction
P = (3, 5, 7, 11, 13, 17, 19)
Q = P[2:]
G = F(566, 49)
DENSITY = F(3458, 405)
LAYOUTS = 16 ** 5
GRID_DENOMINATOR = 12 * 6 * 10 * 12 * 16 * 18
EXPECTED_GATE = F(2488465975171529051, 22392201998694528000)
REPORT569 = ('docs/reports/erdos7-odd-covering/profile-notes/arithmetic/'
             '569-complete-suffix-debits-close-the-six-prime-query-target.md')
MODE_NAMES = (
    'no_3_no_5', 'no_3_with_5', 'with_3_no_5_first_layer',
    'with_3_no_5_deeper_layers', 'with_3_with_5_first_layer',
    'with_3_with_5_deeper_layers',
)


def product(values):
    return reduce(mul, values, F(1))


def outside_tail(prime, cutoff):
    return F(1, (prime - 2) * (prime - 1) * prime ** (cutoff - 2))


def coefficient_profile(cutoff):
    """Six modes by 32 outside supports; each coefficient is G*loss+query."""
    rows = []
    for mode, name in enumerate(MODE_NAMES):
        for mask in range(32):
            primes = tuple(prime for index, prime in enumerate(Q) if mask >> index & 1)
            if mode < 2:
                support = primes + ((5,) if mode == 1 else ())
                mixed = len(support) >= 2
                auxiliary = mode == 1 and len(support) == 2
                full = product(F(1, prime - 2) for prime in support)
                low = product(F(1, prime - 2) - outside_tail(prime, cutoff)
                              for prime in support)
                squarefree = (product(F(1, prime - 1) for prime in support)
                              if mixed and not auxiliary else F(0))
                tail = full - low if mixed else F(0)
                loss = squarefree + tail
                query = full if support else F(0)
            else:
                other = primes + ((5,) if mode >= 4 else ())
                full = product(F(1, prime - 2) for prime in other)
                low = product(F(1, prime - 2) - outside_tail(prime, cutoff)
                              for prime in other)
                if mode in (2, 4):
                    squarefree = (product(F(1, prime - 1) for prime in other)
                                  if len(other) >= 2 else F(0))
                    loss = squarefree + (full - low if other else F(0))
                else:
                    # The screen already contains the full deeper ternary
                    # query sum 1/3. The ternary H-tail is 3^(1-H), giving
                    # the relative factor 3^(2-H) below.
                    loss = full - low + F(1, 3 ** (cutoff - 2)) * low if other else F(0)
                query = full
            rows.append({'mode': name, 'outside_support': primes,
                         'loss_weight': loss, 'query_weight': query,
                         'combined_coefficient': G * loss + query})
    return rows


def decode_layout(code):
    layout = []
    for prime in Q:
        role = code & 15
        code >>= 4
        layout.append({'prime': prime, 'row': role & 1,
                       'column': (role >> 1) & 3,
                       'equal_outside_roots': bool((role >> 3) & 1)})
    return layout


def direct_case(cutoff, code, t0):
    """Rebuild the boundary and all support sums without the coefficient rows."""
    layout = decode_layout(code)
    masses = (t0, 1 - t0)
    grids = {}
    for mask in range(32):
        support = {prime for index, prime in enumerate(Q) if mask >> index & 1}
        grid = []
        for row in range(2):
            for column in range(4):
                if row == 0 and column == 0:
                    grid.append(F(0))
                    continue
                avoidance = F(1)
                for role in layout:
                    if role['prime'] in support:
                        continue
                    a = int(row == role['row'])
                    b = int(column == role['column'])
                    distinct_hits = a + b - (a * b if role['equal_outside_roots'] else 0)
                    avoidance *= 1 - F(distinct_hits, role['prime'] - 1)
                grid.append(avoidance)
        grids[mask] = grid
    block_mass = sum(masses[row] * grids[0][row * 4 + column] / 4
                     for row in range(2) for column in range(4))
    squarefree_loss = F(0)
    complete_tail_loss = F(0)
    query = F(0)
    for support_mask in range(1, 128):
        support = tuple(prime for index, prime in enumerate(P) if support_mask >> index & 1)
        outside_mask = sum(1 << index for index, prime in enumerate(Q) if prime in support)
        grid = grids[outside_mask]
        mixed = len(support) >= 2
        auxiliary = len(support) == 2 and bool(set(support) & {3, 5})
        other = tuple(prime for prime in support if prime != 3)
        full = product(F(1, prime - 2) for prime in other)
        low = product(F(1, prime - 2) - outside_tail(prime, cutoff) for prime in other)
        squarefree = product(F(1, prime - 1) for prime in other)
        if 3 not in support:
            if 5 in support:
                screen = max(masses[0] * grid[column] + masses[1] * grid[column + 4]
                             for column in range(4))
            else:
                screen = sum(masses[row] * grid[row * 4 + column] / 4
                             for row in range(2) for column in range(4))
            query += screen * full
            if mixed:
                complete_tail_loss += screen * (full - low)
                if not auxiliary:
                    squarefree_loss += screen * squarefree
        else:
            row_screens = [max(grid[row * 4:row * 4 + 4]) if 5 in support
                           else sum(grid[row * 4:row * 4 + 4]) / 4 for row in range(2)]
            first = max(masses[row] * row_screens[row] for row in range(2))
            deep = max(row_screens) / 3
            query += (first + deep) * full
            if mixed:
                complete_tail_loss += ((first + deep) * (full - low)
                                       + F(1, 3 ** (cutoff - 1)) * max(row_screens) * low)
                if not auxiliary:
                    squarefree_loss += first * squarefree
    mass = block_mass - squarefree_loss - complete_tail_loss
    gate = G * mass - query
    return {'code': code, 'ternary_root_mass_t0': t0, 'layout': layout,
            'auxiliary_block_mass': block_mass, 'squarefree_nonblock_loss': squarefree_loss,
            'complete_mixed_tail_loss': complete_tail_loss,
            'mass_lower_bound': mass, 'raw_query_upper_bound': query,
            'same_partition_gate_Gs_minus_R': gate,
            'haar_certificate_rhs': 49 * gate / (616 * DENSITY)}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    return value


def prepare_coefficients():
    profile = coefficient_profile(3)
    coefficients = [row['combined_coefficient'] for row in profile]
    denominator = lcm(49, *(coefficient.denominator for coefficient in coefficients))
    integers = [int(coefficient * denominator) for coefficient in coefficients]
    scaled_G = int(G * denominator)
    bound = (scaled_G + sum(integers)) * GRID_DENOMINATOR
    if bound >= 2 ** 126 - 1:
        raise ArithmeticError('signed integer accumulation bound exceeded')
    text = ('\n'.join((str(denominator), str(scaled_G), '3',
                       ' '.join(str(value) for value in integers))) + '\n')
    return profile, denominator, bound, text


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
    parser.add_argument('--engine', type=Path,
                        default=Path(__file__).with_name('two_centre_star_scan.cpp'))
    parser.add_argument('--cxx', default=shutil.which('clang++') or shutil.which('g++'))
    args = parser.parse_args()
    if not args.cxx:
        parser.error('a C++17 compiler supporting signed __int128 is required')
    profile, denominator, bound, coefficient_text = prepare_coefficients()
    with tempfile.TemporaryDirectory(prefix='two-centre-star-') as temporary:
        directory = Path(temporary)
        coefficient_path = directory / 'coefficients.txt'
        executable = directory / 'two_centre_star_scan'
        coefficient_path.write_text(coefficient_text, encoding='utf-8')
        subprocess.run([args.cxx, '-std=c++17', '-O3', str(args.engine), '-o', str(executable)],
                       check=True, capture_output=True, text=True)
        scan = subprocess.run([str(executable), str(coefficient_path)],
                              check=True, capture_output=True, text=True)
    lines = scan.stdout.splitlines()
    if len(lines) != 3 or int(lines[0]) != denominator * GRID_DENOMINATOR:
        raise ArithmeticError('invalid exact engine output header')
    checks = {}

    def require(name, condition):
        if not condition:
            raise ArithmeticError('certificate check failed: ' + name)
        checks[name] = True

    endpoints = []
    direct_checks = []
    for expected_t, line in enumerate(lines[1:], start=1):
        fields = [int(value) for value in line.split()]
        if len(fields) != 9:
            raise ArithmeticError('invalid endpoint result')
        cutoff, t, minimum, maximum, min_code, max_code, min_ties, max_ties, cases = fields
        if cutoff != 3 or t != expected_t or cases != LAYOUTS:
            raise ArithmeticError('wrong scan coverage')
        if not (0 <= min_code < LAYOUTS and 0 <= max_code < LAYOUTS
                and 1 <= min_ties <= LAYOUTS and 1 <= max_ties <= LAYOUTS):
            raise ArithmeticError('invalid extremal layout or multiplicity')
        low = direct_case(3, min_code, F(t, 3))
        high = direct_case(3, max_code, F(t, 3))
        direct_checks.extend((low['same_partition_gate_Gs_minus_R'] == F(minimum, int(lines[0])),
                              high['same_partition_gate_Gs_minus_R'] == F(maximum, int(lines[0]))))
        endpoints.append({'t0': F(t, 3), 'layout_count': cases,
                          'minimum_gate': F(minimum, int(lines[0])),
                          'maximum_gate': F(maximum, int(lines[0])),
                          'minimum_ties': min_ties, 'maximum_ties': max_ties,
                          'minimum_witness': low, 'maximum_witness': high})
    uniform_gate = min(endpoint['minimum_gate'] for endpoint in endpoints)
    haar = 49 * uniform_gate / (616 * DENSITY)
    h2_control = direct_case(2, 218451, F(2, 3))
    require('all_endpoint_extrema_match_independent_direct_fraction_grids', all(direct_checks))
    require('complete_H3_scan_covers_both_endpoints',
            sum(endpoint['layout_count'] for endpoint in endpoints) == 2 * LAYOUTS)
    require('H3_uniform_gate_exact_regression', uniform_gate == EXPECTED_GATE)
    require('H3_uniform_Haar_above_one_over_1000', haar > F(1, 1000))
    require('H2_exact_negative_envelope_control', h2_control['same_partition_gate_Gs_minus_R'] < 0)
    require('source_density_product',
            DENSITY == 2 * product(F(prime, prime - 2) for prime in P if prime != 3))
    require('complete_outside_tail_geometric_recurrence', all(
        outside_tail(prime, 3) == F(1, (prime - 2) * prime ** 2) + outside_tail(prime, 4)
        for prime in P if prime != 3))
    require('complete_ternary_deep_query_and_tail',
            F(2, 9) + F(1, 9) == F(1, 3) and F(1, 9) / F(1, 3) == F(1, 3))
    require('coefficient_shape_and_nonnegative_weights', len(profile) == 192 and all(
        row['loss_weight'] >= 0 and row['query_weight'] >= 0
        and row['combined_coefficient'] == G * row['loss_weight'] + row['query_weight']
        for row in profile))
    require('integer_coefficients_are_exact_and_signed_accumulation_safe',
            all((row['combined_coefficient'] * denominator).denominator == 1 for row in profile)
            and bound < 2 ** 126 - 1)
    require('same_law_23_29_density_conversion',
            haar == (49 * uniform_gate / 567) / (DENSITY * F(22, 21) * F(28, 27)))
    result = {
        'schema': 'two-centre-star-profile-v1',
        'verification_kind': 'exact finite arithmetic supporting ordinary proofs; no Lean verification',
        'source': {
            'producer_name': Path(__file__).name,
            'producer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'engine_name': args.engine.name,
            'engine_sha256': hashlib.sha256(args.engine.read_bytes()).hexdigest(),
            'continuation_reference': {'path': REPORT569, 'equations': ['SD15', 'SD16']},
        },
        'scope': {
            'carrier': P + (23, 29),
            'old_originals': 'all pure, all squarefree mixed, all mixed with maximum exponent>=3',
            'fresh_originals': 'all actual originals touching23 or29, at every height and phase',
            'submeasure': 'rho times ALL actual mixed survivors times auxiliary block survivors',
            'common_source': 'one fixed product rho, auxiliary layout, actual family and submeasure',
            'H2_control': 'one negative envelope case; neither exhaustive scan nor actual covering',
            'endpoint_reduction': 'gate is concave in the actual ternary mass t0 on [1/3,2/3]',
        },
        'constants': {'G': G, 'density_cap': DENSITY, 'cutoff': 3,
                      'geometric_layouts': LAYOUTS, 'endpoint_count': 2,
                      'profile_evaluations': 2 * LAYOUTS,
                      'coefficient_common_denominator': denominator,
                      'integer_absolute_accumulation_bound': bound,
                      'integer_absolute_accumulation_bound_bits': bound.bit_length()},
        'coefficient_profile': profile,
        'endpoint_results': endpoints,
        'uniform': {'gate_lower_bound': uniform_gate, 'Haar_survivor_lower_bound': haar,
                    'extra_raw_weight_open_budget': uniform_gate / G},
        'H2_negative_control': h2_control,
        'checks': checks, 'check_count': len(checks),
    }
    args.output.write_text(json.dumps(encode(result), indent=2, sort_keys=True) + '\n', encoding='utf-8')
    print(f"H=3: {2 * LAYOUTS:,} exact layout/endpoint evaluations; {len(checks)} checks passed.")
    print(f"Uniform gate={float(uniform_gate):.12f}; Haar>1/1000. H=2 has an exact negative envelope case.")
    print('Result:', args.output)


if __name__ == '__main__':
    main()
