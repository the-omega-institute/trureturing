"""A fixed-threshold five-source bound and its four-projection application.

This consumer reads existing pinned source geometry without regenerating it.
It checks a new common query threshold, a supported-source continuation, and
one finite original-label fixture. Ordinary source and interpolation premises
remain separate from this arithmetic; no Lean build is run.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction as F
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
from itertools import product
from math import gcd, prod
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
INPUT = 'four_phase_projection_source_input.json'
RESULT = 'four_phase_projection_source.json'
INPUT_PIN = '6e3f49c284d7e93df824796faf99545312e397eed4be547e6854eb5de01e1c00'
SOURCE_PINS = {
    'six_prime_prefix_certificate.json': 'ecdeb6246626c101b7bb16130366a7d22bf8d71775d5f28997b85e74c796ee61',
    'six_prime_prefix_geometry.json': '0f65a963f617867e87021c695a5ded8ad18cb1217857c0bbc7d49652b0f5fdd1',
    'six_prime_prefix_certificate.py': '3077f18fd91bf8f3a45483690b5f2d1386f1f692dccd9a453c43c99a8746daf4',
}
C5 = F(1052000467553752961669550889525, 113143330653881187980816775279)
OLD_C5 = F(354268696184847779107405, 37639127656852367739093)
DENSITY5 = F(84375000000, 1812390307)
BASE_PRIMES = (3, 5, 7, 11, 13)


def need(ok, message):
    if not ok:
        raise ValueError(message)


def pinned(directory, name, digest):
    raw = (directory / name).read_bytes()
    need(sha256(raw).hexdigest() == digest, 'input identity: ' + name)
    return raw


def exponent(n, p):
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def smooth_part(n, primes):
    return prod(p ** exponent(n, p) for p in primes)


def crt(a, m, b, n):
    need(gcd(m, n) == 1, 'coprime CRT inputs')
    return (a + m * (((b - a) * pow(m, -1, n)) % n)) % (m * n)


def query_bound(directory):
    source = json.loads(pinned(directory, 'six_prime_prefix_certificate.json', SOURCE_PINS['six_prime_prefix_certificate.json']))
    geometry = json.loads(pinned(directory, 'six_prime_prefix_geometry.json', SOURCE_PINS['six_prime_prefix_geometry.json']))
    pinned(directory, 'six_prime_prefix_certificate.py', SOURCE_PINS['six_prime_prefix_certificate.py'])
    spec = spec_from_file_location('four_phase_source_helper', directory / 'six_prime_prefix_certificate.py')
    helper = module_from_spec(spec)
    spec.loader.exec_module(helper)
    need(source['schema'] == 'six-prime-prefix-certificate-v1', 'source schema')
    expected = {(a, b, c, -1, j, 0, 0, 0, -1)
                for a in (1, 2) for b in (2, 4) for c in (a, 3 - a) for j in range(1, 5)}
    need(len(source['rows']) == 32 and {tuple(r['node']) for r in source['rows']} == expected,
         'complete 32-vertex source inventory')
    need(tuple(helper.THRESHOLDS) == (2, 4, 4, 8, 8, 12), 'unchanged stage deletion thresholds')
    table, mean = helper.multiplier_prefixes()[3]
    need(mean == F(105, 64) and all(F(6, m) in helper.RATIOS for m in table if m < 6),
         'fixed query threshold uses only existing cached anchor arguments')
    rows = []
    for original in source['rows']:
        a, b, c, _, j, *_ = original['node']
        reserve = F(original['reserve_lower_bound_cell_units'])
        losses = [F(x) for x in original['rounded_loss_upper_bounds_cell_units']]
        need(len(losses) == 6 and all(x >= 0 for x in losses), 'nonnegative source loss inventory')
        live = reserve - sum(losses[:3])
        need(live > 0, 'positive same-source five-coordinate reserve')
        mass, whole, hinges = helper.envelope(geometry['batches'], a, b, c, j)
        thresholds = {}
        for t in (4, 6):
            small = {m: p for m, p in table.items() if m < t}
            pp = sum(small.values(), F())
            mm = sum((m * p for m, p in small.items()), F())
            need(0 <= pp <= 1 and 0 <= mm <= mean, 'nonnegative exact multiplier remainder')
            hinge = sum((m * p * hinges[F(t, m)] for m, p in small.items()), F())
            hinge += (mean - mm) * whole - t * (1 - pp) * mass
            need(hinge >= 0, 'nonnegative complete-query hinge')
            thresholds[t] = {'hinge': hinge, 'bound': t - 1 + hinge / live}
        slack = (C5 - 5) * live - thresholds[6]['hinge']
        need(C5 >= 5 and slack >= 0, 'same global threshold and nonnegative continuous-vertex slack')
        rows.append({'node': original['node'], 'reserve': reserve, 'five_live_cell_units': live,
                     'comparison_mass': mass, 'linear_envelope': whole,
                     'thresholds': thresholds, 'new_bound_slack': slack})
    need(max(r['thresholds'][6]['bound'] for r in rows) == C5, 'exact new five-source bound')
    need(max(r['thresholds'][4]['bound'] for r in rows) == OLD_C5, 'old fixed-threshold bound retained')
    tight = [r['node'] for r in rows if r['new_bound_slack'] == 0]
    need(tight == [[2, 4, 1, -1, j, 0, 0, 0, -1] for j in (1, 3, 4)], 'tight source vertices')
    mass5 = min(r['five_live_cell_units'] for r in rows) / 135
    need(mass5 == F(1812390307, 22500000000) and F(15, 4) / mass5 == DENSITY5,
         'same source mass and density')
    need(C5 < F(93, 10) and DENSITY5 < 47, 'usable rational source bounds')
    need(len(helper.BATCHES) == 72 and helper.QUERIES == 51840, 'only existing geometry read')
    return {'query_threshold': 6, 'stage_thresholds': list(helper.THRESHOLDS),
            'C5': C5, 'previous_C5': OLD_C5, 'density5': DENSITY5, 'mass5': mass5,
            'tight_vertices': tight, 'rows': rows, 'cached_geometry_batches': 72,
            'cached_integer_reads': 51840, 'geometry_regenerated': False}


def continuation(c5=C5, density5=DENSITY5, r17=4, r19=4):
    need(0 <= r17 < 16 and 0 <= r19 < 18, 'positive projection-mask survival')
    r7 = (1 + c5) * (1 + F(1, 16 - r17)) * (1 + F(1, 18 - r19)) - 1
    density7 = density5 * F(16, 16 - r17) * F(18, 18 - r19)
    live9 = 1 - F(51, 616) * (1 + r7)
    need(live9 > 0, 'positive same-source nine-coordinate reserve')
    return {'r17': r17, 'r19': r19, 'query7': r7, 'density7': density7,
            'live9': live9, 'haar9': live9 / density7}


def fixture(data):
    need(tuple(data['core_primes']) == BASE_PRIMES
         and tuple(data['old_primes']) == BASE_PRIMES + (17, 19)
         and tuple(data['outside_primes']) == (23, 29), 'fixed first-nine-prime carrier')
    old = data['old_originals']
    units = data['unit_originals']
    need(len(old) == 14 and len(units) == 2, 'fixture inventory sizes')
    originals, seen = [], set()
    def add(m, a, kind, **extra):
        need(type(m) is int and m > 1 and m % 2 == 1 and m not in seen
             and type(a) is int and 0 <= a < m, 'distinct odd numerical originals with canonical phases')
        need(smooth_part(m, data['old_primes'] + data['outside_primes']) == m, 'original prime support')
        seen.add(m)
        row = {'modulus': m, 'residue': a, 'kind': kind, **extra}
        originals.append(row)
        return row
    projections = defaultdict(set)
    for row in old:
        m, a, side = row['modulus'], row['residue'], row['assignment']
        need(smooth_part(m, data['old_primes']) == m, 'old original support')
        core = smooth_part(m, BASE_PRIMES)
        if core == m:
            need(side is None, 'core-only originals stay in the five-source family')
        else:
            need(type(side) is int and side in (17, 19) and m % side == 0,
                 'every non-core original has one actual positive endpoint assignment')
            e = exponent(m, side)
            projections[side, e].add(a % (side ** e))
        add(m, a, 'old', assignment=side)
    need(projections and all(len(phases) <= 4 for phases in projections.values()),
         'four distinct projected phases per actual depth')
    need(projections[17, 1] == projections[19, 1] == {0, 1, 2, 3}, 'both four-phase bounds exercised')
    need(any(r['modulus'] % (17 * 19) == 0 and r['assignment'] in (17, 19) for r in old),
         'one actual mixed original is assigned once')
    need({(r['modulus'], r['residue']) for r in units} == {(23, 0), (29, 0)},
         'actual unit classes establish the conditioned-law scope')
    for row in units:
        add(row['modulus'], row['residue'], 'unit')
    cycle = data['cycle']
    n = cycle['count']
    need(type(n) is int and n == 23 * 22 and cycle['old_prime'] == 3
         and cycle['outside_prime'] == 23 and cycle['index_first'] == 1
         and cycle['index_last'] == n and cycle['outside_depths'] == [1, 2], 'two complete fixed phase cycles')
    need(cycle['old_residue_initial'] == [0, 1, 2]
         and cycle['old_residue_after_initial'] == '3^(i-1)-1'
         and cycle['depth1_residue'] == '1+(i mod22)'
         and cycle['depth2_residue'] == '23*floor((i-1)/22)+1+((i-1) mod22)'
         and cycle['full_modulus'] == '3^i*23^e'
         and cycle['full_residue'] == 'CRT(old residue modulo3^i, depth-e residue modulo23^e)',
         'literal original-generation formulas')
    old_cylinders, cycle_rows = [], []
    phases = {1: Counter(), 2: Counter()}
    for i in range(1, n + 1):
        d = 3 ** i
        alpha = cycle['old_residue_initial'][i - 1] if i <= 3 else 3 ** (i - 1) - 1
        need(0 <= alpha < d, 'actual old phase at its full depth')
        old_cylinders.append((alpha, d))
        for e in (1, 2):
            q = 23 ** e
            b = 1 + i % 22 if e == 1 else 23 * ((i - 1) // 22) + 1 + (i - 1) % 22
            a = crt(alpha, d, b, q)
            need(a % d == alpha and a % q == b and b % 23 != 0, 'original CRT phase and nonzero unit root')
            phases[e][b] += 1
            cycle_rows.append(add(d * q, a, 'cycle', index=i, depth=e,
                                  old_modulus=d, old_residue=alpha, outside_residue=b))
    need(len(originals) == 1028 and len(cycle_rows) == 1012, 'complete distinct actual inventory')
    need(phases[1] == Counter({a: 23 for a in range(1, 23)})
         and phases[2] == Counter({a: 1 for a in range(23 ** 2) if a % 23}),
         'all allowed phases occur with the required multiplicities')
    need({a % 3 for a, _ in old_cylinders} == {0, 1, 2}, 'three old roots rule out a literal two-reference template')
    disjoint_checks = 0
    for i, (a, d) in enumerate(old_cylinders):
        for b, f in old_cylinders[:i]:
            need(a % f != b, 'different old cylinders are disjoint')
            disjoint_checks += 1
    need(disjoint_checks == n * (n - 1) // 2, 'complete old-cylinder disjointness checks')
    # A single actual common law avoiding0mod23 is supported on these506 atoms.
    # Pointwise equality of raw costs proves the claim for every such law.
    unit_avoiding_atoms = [a for a in range(23 ** 2) if a % 23]
    costs = [sum(count for a, count in phases[1].items() if y % 23 == a)
             + phases[2].get(y, 0) for y in unit_avoiding_atoms]
    need(len(costs) == 506 and set(costs) == {24}, 'pointwise every-conditioned-law phase-cycle identity')
    cut_capacity = n + 1
    grouping = []
    for side23, side29 in product(('R', 'S'), repeat=2):
        scale = 22 if side23 == 'R' else 28
        demand = scale * costs[0]
        need(demand > cut_capacity, 'conditioned raw account exceeds every reachable ancestor capacity')
        grouping.append({'side23': side23, 'side29': side29, 'scale': scale,
                         'demand': demand, 'ancestor_capacity': cut_capacity,
                         'deficit': demand - cut_capacity})
    # Each cycle class has a private witness in the complete finite family.
    # The theorem does not depend on this extra finite check.
    other = {int(p): a for p, a in data['private_witness_other_coordinates'].items()}
    need(set(other) == {5, 7, 11, 13, 17, 19, 29}
         and all(type(a) is int and 0 <= a < p for p, a in other.items()), 'fixed private-witness coordinates')
    joint_residue, joint_modulus = 0, 1
    for p, a in sorted(other.items()):
        joint_residue = crt(joint_residue, joint_modulus, a, p)
        joint_modulus *= p
    witness_digest = sha256()
    witness_checks = 0
    for row in cycle_rows:
        rr = crt(row['outside_residue'], 23 ** row['depth'], joint_residue, joint_modulus)
        mm = (23 ** row['depth']) * joint_modulus
        witness = crt(row['old_residue'], 3 ** n, rr, mm)
        need(witness % row['modulus'] == row['residue'], 'private witness meets its own original')
        for other_row in originals:
            if other_row is not row:
                need(witness % other_row['modulus'] != other_row['residue'], 'private witness avoids every other original')
                witness_checks += 1
        witness_digest.update((str(row['modulus']) + ':' + str(witness) + '\n').encode())
    need(witness_checks == len(cycle_rows) * (len(originals) - 1), 'complete finite private-witness checks')
    digest = sha256((json.dumps(originals, sort_keys=True, separators=(',', ':')) + '\n').encode()).hexdigest()
    return {'original_count': len(originals), 'old_original_count': len(old), 'unit_original_count': len(units),
            'cycle_original_count': len(cycle_rows), 'original_list_sha256': digest,
            'projection_phase_sets': [{'prime': p, 'depth': e, 'phases': sorted(a)}
                                      for (p, e), a in sorted(projections.items())],
            'old_disjointness_checks': disjoint_checks, 'conditioned_atoms': len(costs),
            'conditioned_unscaled_raw_cost': costs[0], 'groupings': grouping,
            'private_witness_checks': witness_checks, 'private_witness_sha256': witness_digest.hexdigest(),
            'scope': 'Raw obstruction requires avoidance of0mod23; it does not refute unconditioned Haar transports.',
            'first_cycle_originals': cycle_rows[:6], 'last_cycle_originals': cycle_rows[-2:]}


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def certificate(directory):
    data = json.loads(pinned(directory, INPUT, INPUT_PIN))
    source = query_bound(directory)
    exact = continuation()
    coarse = continuation(F(93, 10), F(47))
    need(coarse['query7'] == F(1227, 112) and coarse['density7'] == F(564, 7)
         and coarse['live9'] == F(703, 68992) and coarse['haar9'] == F(4921, 38911488)
         and coarse['haar9'] > F(1, 8000), 'simple nine-prime constants')
    need(exact['haar9'] > coarse['haar9'], 'exact constants strengthen displayed coarse reserve')
    return encode({'schema': 'four-phase-projection-source-v1',
                   'scope': 'Ordinary source premises plus exact fixed-threshold and original-fixture controls; no Lean replay.',
                   'source_pins': SOURCE_PINS, 'input_pin': INPUT_PIN,
                   'source': source, 'exact_continuation': exact,
                   'coarse_continuation': coarse, 'fixture': fixture(data)})


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--input-dir', type=Path, default=ROOT)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = certificate(args.input_dir)
    payload = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(payload)
        print(json.dumps({'written': str(args.output), 'query5': str(C5), 'haar9': result['exact_continuation']['haar9']}))
    else:
        retained = json.loads((args.input_dir / RESULT).read_text())
        need(result == retained, 'retained result identity')
        print(json.dumps({'verified': RESULT, 'query5': str(C5), 'haar9': result['exact_continuation']['haar9']}))


if __name__ == '__main__':
    main()
