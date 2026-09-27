"""Independent exact full-coordinate audit of the literal eleven-label family."""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import permutations, product
import argparse
import importlib.util
import json
import sys
sys.dont_write_bytecode = True
from pathlib import Path


CERTIFICATE = 'certificates/source_norms/source-budgets/adaptive_head_verification.json'
INPUT = 'frontier/source-budgets/adaptive_head_input_315.json'
CANDIDATE = 'frontier/source-budgets/adaptive_head_bellman.py'
CANDIDATE_CERTIFICATE = 'certificates/source_norms/source-budgets/adaptive_head_bellman.json'
SOURCES = ('certificate_io.py',
           'problem-details/55-adaptive-read-once-head-orders-with-unrestricted-tail-comparison.md',
           INPUT, 'frontier/source-budgets/depth_cap_bellman.py',
           CANDIDATE, CANDIDATE_CERTIFICATE)


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def fill(state, axis, value):
    return state[:axis] + (value,) + state[axis + 1:]


def crt(state):
    return sum(x * (315 // q) * pow(315 // q, -1, q)
               for x, q in zip(state, SIZES)) % 315


def original_bad(state):
    point = crt(state)
    return int(any(point % modulus == residue for modulus, residue in LABELS))


def calculate():
    from math import gcd
    require(tuple(m for m, _ in LABELS) == tuple(m for m in range(2, 316) if 315 % m == 0),
            'exact original nonunit divisors of 315')
    points = tuple(product(*(range(q) for q in SIZES)))
    require(len({crt(x) for x in points}) == 315, 'complete bijective original CRT')
    for state in points:
        coordinate_bad = int(any(all(x % gcd(modulus, q) == residue % gcd(modulus, q)
                                    for x, q in zip(state, SIZES))
                                 for modulus, residue in LABELS))
        require(original_bad(state) == coordinate_bad, 'original numerical and coordinate payoff agree')

    fixed = []
    for order in permutations(range(3)):
        @lru_cache(None)
        def fixed_value(depth, state):
            if depth == 3:
                return F(original_bad(state))
            axis = order[depth]
            costs = sorted(fixed_value(depth + 1, fill(state, axis, x))
                           for x in range(SIZES[axis]))
            return sum(costs[:KEEP[axis]], F(0)) / KEEP[axis]

        answer = fixed_value(0, (-1, -1, -1))
        fixed.append(dict(prime_order=[PRIMES[i] for i in order], bad_mass=str(answer),
                          actual_prefix_states=fixed_value.cache_info().currsize))
    require([row['bad_mass'] for row in fixed] == ['1/60', '1/30', '1/20', '1/30', '1/15', '1/15'],
            'independent six fixed-order values')

    policy = {}

    @lru_cache(None)
    def adaptive_value(state):
        if all(x >= 0 for x in state):
            return F(original_bad(state))
        candidates = []
        for axis in range(3):
            if state[axis] >= 0:
                continue
            ordered = sorted((adaptive_value(fill(state, axis, x)), x)
                             for x in range(SIZES[axis]))
            chosen = tuple(x for _, x in ordered[:KEEP[axis]])
            cost = sum((c for c, _ in ordered[:KEEP[axis]]), F(0)) / KEEP[axis]
            candidates.append((cost, axis, chosen))
        best, axis, chosen = min(candidates)
        policy[state] = (axis, chosen)
        return best

    optimum = adaptive_value((-1, -1, -1))
    require(optimum == 0, 'independent adaptive zero mass')
    require(optimum < min(F(row['bad_mass']) for row in fixed), 'strict advantage over every fixed order')
    support = defaultdict(F)
    histories = []

    def expand(state, weight, transcript):
        if all(x >= 0 for x in state):
            support[state] += weight
            return
        axis, chosen = policy[state]
        histories.append((state, weight, transcript, axis, chosen))
        for x in chosen:
            expand(fill(state, axis, x), weight / KEEP[axis], transcript + ((axis, x),))

    expand((-1, -1, -1), F(1), ())
    require(sum(support.values(), F(0)) == 1, 'actual reconstructed law normalized')
    require(len(support) == 60 and all(w == F(1, 60) for w in support.values()),
            '60 distinct actual CRT leaves, each mass 1/60')
    require(sum(w * original_bad(state) for state, w in support.items()) == optimum,
            'actual original forbidden union equals adaptive value')

    def follows(full, transcript):
        state = (-1, -1, -1)
        for axis, x in transcript:
            if policy[state][0] != axis or full[axis] != x:
                return False
            state = fill(state, axis, x)
        return True

    cap_checks = 0
    rows = []
    for state, weight, transcript, axis, chosen in histories:
        branch = {full: w for full, w in support.items() if follows(full, transcript)}
        require(sum(branch.values(), F(0)) == weight, 'actual transcript probability')
        row = [sum((w for full, w in branch.items() if full[axis] == x), F(0)) / weight
               for x in range(SIZES[axis])]
        require(row == [F(1, KEEP[axis]) if x in chosen else F(0) for x in range(SIZES[axis])],
                'actual conditional law agrees with selected normalized kernel')
        p, h, k = PRIMES[axis], HEIGHTS[axis], KEEP[axis]
        for e in range(h + 1):
            cap = min(F(1), F(p ** (h - e), k))
            for a in range(p ** e):
                mass = sum((row[x] for x in range(SIZES[axis]) if x % (p ** e) == a), F(0))
                require(mass <= cap, 'actual full-transcript depth cap')
                cap_checks += 1
        rows.append(dict(transcript=[[PRIMES[i], x] for i, x in transcript],
                         prefix_mass=str(weight), next_prime=p, selected_values=list(chosen)))
    depths = defaultdict(set)
    for _, _, history, axis, _ in histories:
        depths[len(history)].add(axis)
    require(any(len(axes) > 1 for axes in depths.values()), 'reachable policy order actually depends on observed values')
    return dict(schema='adaptive-original-315-independent-v1',
                scope='Ordinary exact finite calculation. Read-once coordinate selection from observed full coordinates; fixed literal original congruences and old flat caps. Does not change Chapter 54 or solve Erdos 7.',
                primes=PRIMES, heights=HEIGHTS, keep=KEEP, labels=LABELS,
                original_period=315, original_CRT_points_checked=len(points), fixed_order_results=fixed,
                adaptive_bad_mass=str(optimum), adaptive_actual_prefix_states=adaptive_value.cache_info().currsize,
                reachable_policy_rows=rows, full_transcript_depth_caps_checked=cap_checks,
                actual_support=[dict(coordinates=state, original_CRT_residue=crt(state), mass=str(w))
                                for state, w in sorted(support.items())],
                producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'readable certificate IO')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def verification(base):
    global PRIMES, HEIGHTS, SIZES, KEEP, LABELS
    io = load_module('independent_adaptive_certificate_io', base/'certificate_io.py')
    source_bytes = {name: io.read_artifact_bytes(base/name) for name in SOURCES}
    data = json.loads(source_bytes[INPUT], object_pairs_hook=io._unique)
    require(set(data) == {'schema', 'primes', 'heights', 'ks', 'labels', 'profiles'},
            'exact unique literal input fields')
    require(data['schema'] == 'adaptive-head-input-315-v1', 'literal input schema')
    require(all(type(x) is int for name in ('primes', 'heights', 'ks') for x in data[name]),
            'integer original coordinate data')
    PRIMES, HEIGHTS, KEEP = (tuple(data[name]) for name in ('primes', 'heights', 'ks'))
    require(PRIMES == (3, 5, 7) and HEIGHTS == (2, 1, 1) and KEEP == (4, 3, 5),
            'audited original coordinate dimensions and capacities')
    SIZES = tuple(p**h for p, h in zip(PRIMES, HEIGHTS))
    LABELS = tuple(tuple(row) for row in data['labels'])
    require(all(len(row) == 2 and all(type(x) is int for x in row)
                and row[0] > 1 and 0 <= row[1] < row[0] for row in LABELS),
            'literal original numerical classes')
    labels_hash = sha256(json.dumps(data['labels'], separators=(',', ':')).encode()).hexdigest()
    require(labels_hash == '6bf58b5cc0862ee95b92550a53ab093c9e5802eae5b11ae44cbc5e0748b01ad2',
            'same independently audited eleven original labels')
    profiles = [[str(min(F(1), F(p**(h-e), k))) for e in range(h+1)]
                for p, h, k in zip(PRIMES, HEIGHTS, KEEP)]
    require(data['profiles'] == profiles, 'exact old flat profiles, all depths retained')
    candidate = json.loads(source_bytes[CANDIDATE_CERTIFICATE], object_pairs_hook=io._unique)
    require(candidate['schema'] == 'adaptive-head-bellman-v1', 'candidate semantic schema')
    require(candidate['producer_sha256'] == sha256(source_bytes[CANDIDATE]).hexdigest(),
            'current candidate producer')
    require(set(SOURCES) - {CANDIDATE, CANDIDATE_CERTIFICATE} <= set(candidate['source_sha256']),
            'candidate declares the complete required input and mathematical source bindings')
    for name, digest in candidate['source_sha256'].items():
        raw = io.read_artifact_bytes(base/name)
        require(sha256(raw).hexdigest() == digest, 'current candidate source dependency: ' + name)
        if name in source_bytes:
            require(source_bytes[name] == raw, 'unchanged shared source dependency')
        source_bytes[name] = raw
    require(all(candidate[name] == data[name] for name in ('primes', 'heights', 'ks', 'profiles')),
            'candidate uses the same original coordinates and profiles')
    require(candidate['original_labels_sha256'] == labels_hash, 'candidate uses the unique literal label source')
    require(candidate['original_label_source'] == INPUT and candidate['original_label_count'] == 11
            and candidate['original_period'] == 315, 'candidate original-label provenance and full period')

    result = calculate()
    independent_fixed = [dict(order=row['prime_order'], value=row['bad_mass'])
                         for row in result['fixed_order_results']]
    require(candidate['fixed_values'] == independent_fixed,
            'six independent exact fixed-order minima match candidate')
    require(candidate['adaptive_value'] == result['adaptive_bad_mass'] == '0',
            'independent adaptive zero minimum matches candidate')
    support = sorted(row['original_CRT_residue'] for row in result['actual_support'])
    require(candidate['crt_support'] == support and candidate['each_point_mass'] == '1/60',
            'identical complete original CRT support and point masses')
    independent_rows = [dict(history=row['transcript'], next_prime=row['next_prime'],
                             selected_residues=row['selected_values'],
                             each_probability=str(F(1, KEEP[PRIMES.index(row['next_prime'])])))
                        for row in result['reachable_policy_rows']]
    require(candidate['rows'] == independent_rows, 'identical full reachable adaptive conditional policy')
    violations = candidate['fixed_order_cap_violations']
    require(len(violations) == 6 and {tuple(row['order']) for row in violations} ==
            set(permutations(PRIMES)), 'one actual cap obstruction for each fixed order')
    for row in violations:
        order, prefix, p = row['order'], row['prefix'], row['prime']
        require(len(prefix) < len(order) and order[len(prefix)] == p,
                'fixed-order obstruction identifies its actual next coordinate')
        require(all(type(x) is int and 0 <= x < SIZES[PRIMES.index(q)]
                    for q, x in zip(order, prefix)), 'valid fixed-order prefix residues')
        branch = [x for x in support if all(x % SIZES[PRIMES.index(q)] == a
                                           for q, a in zip(order, prefix))]
        require(branch, 'positive-probability fixed-order prefix')
        actual = F(sum(x % SIZES[PRIMES.index(p)] == row['residue'] for x in branch), len(branch))
        allowed = F(1, KEEP[PRIMES.index(p)])
        require(actual == F(row['conditional_probability']) > allowed == F(row['allowed_atom_cap']),
                'independently recomputed actual fixed-order cap violation')
    require(all(io.read_artifact_bytes(base/name) == raw for name, raw in source_bytes.items()),
            'all verification sources unchanged during calculation')
    result.update(schema='adaptive-head-verification-v1', profiles=profiles,
                  original_label_source=INPUT, original_labels_sha256=labels_hash,
                  candidate_fixed_order_cap_violations_checked=len(violations),
                  source_sha256={name: sha256(raw).hexdigest() for name, raw in source_bytes.items()})
    result['scope'] += (' Full-transcript caps and fixed original labels are required. '
                        'Existing unrestricted-tail charges retain their numerical prime schedule. '
                        'The old 154-label atom-cap obstruction is unaffected.')
    return json.loads(json.dumps(result))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io = load_module('independent_adaptive_output_io', args.base/'certificate_io.py')
    result = verification(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(path), object_pairs_hook=io._unique),
                'exact independent adaptive-head verification replay')
    print(json.dumps({name: value for name, value in result.items()
                      if name not in ('reachable_policy_rows', 'actual_support', 'labels')}, indent=2))


if __name__ == '__main__':
    main()
