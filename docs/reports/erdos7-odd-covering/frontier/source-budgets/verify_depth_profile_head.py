"""Independent exact full-leaf verification of the fixed depth-profile head.

Original labels come from the canonical literal producer. The candidate
solver is not imported: every actual local leaf is evaluated and allocated
through all its actual ancestor capacities using exact integer arithmetic.
"""
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from math import gcd, lcm, prod
from pathlib import Path
import argparse
import importlib.util
import json
import sys
sys.dont_write_bytecode = True

CERTIFICATE = 'certificates/source_norms/source-budgets/depth_profile_head_verification.json'
INPUT = 'frontier/source-budgets/depth_profile_head_input.json'
LABEL_SOURCE = 'frontier/source-budgets/capped_head_bellman.py'
CANDIDATE = 'frontier/source-budgets/depth_cap_bellman.py'
CANDIDATE_CERTIFICATE = 'certificates/source_norms/source-budgets/depth_cap_bellman.json'
SOURCES = ('certificate_io.py',
           'problem-details/54-depth-profile-head-laws-with-unrestricted-original-tails.md',
           INPUT, LABEL_SOURCE, CANDIDATE, CANDIDATE_CERTIFICATE)


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def unique(pairs):
    output = {}
    for key, value in pairs:
        require(key not in output, 'duplicate JSON key')
        output[key] = value
    return output


def factor(n):
    answer = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            answer[p] = answer.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        answer[n] = answer.get(n, 0) + 1
    return answer


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'readable independent-verifier source')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def calculate(base):
    io = load_module('independent_depth_profile_certificate_io', base/'certificate_io.py')
    source_bytes = {name: io.read_artifact_bytes(base/name) for name in SOURCES}
    record = json.loads(source_bytes[INPUT], object_pairs_hook=io._unique)
    require(set(record) == {'schema', 'head_label_source', 'head_label_factory',
                            'prime_order', 'heights', 'profiles'}, 'exact profile input fields')
    require(record['schema'] == 'depth-profile-head-input-v1', 'profile input schema')
    require(record['head_label_source'] == LABEL_SOURCE and
            record['head_label_factory'] == 'counterexample_154_labels', 'canonical original label input')
    literal = load_module('independent_depth_profile_literal_labels', base/LABEL_SOURCE)
    literal_labels = literal.counterexample_154_labels()
    original = dict(labels=literal_labels, prime_order=record['prime_order'], heights=record['heights'])
    candidate = json.loads(source_bytes[CANDIDATE_CERTIFICATE], object_pairs_hook=io._unique)
    require(candidate['schema'] == 'depth-cap-bellman-v1', 'candidate certificate schema')
    require(candidate['producer_sha256'] == sha256(source_bytes[CANDIDATE]).hexdigest(), 'current candidate source')
    for name, digest in candidate['source_sha256'].items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == digest,
                'current candidate source dependency: ' + name)
    require(candidate['prime_order'] == record['prime_order'] and
            candidate['heights'] == record['heights'] and candidate['profiles'] == record['profiles'],
            'candidate cert uses this exact original source/profile')
    require(candidate['original_label_source'] == LABEL_SOURCE and candidate['original_label_count'] == 154,
            'candidate original label provenance')
    require(candidate['original_labels_sha256'] == sha256(json.dumps(literal_labels,separators=(',',':')).encode()).hexdigest(),
            'candidate actual original labels')
    budget = dict(profiles=record['profiles'], epsilon_exact=candidate['epsilon_exact'])
    labels = tuple(tuple(pair) for pair in original['labels'])
    factorizations = [factor(n) for n, _ in labels]
    primes = tuple(sorted(set().union(*(set(f) for f in factorizations))))
    heights = tuple(max(f.get(p, 0) for f in factorizations) for p in primes)
    require(list(primes) == original['prime_order'] and list(heights) == original['heights'], 'derived original primes/heights')
    require(len(labels) == len(set(n for n, _ in labels)) == 154, '154 distinct original numerical moduli')
    require(all(n > 1 and n % 2 and 0 <= a < n for n, a in labels), 'actual original odd classes')
    normalized = ''.join(f'{n}:{a}\n' for n, a in labels)
    require(sha256(normalized.encode()).hexdigest() == 'ae00ed2c19a8e06b4ccdcdd186a70d85e8f2aafaa1b0043c63e1d3780e877f42', 'same independently verified original154 literal table')
    profiles = tuple(tuple(Fraction(x) for x in row) for row in budget['profiles'])
    sizes = tuple(p ** h for p, h in zip(primes, heights))
    require(len(profiles) == len(primes), 'profile coordinate count')
    for p, h, row in zip(primes, heights, profiles):
        require(len(row) == h + 1 and row[0] == 1, 'profile shape/root')
        require(all(Fraction(1, p ** e) <= row[e] <= row[e - 1] for e in range(1, h + 1)), 'feasible monotone actual depth caps')
    require(prod(sizes) == lcm(*(n for n, _ in labels)), 'full original lcm, no truncated height')
    units = tuple(lcm(*(x.denominator for x in row)) for row in profiles)
    suffix_denominators = tuple(prod(units[axis:]) for axis in range(len(primes) + 1))
    last = tuple(max(i for i, p in enumerate(primes) if p in f) for f in factorizations)
    completed = tuple(sum(1 << j for j, final in enumerate(last) if final < axis)
                      for axis in range(len(primes) + 1))
    local_match = []
    leaf_paths = []
    initial_capacities = []
    for axis, (p, h, size, row, denominator) in enumerate(zip(primes, heights, sizes, profiles, units)):
        literal_moduli = tuple(gcd(n, size) for n, _ in labels)
        local_match.append(tuple(sum(1 << j for j, ((_, a), q) in enumerate(zip(labels, literal_moduli))
                                          if leaf % q == a % q)
                                 for leaf in range(size)))
        offsets = []
        capacities = []
        for e, cap in enumerate(row):
            offsets.append(len(capacities))
            amount = cap * denominator
            require(amount.denominator == 1, 'exact integer capacity units')
            capacities.extend([amount.numerator] * (p ** e))
        initial_capacities.append(tuple(capacities))
        leaf_paths.append(tuple(tuple(offsets[e] + leaf % (p ** e) for e in range(h + 1))
                               for leaf in range(size)))

    leaf_evaluations = allocated_leaves = binding_checks = nonterminal_rows = 0

    @lru_cache(None)
    def value(axis, active):
        nonlocal leaf_evaluations, allocated_leaves, binding_checks, nonterminal_rows
        if not active:
            return 0
        if active & completed[axis]:
            return suffix_denominators[axis]
        require(axis < len(primes), 'actual terminal original union')
        costs = tuple(value(axis + 1, active & mask) for mask in local_match[axis])
        leaf_evaluations += len(costs)
        remaining = list(initial_capacities[axis])
        objective = 0
        selected = 0
        # Greedy on actual leaves, retaining every ancestor's absolute cap.
        for leaf in sorted(range(sizes[axis]), key=lambda a: (costs[a], a)):
            path = leaf_paths[axis][leaf]
            amount = min(remaining[node] for node in path)
            if amount:
                for node in path:
                    remaining[node] -= amount
                    require(remaining[node] >= 0, 'actual selected mass respects every ancestor capacity')
                    binding_checks += 1
                selected += amount
                objective += amount * costs[leaf]
                allocated_leaves += 1
            if remaining[0] == 0:
                break
        require(selected == units[axis] and remaining[0] == 0, 'actual normalized conditional row')
        nonterminal_rows += 1
        return objective

    numerator = value(0, (1 << len(labels)) - 1)
    actual = Fraction(numerator, suffix_denominators[0])
    expected = Fraction(850282109320449012581343404003218456990123,
                        2126237451649555718697975632038158000000000)
    require(actual == expected == Fraction(budget['epsilon_exact']), 'independent NEW-profile154 optimum exact equality')
    require(candidate['original_period'] == prod(sizes), 'candidate actual full period')
    require(candidate['states'] == value.cache_info().currsize, 'candidate original-label state count')
    require(actual < Fraction(2, 5), 'verified head mass below two fifths')
    require(all(io.read_artifact_bytes(base/name) == raw for name, raw in source_bytes.items()),
            'verification sources unchanged during evaluation')
    result = dict(schema='depth-profile-head-verification-v1',
                  scope='Independent full-local-leaf laminar-cap Bellman evaluation for the canonical fixed 154-label head and supplied depth profile. Exact original-label payoff and normalized feasible conditional allocations; tail-budget verification is separate.',
                  original_label_count=len(labels), original_label_source=LABEL_SOURCE,
                  original_labels_sha256=sha256(json.dumps(literal_labels,separators=(',',':')).encode()).hexdigest(),
                  normalized_original_labels_sha256=sha256(normalized.encode()).hexdigest(),
                  prime_order=list(primes), heights=list(heights), original_period=prod(sizes),
                  profiles=[[str(x) for x in row] for row in profiles],
                  epsilon_exact=str(actual), candidate_epsilon_exact=candidate['epsilon_exact'],
                  states=value.cache_info().currsize, nonterminal_rows=nonterminal_rows,
                  actual_coordinate_leaf_evaluations=leaf_evaluations,
                  positive_selected_leaf_allocations=allocated_leaves,
                  exact_ancestor_capacity_subtractions_checked=binding_checks,
                  row_capacity_denominator_units=list(units),
                  source_sha256={name:sha256(raw).hexdigest() for name,raw in source_bytes.items()},
                  producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io = load_module('independent_depth_profile_output_io', args.base/'certificate_io.py')
    result = calculate(args.base)
    path = args.base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path, json.dumps(result, indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(path), object_pairs_hook=io._unique),
                'exact independent depth-profile head verification replay')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
