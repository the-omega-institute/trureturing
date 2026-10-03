"""Seven prescribed private-prefix types; no source, parameter, or prime search."""
import argparse
import json
from fractions import Fraction as F
from math import prod
from pathlib import Path

checks = 0


def require(condition, message):
    global checks
    if not condition:
        raise ValueError(message)
    checks += 1


def is_prefix(a, b):
    return len(a) <= len(b) and a == b[:len(a)]


def union_mass(words, q):
    antichain = []
    for word in sorted(set(words), key=lambda w: (len(w), w)):
        if not any(is_prefix(old, word) for old in antichain):
            antichain.append(word)
    return sum((F(1, q ** len(word)) for word in antichain), F())


def intersection_mass(left, right, q):
    intersections = []
    for a in left:
        for b in right:
            if is_prefix(a, b):
                intersections.append(b)
            elif is_prefix(b, a):
                intersections.append(a)
    return union_mass(intersections, q)


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()

q = 11
private_primes = [11, 13, 17, 19, 23, 29, 31, 37, 41]
role_names = ['F5', 'S5', 'F7', 'S7']
deep_roles = [2, 4, 3, 5]
types = [
    ('empty', (2, 3, 4, 5), []),
    ('F5-F7', (2, 3, 2, 4), [(0, 2)]),
    ('F5-S7', (2, 3, 4, 2), [(0, 3)]),
    ('S5-F7', (2, 3, 3, 4), [(1, 2)]),
    ('S5-S7', (2, 3, 4, 3), [(1, 3)]),
    ('F5-F7,S5-S7', (2, 3, 2, 3), [(0, 2), (1, 3)]),
    ('F5-S7,S5-F7', (2, 3, 3, 2), [(0, 3), (1, 2)]),
]
pure = [(0,), (6, 0)]
star = [(1,), (6, 1)]
c = 1 / (1 - union_mass(pure, q))
b = c * (F(1, q) + F(1, q*q))
require(c == F(121, 109), 'incorrect fixed pure normalizer')
require(b == F(12, 109), 'incorrect fixed complete-role mass')
results = []
observed_types = set()
for name, digits, expected_edges in types:
    require(all(d not in (0, 1, 6) and 0 <= d < q for d in digits), 'forbidden first digit')
    require(digits[0] != digits[1] and digits[2] != digits[3], 'within-head collision')
    edges = [(i, j) for i in (0, 1) for j in (2, 3) if digits[i] == digits[j]]
    require(edges == expected_edges, 'wrong named incidence type')
    observed_types.add(tuple(edges))
    roles = [[(digits[i],), (6, deep_roles[i])] for i in range(4)]
    for role in roles:
        require(c * union_mass(role, q) == b, 'individual role mass changed')
        require(intersection_mass(role, pure + star, q) == 0, 'role hits pure or star')
    require(intersection_mass(roles[0], roles[1], q) == 0, 'head5 union no longer disjoint')
    require(intersection_mass(roles[2], roles[3], q) == 0, 'head7 union no longer disjoint')
    left, right = roles[0] + roles[1], roles[2] + roles[3]
    X, Y = c * union_mass(left, q), c * union_mass(right, q)
    overlap = c * intersection_mass(left, right, q)
    require(X == 2*b and Y == 2*b, 'same-head raw marginal mass changed')
    require(overlap == len(edges)*c/q, 'cross-head overlap formula failed')
    union = c * union_mass(left + right, q)
    require(union == X + Y - overlap, 'literal joint union failed')
    local_envelopes = []
    # Two fixed star states, not a search over sources or head addresses.
    for star_active in (False, True):
        g = 1 - (b if star_active else 0)
        H = g - union
        P, K = max(F(), g-X-Y), g-max(X, Y)
        require(0 <= P <= H <= K <= g, 'same-source envelopes failed')
        require(H == g-X-Y+len(edges)*c/q, 'exact complement correction failed')
        local_envelopes.append({'star_active': star_active, 'g': str(g),
                                'P': str(P), 'H': str(H), 'K': str(K)})
    results.append({'name': name, 'role_order': role_names, 'digits': digits,
                    'edges': [[role_names[i], role_names[j]] for i, j in edges],
                    'raw_X': str(X), 'raw_Y': str(Y), 'raw_overlap': str(overlap),
                    'local_all-role_envelopes': local_envelopes})
require(len(observed_types) == 7, 'seven types are not distinct')
counts = []
for p in private_primes:
    M = p-3
    empty = M*(M-1)*(M-2)*(M-3)
    single = M*(M-1)*(M-2)
    perfect = M*(M-1)
    total = (M*(M-1))**2
    require(empty + 4*single + 2*perfect == total, 'fixed-support counting identity failed')
    counts.append({'q': p, 'available_digits': M, 'empty': empty,
                   'each_single': single, 'each_perfect': perfect, 'total': total})

result = {
    'scope': 'Exactly seven prescribed prefix types at q=11, retained depth2. '
             'Literal prefix unions use an antichain calculation; no full-period enumeration. '
             'The all-N and uniform-continuation conclusions are proofs in the companion note. '
             'Formula counts use only the nine declared private primes.',
    'source_reference': 'Report528 FC147-FC152; fixed prefixes reproduced explicitly',
    'checks': checks,
    'local_q': q, 'local_depth': 2, 'pure_prefixes': pure, 'star_prefixes': star,
    'pure_normalizer': str(c), 'complete_role_mass': str(b),
    'types': results, 'per_prime_assignment_counts': counts,
    'global_named_incidence_types': 7 ** len(private_primes),
    'global_literal_assignments': prod(row['total'] for row in counts),
    'continuation_producer_rerun': False,
}
args.output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'checks': checks, 'output': str(args.output),
                  'global_named_incidence_types': result['global_named_incidence_types'],
                  'global_literal_assignments': result['global_literal_assignments']}, indent=2))
