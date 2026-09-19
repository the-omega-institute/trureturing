"""Exact CPI tree optimization and checkable branch-price certificates.

No external dependencies. Run Python with -I -O; checks do not use assert.
Arithmetic uses integers and Fractions. All fixture objectives are independently
evaluated by summing the literal square over leaves.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from collections import defaultdict
from fractions import Fraction as F
from functools import cache
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import random


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def make_tree(p, H, leaves):
    require(isinstance(p, int) and p > 1, "invalid base")
    require(isinstance(H, int) and H >= 0, "invalid height")
    mass = defaultdict(F)
    for x, weight in leaves.items():
        require(isinstance(x, int) and 0 <= x < p**H, "leaf outside period")
        require(weight >= 0, "negative row weight")
        if weight:
            for e in range(H + 1):
                mass[e, x % p**e] += F(weight)
    child = {v: [] for v in mass}
    child.setdefault((0, 0), [])
    for e, x in mass:
        if e:
            child[e - 1, x % p**(e - 1)].append((e, x))
    for children in child.values():
        children.sort()
    levels = [sorted(v for v in mass if v[0] == e) for e in range(H + 1)]
    maxima = [max((mass[v] for v in level), default=F(0)) for level in levels]
    envelope = sum((2*e + 1)*maxima[e] for e in range(1, H + 1))
    return dict(mass), child, levels, envelope


def exact_subset_dp(mass, child, H):
    """Return max integral(N^2+2N), a maximizing tuple, and DP counters."""
    operations = 0
    stored_entries = 0
    all_depths = (1 << H) - 1

    @cache
    def table(v, a):
        nonlocal operations, stored_entries
        e = v[0]
        future_depths = all_depths ^ ((1 << e) - 1)
        result = {}
        for chosen in ([False, True] if e else [False]):
            base = (3 + 2*a)*mass[v] if chosen else F(0)
            aa = a + int(chosen)
            partial = {0: (F(0), ())}
            for u in child[v]:
                child_table = table(u, aa)
                updated = {}
                for assigned, (score, witness) in partial.items():
                    available = future_depths ^ assigned
                    sub = available
                    while True:
                        operations += 1
                        val = child_table.get(sub)
                        if val is not None:
                            key = assigned | sub
                            candidate = score + val[0], witness + val[1]
                            if key not in updated or candidate[0] > updated[key][0]:
                                updated[key] = candidate
                        if not sub:
                            break
                        sub = (sub - 1) & available
                partial = updated
            for mask, (score, witness) in partial.items():
                own_bit = (1 << (e - 1)) if chosen else 0
                result[mask | own_bit] = base + score, ((v,) if chosen else ()) + witness
        stored_entries += len(result)
        return result

    if not mass:
        return F(0), (), {"node_ancestor_tables": 0, "table_entries": 0,
                          "convolution_trials": 0}
    answer = table((0, 0), 0).get(all_depths)
    require(answer is not None, "missing feasible full-depth tuple")
    return answer[0], answer[1], {
        "node_ancestor_tables": table.cache_info().currsize,
        "table_entries": stored_entries,
        "convolution_trials": operations,
    }


def price_dp(mass, child, H, prices, fixed=None):
    """Bellman upper certificate, optionally fixing one node at some depths.

    At a fixed depth, that node is forced in and all its peers forced out.
    The corresponding price must be zero. Free depths have no cardinality
    constraint inside this relaxed oracle. Prices can have either sign.
    """
    fixed = {} if fixed is None else dict(fixed)
    require(len(prices) == H, "wrong price dimension")
    for e, v in fixed.items():
        require(v in mass and v[0] == e and 1 <= e <= H, "invalid fixed node")
        require(prices[e - 1] == 0, "fixed depth charged twice")

    @cache
    def rec(v, a):
        e = v[0]
        no = sum(rec(u, a) for u in child[v])
        if not e:
            return no
        yes = ((3 + 2*a)*mass[v] - prices[e - 1]
               + sum(rec(u, a + 1) for u in child[v]))
        if e in fixed:
            return yes if v == fixed[e] else no
        return max(no, yes)

    if not mass:
        return F(0), 0
    bound = rec((0, 0), 0) + sum(prices)
    return bound, rec.cache_info().currsize


def direct_score(p, leaves, selected):
    """Literal leaf objective, without using prefix masses or ancestry pairs."""
    return sum(F(weight)*(n*n + 2*n)
               for x, weight in leaves.items()
               for n in [sum(x % p**e == a for e, a in selected)])


def brute_tuple_max(p, H, leaves, levels):
    if not any(leaves.values()):
        return F(0), 1
    best = F(-1)
    count = 0
    for selected in product(*levels[1:]):
        best = max(best, direct_score(p, leaves, selected))
        count += 1
    return best, count


def fixture(S, expected_omega):
    p, H = 17, 3
    leaves = {x: F(1) for x in S}
    mass, child, levels, envelope = make_tree(p, H, leaves)
    score, selected, stats = exact_subset_dp(mass, child, H)
    brute, tuples = brute_tuple_max(p, H, leaves, levels)
    require(score == brute == direct_score(p, leaves, selected), "fixture DP mismatch")
    require(envelope - score == expected_omega, "fixture Omega mismatch")
    return leaves, mass, child, levels, envelope, score, stats, tuples


def literal_arithmetic(S):
    """Reconstruct CPI5's original odd moduli and the actual row at old x=1."""
    prime_powers = [(3, 4), (5, 2), (7, 1), (11, 1), (13, 1)]
    Q = 1
    divisors = [1]
    phi = 1
    for prime, exponent in prime_powers:
        Q *= prime**exponent
        phi *= (prime - 1)*prime**(exponent - 1)
        divisors = [d*prime**e for d in divisors for e in range(exponent + 1)]
    divisors.sort()
    nonunit = [d for d in divisors if d != 1]
    require((Q, len(divisors), phi) == (2027025, 120, 777600), "old carrier counts")
    p, H = 17, 3
    prefixes = {e: {x % p**e for x in S} for e in range(1, H + 1)}
    # The pure root0 is excluded separately. At later depths delete the children
    # of retained parents that do not occur in the target support.
    masks = {1: sorted(set(range(1, p)) - prefixes[1])}
    for e in range(2, H + 1):
        candidates = {a + p**(e - 1)*j for a in prefixes[e - 1] for j in range(p)}
        masks[e] = sorted(candidates - prefixes[e])
    require([len(masks[e]) for e in range(1, H + 1)] == [14, 27, 110],
            "mixed-mask count mismatch")
    forbidden = [(d, 0) for d in nonunit]
    forbidden += [(p**e, 0) for e in range(1, H + 1)]
    mixed = []
    for e in range(1, H + 1):
        require(len(masks[e]) <= len(nonunit), "insufficient distinct original cofactors")
        for d, y in zip(nonunit, masks[e]):
            current_modulus = p**e
            modulus = d*current_modulus
            residue = (1 + d*((y - 1)*pow(d, -1, current_modulus) % current_modulus)) % modulus
            require(residue % d == 1 and residue % current_modulus == y,
                    "CRT reconstruction failed")
            forbidden.append((modulus, residue))
            mixed.append((d, current_modulus, residue))
    require(len(forbidden) == 273, "forbidden label count")
    require(len({m for m, _ in forbidden}) == len(forbidden), "repeated original modulus")
    require(all(m > 1 and m % 2 and 0 <= a < m for m, a in forbidden),
            "invalid original odd congruence")
    complete_labels = [d*p**e for d in divisors for e in range(H + 1)]
    require(len(complete_labels) == len(set(complete_labels)) == 480,
            "complete original test inventory")
    # At x=1 every old nonunit zero class is avoided. Reconstruct the joint CRT
    # point for each current leaf, and test every actual original congruence.
    survivors = []
    pure_count = 0
    for y in range(p**H):
        joint = (1 + Q*((y - 1)*pow(Q, -1, p**H) % p**H)) % (Q*p**H)
        require(joint % Q == 1 and joint % p**H == y, "joint CRT point")
        if y % p:
            pure_count += 1
        if all(joint % m != residue for m, residue in forbidden):
            survivors.append(y)
    require(survivors == sorted(S), "literal original family survivor mismatch")
    require(pure_count == (p - 1)*p**(H - 1) == 4624, "pure survivor count")
    alpha = F(pure_count - len(survivors), pure_count)
    delta = F(8 - 1, p - 2)
    gain = 1/(1 - min(alpha, delta))
    weight = gain/pure_count
    require(weight == F(15, 36992), "actual AP/T8 leaf weight")
    require((envelope := make_tree(p, H, {x: weight for x in S})[3]) == 40*weight,
            "weighted prefix envelope")
    encoded = json.dumps(sorted(forbidden), separators=(",", ":")).encode("ascii")
    return {
        "Q": Q, "old_uniform_unit_count": phi, "old_test_labels": len(divisors),
        "forbidden_odd_moduli": len(forbidden), "complete_test_labels": len(complete_labels),
        "mixed_masks_by_depth": [len(masks[e]) for e in range(1, H + 1)],
        "pure_current_leaves": pure_count, "surviving_current_leaves": survivors,
        "alpha": str(alpha), "delta_T8": str(delta), "killed_leaf_weight": str(weight),
        "original_family_sha256": hashlib.sha256(encoded).hexdigest(),
    }


def main():
    S = [1, 2, 18, 35, 52, 69, 86, 291, 580]
    Sprime = [1, 290, 579, 18, 35, 52, 2, 19, 36]
    a = fixture(S, F(8))
    b = fixture(Sprime, F(0))
    arith_a, arith_b = literal_arithmetic(S), literal_arithmetic(Sprime)
    leaves, mass, child, levels, envelope, score, stats, tuples = a
    upper, states = price_dp(mass, child, 3, [F(18), F(6), F(6)])
    require(upper == 33 and envelope - upper == 7, "unbranched price certificate")
    unbranched_upper = upper
    branches = []
    for root, prices, expected in [((1, 1), [0, 9, 5], 32), ((1, 2), [0, 15, 7], 31)]:
        bound, nstates = price_dp(mass, child, 3, list(map(F, prices)), {1: root})
        require(bound == expected, "branched certificate")
        branches.append({"root": list(root), "prices": prices,
                         "score_upper": int(bound), "bellman_states": nstates})
    require(max(x["score_upper"] for x in branches) == score, "branch cover mismatch")

    # Three actual selected subsets certify the optimum scalar-price relaxation.
    mixture = [
        [(1, 1), (1, 2), (2, 2), (3, 2), (3, 291), (3, 580)],
        [(2, 2)],
        [(1, 1), (2, 2)],
    ]
    mix_scores = [direct_score(17, leaves, z) for z in mixture]
    mix_counts = [[sum(e == d for e, _ in z) for d in range(1, 4)] for z in mixture]
    require(mix_scores == [63, 9, 27], "dual obstruction scores")
    require([sum(z[d] for z in mix_counts) for d in range(3)] == [3, 3, 3],
            "dual obstruction mean counts")
    require(sum(mix_scores)/3 == upper, "dual obstruction average")

    # Independent literal-square comparisons for every binary depth3 support.
    exhaustive_rows = 0
    for bitmask in range(256):
        row = {x: F(bool(bitmask & (1 << x))) for x in range(8)}
        m, c, ls, env = make_tree(2, 3, row)
        exact, witness, _ = exact_subset_dp(m, c, 3)
        brute, _ = brute_tuple_max(2, 3, row, ls)
        require(exact == brute, "exhaustive support mismatch")
        require(env >= exact, "negative Omega")
        exhaustive_rows += 1

    rng = random.Random(718039)
    weighted_rows = 0
    for p, H, count in [(2, 4, 40), (3, 3, 40)]:
        for _ in range(count):
            row = {x: F(rng.randrange(5), rng.randrange(1, 5)) for x in range(p**H)}
            m, c, ls, env = make_tree(p, H, row)
            exact, witness, _ = exact_subset_dp(m, c, H)
            brute, _ = brute_tuple_max(p, H, row, ls)
            require(exact == brute == direct_score(p, row, witness), "weighted DP mismatch")
            prices = [F(rng.randrange(-4, 30), rng.randrange(1, 5)) for _ in range(H)]
            bound, _ = price_dp(m, c, H, prices)
            require(exact <= bound, "invalid price bound")
            # Root branching, retaining every occupied root.
            root_bounds = [price_dp(m, c, H, [F(0)] + prices[1:], {1: root})[0]
                           for root in ls[1]]
            require(exact <= max(root_bounds), "invalid branch cover")
            weighted_rows += 1

    # Independently exhaust ALL unrestricted selected subsets for small trees.
    unrestricted_rows = 0
    for _ in range(20):
        row = {x: F(rng.randrange(4), rng.randrange(1, 4)) for x in range(8)}
        m, c, ls, _ = make_tree(2, 3, row)
        nodes = [v for v in m if v[0]]
        prices = [F(rng.randrange(-3, 12), rng.randrange(1, 4)) for _ in range(3)]
        relaxed_best = max(direct_score(2, row, selected)
                           - sum(prices[e - 1] for e, _ in selected)
                           for mask in range(1 << len(nodes))
                           for selected in [[v for i, v in enumerate(nodes) if mask & (1 << i)]])
        upper, _ = price_dp(m, c, 3, prices)
        require(upper == relaxed_best + sum(prices), "unrestricted Bellman mismatch")
        unrestricted_rows += 1

    output = {
        "schema": "cpi-prefix-correction-v1",
        "S": {"envelope_score": int(envelope), "exact_score": int(score),
              "exact_omega": int(envelope-score), "complete_tuples": tuples,
              "subset_dp": stats, "unbranched_upper": int(unbranched_upper),
              "unbranched_omega_lower": 7, "unbranched_bellman_states": states,
              "branch_certificates": branches, "optimal_scalar_dual_score": 33,
              "literal_arithmetic": arith_a},
        "Sprime": {"envelope_score": int(b[4]), "exact_score": int(b[5]),
                   "exact_omega": int(b[4]-b[5]), "subset_dp": b[6],
                   "literal_arithmetic": arith_b},
        "independent_checks": {"binary_depth3_supports": exhaustive_rows,
                               "rational_weighted_rows": weighted_rows,
                               "all_subset_price_oracles": unrestricted_rows},
        "arithmetic": "exact integers and fractions; ordinary computation, not Lean",
    }
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", nargs="?", type=Path,
                        default=(Path(__file__).resolve().parent / 'certificates/prefix_correction_certificate.json'))
    parser.add_argument("--emit-certificate", action="store_true",
                        help="recompute exact fixture data and emit a candidate certificate")
    args = parser.parse_args()
    if not args.emit_certificate:
        def unique_pairs(pairs):
            out = {}
            for key, value in pairs:
                require(key not in out, "duplicate JSON certificate key")
                out[key] = value
            return out
        expected = json.loads(read_artifact_text(args.certificate), object_pairs_hook=unique_pairs)
        require(expected == output, "certificate differs from independently recomputed data")
    print(json.dumps(output, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
