#!/usr/bin/env python3
"""Exact comparison of canonical-digit and full-prime-block AP resampling.

The only mathematical inputs are the literal original congruences below.
Both chains, their complete terminal laws, and graph-polynomial certificates
are constructed with standard-library rational arithmetic. No external data
is read. Running this file writes its sibling JSON deterministically.

The HLS matching-reduced certificate is a computed polynomial value here;
this experiment does not assert a general HLS output-distribution theorem.
"""

from fractions import Fraction as F
from itertools import combinations, product
from math import lcm, prod
from pathlib import Path
import json


PRIME_EXCLUSIONS = ((0, 3), (0, 5), (0, 7))
BAD_APS = ((1, 9), (1, 15), (1, 21))
QUERY_APS = (
    ("C5", ((2, 5),)),
    ("C7", ((2, 7),)),
    ("C5_intersect_C7", ((2, 5), (2, 7))),
)
MATCHING = ((9, 15),)


def prime_powers(n):
    result = {}
    divisor = 2
    while divisor * divisor <= n:
        while n % divisor == 0:
            result[divisor] = result.get(divisor, 0) + 1
            n //= divisor
        divisor += 1
    if n > 1:
        result[n] = 1
    return result


PERIOD = lcm(*(m for _, m in PRIME_EXCLUSIONS + BAD_APS))
HEIGHTS = prime_powers(PERIOD)
LABELS = tuple(m for _, m in BAD_APS)
RESIDUES = dict((m, a) for a, m in BAD_APS)
SOURCE = tuple(x for x in range(PERIOD)
               if all(x % m != a for a, m in PRIME_EXCLUSIONS))
INITIAL = F(1, len(SOURCE))
ACTIVE = {x: tuple(m for m in LABELS if x % m == RESIDUES[m])
          for x in SOURCE}
TRANSIENT = tuple(x for x in SOURCE if ACTIVE[x])
ABSORBING = frozenset(x for x in SOURCE if not ACTIVE[x])


def powerset(items):
    items = tuple(items)
    for size in range(len(items) + 1):
        yield from combinations(items, size)


class CoordinateModel:
    """Two product-coordinate presentations of the same conditioned Haar law."""

    def __init__(self, kind):
        self.kind = kind
        self.coordinates = tuple(
            (p, j) for p, height in HEIGHTS.items()
            for j in (range(height) if kind == "canonical_digit" else (height,))
        )
        if kind == "canonical_digit":
            self.domains = tuple(tuple(range(1 if j == 0 else 0, p))
                                 for p, j in self.coordinates)
        else:
            self.domains = tuple(tuple(a for a in range(p ** height) if a % p)
                                 for p, height in self.coordinates)
        self.scopes = {
            m: tuple(i for i, (p, j) in enumerate(self.coordinates)
                     if (j < prime_powers(m).get(p, 0)
                         if kind == "canonical_digit" else m % p == 0))
            for m in LABELS
        }
        coordinate_states = tuple(product(*self.domains))
        assert len(coordinate_states) == len(SOURCE)
        assert {self.decode(s) for s in coordinate_states} == set(SOURCE)
        assert all(self.decode(self.encode(x)) == x for x in SOURCE)
        assert all(self.encode(self.decode(s)) == s for s in coordinate_states)
        assert F(1, prod(map(len, self.domains))) == INITIAL

    def encode(self, x):
        if self.kind == "canonical_digit":
            return tuple((x // p ** j) % p for p, j in self.coordinates)
        return tuple(x % p ** height for p, height in self.coordinates)

    def decode(self, state):
        blocks = {}
        for (p, j), value in zip(self.coordinates, state):
            blocks[p] = blocks.get(p, 0) + (
                value * p ** j if self.kind == "canonical_digit" else value)
        return sum(a * (PERIOD // p ** HEIGHTS[p])
                   * pow(PERIOD // p ** HEIGHTS[p], -1, p ** HEIGHTS[p])
                   for p, a in blocks.items()) % PERIOD

    def assignment(self, congruences):
        assert self.kind == "canonical_digit"
        fixed = {}
        for residue, modulus in congruences:
            assert PERIOD % modulus == 0
            heights = prime_powers(modulus)
            for i, (p, j) in enumerate(self.coordinates):
                if j < heights.get(p, 0):
                    value = (residue // p ** j) % p
                    assert value in self.domains[i]
                    assert i not in fixed or fixed[i] == value
                    fixed[i] = value
        for x in SOURCE:
            assert (all(x % m == a for a, m in congruences)
                    == all(self.encode(x)[i] == a for i, a in fixed.items()))
        return fixed

    def transition(self, x, label):
        indices = self.scopes[label]
        probability = F(1, prod(len(self.domains[i]) for i in indices))
        row = {}
        for draws in product(*(self.domains[i] for i in indices)):
            target = list(self.encode(x))
            for i, value in zip(indices, draws):
                target[i] = value
            y = self.decode(target)
            row[y] = row.get(y, F()) + probability
        assert sum(row.values()) == 1
        return row


def solve_exact(matrix, rhs):
    """Gauss-Jordan elimination over Q, with no floating-point operations."""
    n = len(rhs)
    a = [list(row) + [rhs[i]] for i, row in enumerate(matrix)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if a[i][j])
        a[j], a[pivot] = a[pivot], a[j]
        divisor = a[j][j]
        a[j] = [value / divisor for value in a[j]]
        for i in range(n):
            if i != j and a[i][j]:
                factor = a[i][j]
                a[i] = [x - factor * y for x, y in zip(a[i], a[j])]
    return tuple(row[-1] for row in a)


def terminal_law(model):
    kernels = {x: model.transition(x, min(ACTIVE[x])) for x in TRANSIENT}
    continuation = max(sum(prob for y, prob in row.items() if ACTIVE[y])
                       for row in kernels.values())
    assert continuation <= F(1, 2)  # Uniform geometric absorption guarantee.
    q = [[kernels[x].get(y, F()) for y in TRANSIENT] for x in TRANSIENT]
    matrix = [[F(i == j) - q[j][i] for j in range(len(TRANSIENT))]
              for i in range(len(TRANSIENT))]
    visits = dict(zip(TRANSIENT, solve_exact(matrix, [INITIAL] * len(TRANSIENT))))
    visit_residual = max(abs(visits[y] - INITIAL - sum(
        visits[x] * kernels[x].get(y, F()) for x in TRANSIENT)) for y in TRANSIENT)
    assert visit_residual == 0 and all(v >= 0 for v in visits.values())
    terminal = {x: INITIAL if x in ABSORBING else F() for x in SOURCE}
    for x, row in kernels.items():
        for y, probability in row.items():
            if y in ABSORBING:
                terminal[y] += visits[x] * probability
    flow_residual = max(abs(terminal[y] - INITIAL - sum(
        visits[x] * kernels[x].get(y, F()) for x in TRANSIENT)) for y in ABSORBING)
    assert flow_residual == 0 and sum(terminal.values()) == 1
    assert all(terminal[x] == 0 for x in TRANSIENT)
    assert all(terminal[x] > 0 for x in ABSORBING)
    return terminal, visits, {
        "coordinate_kind": model.kind,
        "coordinate_parameters_prime_and_digit_index_or_block_height": model.coordinates,
        "coordinate_domains": model.domains,
        "resampling_scopes": model.scopes,
        "policy": "Resample the smallest currently true numerical AP label.",
        "expected_resamplings": sum(visits.values()),
        "expected_resamplings_by_label": {
            m: sum(v for x, v in visits.items() if min(ACTIVE[x]) == m) for m in LABELS},
        "terminal_mass_classes": {
            str(value): sum(v == value for v in terminal.values())
            for value in sorted(set(terminal.values()))},
        "maximum_one_step_transient_probability": continuation,
        "maximum_visit_equation_residual": visit_residual,
        "maximum_absorption_flow_residual": flow_residual,
        "normalization_residual": abs(sum(terminal.values()) - 1),
    }


def conflict(left, right):
    return any(left[i] != right[i] for i in left.keys() & right.keys())


def polynomial(vertices, edges, weights):
    return sum(((-1) ** len(subset)) * prod(weights[i] for i in subset)
               for subset in powerset(vertices)
               if not any(frozenset(pair) in edges for pair in combinations(subset, 2)))


def ratio(vertices, edges, weights, neighborhood):
    numerator = polynomial(tuple(v for v in vertices if v not in neighborhood), edges, weights)
    denominator = polynomial(vertices, edges, weights)
    thresholds = tuple(
        polynomial(u, edges, weights)
        / polynomial(tuple(v for v in u if v not in neighborhood), edges, weights)
        for u in powerset(vertices))
    assert all(t > 0 for t in thresholds)
    assert min(thresholds) == denominator / numerator
    return numerator / denominator, {
        "query_neighbors": neighborhood,
        "numerator": numerator, "denominator": denominator,
        "psi": numerator / denominator,
        "all_induced_query_threshold_ratios": thresholds,
        "minimum_query_threshold": min(thresholds),
    }


def serializable(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): serializable(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [serializable(v) for v in value]
    return value


def main():
    if not __debug__:
        raise RuntimeError("Run without -O: exact verification uses assertions.")
    assert all(a == 0 and prime_powers(p) == {p: 1} for a, p in PRIME_EXCLUSIONS)
    assert {p for _, p in PRIME_EXCLUSIONS} == set(HEIGHTS)
    assert (PERIOD, len(SOURCE), len(TRANSIENT), len(ABSORBING)) == (315, 144, 42, 102)
    canonical = CoordinateModel("canonical_digit")
    full_block = CoordinateModel("full_prime_block")
    assignments = {m: canonical.assignment(((a, m),)) for a, m in BAD_APS}
    assert all(tuple(assignments[m]) == canonical.scopes[m] for m in LABELS)
    p = {m: sum(INITIAL for x in SOURCE if m in ACTIVE[x]) for m in LABELS}
    overlaps = {pair: sum(INITIAL for x in SOURCE if all(m in ACTIVE[x] for m in pair))
                for pair in combinations(LABELS, 2)}
    assert tuple(p.values()) == (F(1, 6), F(1, 8), F(1, 12))
    assert tuple(overlaps.values()) == (F(1, 24), F(1, 36), F(1, 48))
    shared = {frozenset(pair) for pair in combinations(LABELS, 2)
              if set(canonical.scopes[pair[0]]) & set(canonical.scopes[pair[1]])}
    assert shared == {frozenset(pair) for pair in combinations(LABELS, 2)
                      if set(full_block.scopes[pair[0]]) & set(full_block.scopes[pair[1]])}
    conflicts = {frozenset(pair) for pair in combinations(LABELS, 2)
                 if conflict(*(assignments[m] for m in pair))}
    assert len(shared) == 3 and not conflicts
    r = dict(p)
    assert len({m for pair in MATCHING for m in pair}) == 2 * len(MATCHING)
    for i, j in MATCHING:
        assert frozenset((i, j)) in shared and overlaps[i, j] > 0
        epsilon = overlaps[i, j] ** 2 / 17
        r[i] -= epsilon
        r[j] -= epsilon
        assert 2 * epsilon <= r[i] * r[j]
    after_deletion = shared - {frozenset(pair) for pair in MATCHING}
    assert conflicts <= after_deletion and all(0 < r[m] <= p[m] < 1 for m in LABELS)
    configurations = (
        ("conflict_original", conflicts, p),
        ("shared_matching_reduced", shared, r),
        ("shared_original", shared, p),
        ("shared_after_matched_edge_deletion_original", after_deletion, p),
    )
    polynomials = {}
    for name, edges, weights in configurations:
        values = [{"vertices": u, "value": polynomial(u, edges, weights)}
                  for u in powerset(LABELS)]
        assert all(row["value"] > 0 for row in values)
        polynomials[name] = values

    can_law, can_visits, can_summary = terminal_law(canonical)
    block_law, block_visits, block_summary = terminal_law(full_block)
    assert can_summary["expected_resamplings"] == F(29, 77)
    assert block_summary["expected_resamplings"] == F(17, 42)
    assert all(block_law[x] == (F(1, 108) if x % 5 == 1 else F(5, 504))
               for x in ABSORBING)
    different = sum(can_law[x] != block_law[x] for x in SOURCE)
    assert different == len(ABSORBING) == 102

    queries = []
    for name, congruences in QUERY_APS:
        fixed = canonical.assignment(congruences)
        neighbors_shared = tuple(m for m in LABELS if fixed.keys() & assignments[m].keys())
        neighbors_conflict = tuple(m for m in LABELS if conflict(fixed, assignments[m]))
        target = tuple(x for x in SOURCE if all(x % m == a for a, m in congruences))
        base = INITIAL * len(target)
        actual_can = sum(can_law[x] for x in target)
        actual_block = sum(block_law[x] for x in target)
        psi_conflict, detail_conflict = ratio(LABELS, conflicts, p, neighbors_conflict)
        psi_reduced, detail_reduced = ratio(LABELS, shared, r, neighbors_shared)
        psi_shared, detail_shared = ratio(LABELS, shared, p, neighbors_shared)
        assert actual_can <= base * psi_conflict < base * psi_reduced < base * psi_shared
        queries.append({
            "name": name, "original_congruences_residue_modulus": congruences,
            "source_probability": base,
            "canonical_digit_output_probability": actual_can,
            "full_prime_block_output_probability": actual_block,
            "conflict_certificate": base * psi_conflict,
            "hls_matching_reduced_certificate": base * psi_reduced,
            "ordinary_shared_certificate": base * psi_shared,
            "conflict_ratio": detail_conflict,
            "hls_matching_reduced_ratio": detail_reduced,
            "ordinary_shared_ratio": detail_shared,
            "matching_reduced_minus_conflict_certificate": base * (psi_reduced - psi_conflict),
        })

    witness_source = full_block.decode((4, 1, 2))
    witness_target = full_block.decode((1, 2, 2))
    assert ACTIVE[witness_source] == (15,) and ACTIVE[witness_target] == (9,)
    block_probability = full_block.transition(witness_source, 15).get(witness_target, F())
    can_probability = canonical.transition(witness_source, 15).get(witness_target, F())
    assert block_probability == F(1, 24) and can_probability == 0
    assert not conflict(assignments[9], assignments[15])
    payload = {
        "scope": "Finite original AP layout, not a whole cover or a new AP exclusion. "
                 "The two algorithms have different terminal laws; no stochastic ordering is asserted.",
        "certificate_scope": "HLS matching-reduced entries are exact graph-polynomial values. "
                             "No general HLS output-law theorem is asserted by this experiment.",
        "source": "Uniform Haar modulo the period, conditioned to avoid the literal prime classes.",
        "period": PERIOD,
        "prime_exclusions_residue_modulus": PRIME_EXCLUSIONS,
        "bad_APs_residue_modulus": BAD_APS,
        "state_count": len(SOURCE), "transient_count": len(TRANSIENT),
        "absorbing_count": len(ABSORBING),
        "canonical_assignments": assignments, "bad_probabilities": p,
        "pair_intersections": {f"{i},{j}": value for (i, j), value in overlaps.items()},
        "shared_variable_edges": sorted(tuple(sorted(edge)) for edge in shared),
        "conflict_edges": sorted(tuple(sorted(edge)) for edge in conflicts),
        "matching": MATCHING, "matching_reduced_weights": r,
        "all_induced_shearer_polynomials": polynomials,
        "canonical_digit": can_summary, "full_prime_block": block_summary,
        "states_with_different_terminal_mass": different,
        "queries": queries,
        "transition_witness": {
            "source_residue": witness_source, "target_residue": witness_target,
            "source_blocks": full_block.encode(witness_source),
            "target_blocks": full_block.encode(witness_target),
            "source_digits": canonical.encode(witness_source),
            "target_digits": canonical.encode(witness_target),
            "source_true_labels": ACTIVE[witness_source],
            "target_true_labels": ACTIVE[witness_target],
            "selected_label": 15,
            "full_prime_block_transition_probability": block_probability,
            "canonical_digit_transition_probability": can_probability,
            "meaning": "Full-block resampling can newly cause the compatible AP 9 from AP 15; "
                       "its causality graph cannot be replaced by the empty canonical conflict graph.",
        },
        "state_data": [{
            "original_residue": x, "blocks": full_block.encode(x), "digits": canonical.encode(x),
            "initial_mass": INITIAL, "true_labels": ACTIVE[x],
            "selected_label": min(ACTIVE[x]) if ACTIVE[x] else None,
            "canonical_digit_terminal_mass": can_law[x],
            "full_prime_block_terminal_mass": block_law[x],
            "canonical_digit_expected_visits": can_visits.get(x, F()),
            "full_prime_block_expected_visits": block_visits.get(x, F()),
        } for x in SOURCE],
    }
    output = Path(__file__).resolve().with_suffix(".json")
    output.write_text(json.dumps(serializable(payload), ensure_ascii=False, separators=(",", ":")) + "\n",
                      encoding="utf-8")
    print(json.dumps(serializable({
        "states": len(SOURCE), "absorbing_states": len(ABSORBING),
        "different_terminal_masses": different,
        "canonical_expected_resamplings": can_summary["expected_resamplings"],
        "full_block_expected_resamplings": block_summary["expected_resamplings"],
        "all_exact_checks_passed": True,
    }), indent=2))


if __name__ == "__main__":
    main()
