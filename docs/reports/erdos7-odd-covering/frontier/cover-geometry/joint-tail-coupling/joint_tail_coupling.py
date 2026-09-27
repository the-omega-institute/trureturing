#!/usr/bin/env python3
"""Exact rational realizability for the two newest divisor labels.

No dependencies; stdout is a verification summary.  This verifies the coupling
criterion and K=2 score reconstruction, not the unresolved rank bound 46/9.
"""

from collections import defaultdict, deque
from fractions import Fraction as F
from itertools import product
import json


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def compositions(total, size):
    if size == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in compositions(total - first, size - 1):
            yield (first,) + tail


def diagnose(alpha, q, v, h):
    """Return [] exactly on the rational realizability polytope.

    Arrays are lists/tuples; scalar entries must have type int or Fraction.
    In particular bool and float are rejected rather than coerced.
    """
    if any(type(array) not in (list, tuple) for array in (q, v, h)):
        return ["arrays must be lists or tuples"]
    if any(type(row) not in (list, tuple) for row in list(v) + list(h)):
        return ["rows must be lists or tuples"]
    n, rows = len(q), len(v)
    if n == 0 or rows == 0 or len(h) != rows:
        return ["empty carrier or row-count mismatch"]
    if any(len(row) != n for row in list(v) + list(h)):
        return ["dimension mismatch"]
    values = [alpha] + list(q) + [x for row in v for x in row]
    values += [x for row in h for x in row]
    if any(type(x) not in (int, F) for x in values):
        return ["mass must have type int or Fraction (bool and float rejected)"]
    if any(x < 0 for x in values):
        return ["negative mass"]
    failures = []
    if sum(q) != alpha or sum(map(sum, v)) != alpha:
        failures.append("marginal total mismatch")
    if any(h[r][y] > v[r][y] for r in range(rows) for y in range(n)):
        failures.append("diagonal exceeds cell marginal")
    hy = [sum(h[r][y] for r in range(rows)) for y in range(n)]
    vy = [sum(v[r][y] for r in range(rows)) for y in range(n)]
    if any(hy[y] > q[y] for y in range(n)):
        failures.append("diagonal exceeds source marginal")
    mass = alpha - sum(hy)
    for y in range(n):
        if q[y] + vy[y] - 2 * hy[y] > mass:
            failures.append("forbidden-fibre Hall cut at " + str(y))
    return failures


def reconstruct(alpha, q, v, h):
    """Return W[u][r][y], with row marginals q, column marginals v,
    and prescribed diagonal W[y][r][y] = h[r][y].
    Uses exact rational Edmonds-Karp flow on the fibre graph.
    """
    problems = diagnose(alpha, q, v, h)
    if problems:
        raise ValueError("; ".join(problems))
    alpha = F(alpha)
    q = [F(x) for x in q]
    v = [[F(x) for x in row] for row in v]
    h = [[F(x) for x in row] for row in h]
    n, rows = len(q), len(v)
    hy = [sum(h[r][y] for r in range(rows)) for y in range(n)]
    a = [q[y] - hy[y] for y in range(n)]
    b = [sum(v[r][y] for r in range(rows)) - hy[y] for y in range(n)]
    mass = alpha - sum(hy)
    result = [[[F(0) for _ in range(n)] for _ in range(rows)] for _ in range(n)]
    for y in range(n):
        for r in range(rows):
            result[y][r][y] = h[r][y]
    if mass == 0:
        check_witness(alpha, q, v, h, result)
        return result

    source, sink = 2 * n, 2 * n + 1
    graph = [dict() for _ in range(2 * n + 2)]

    def edge(u, z, capacity):
        graph[u][z] = capacity
        graph[z][u] = F(0)

    for y in range(n):
        edge(source, y, a[y])
        edge(n + y, sink, b[y])
    for u in range(n):
        for y in range(n):
            if u != y:
                edge(u, n + y, mass)
    sent = F(0)
    while sent < mass:
        parent = {source: None}
        queue = deque([source])
        while queue and sink not in parent:
            u = queue.popleft()
            for z, capacity in graph[u].items():
                if capacity > 0 and z not in parent:
                    parent[z] = u
                    queue.append(z)
        require(sink in parent, "Hall-feasible margins unexpectedly blocked")
        amount, z = mass - sent, sink
        while z != source:
            u = parent[z]
            amount = min(amount, graph[u][z])
            z = u
        z = sink
        while z != source:
            u = parent[z]
            graph[u][z] -= amount
            graph[z][u] += amount
            z = u
        sent += amount
    for u in range(n):
        for y in range(n):
            if u != y and b[y] > 0:
                fibre_flow = mass - graph[u][n + y]
                for r in range(rows):
                    result[u][r][y] = fibre_flow * (v[r][y] - h[r][y]) / b[y]
    check_witness(alpha, q, v, h, result)
    return result


def check_witness(alpha, q, v, h, witness):
    n, rows = len(q), len(v)
    require(all(type(x) is F for layer in witness for row in layer for x in row),
            "witness entry is not Fraction")
    require(all(x >= 0 for layer in witness for row in layer for x in row),
            "negative witness entry")
    require(sum(x for layer in witness for row in layer for x in row) == alpha,
            "witness total mismatch")
    for u in range(n):
        require(sum(map(sum, witness[u])) == q[u], "source marginal mismatch")
    for r in range(rows):
        for y in range(n):
            require(sum(witness[u][r][y] for u in range(n)) == v[r][y],
                    "target marginal mismatch")
            require(witness[y][r][y] == h[r][y], "prescribed diagonal mismatch")


def exhaustive_small():
    """Compare with independent enumeration of all integer joint tables.
    Fractions have denominators 1..3, fibres 1..3, rows 1..2.
    """
    tables, candidates, feasible = 0, 0, 0
    for n, rows, total in product(range(1, 4), range(1, 3), range(1, 4)):
        realized = set()
        for flat in compositions(total, n * rows * n):
            tables += 1
            q = tuple(sum(flat[u * rows * n:(u + 1) * rows * n]) for u in range(n))
            v = tuple(sum(flat[u * rows * n + j] for u in range(n))
                      for j in range(rows * n))
            h = tuple(flat[y * rows * n + r * n + y]
                      for r in range(rows) for y in range(n))
            realized.add((q, v, h))
        for q in compositions(total, n):
            for v in compositions(total, rows * n):
                for h in product(*(range(value + 1) for value in v)):
                    candidates += 1
                    qr = [F(x, total) for x in q]
                    vr = [[F(v[r * n + y], total) for y in range(n)] for r in range(rows)]
                    hr = [[F(h[r * n + y], total) for y in range(n)] for r in range(rows)]
                    passes = not diagnose(F(1), qr, vr, hr)
                    require(passes == ((q, v, h) in realized),
                            "criterion/enumeration mismatch")
                    if passes:
                        feasible += 1
                        reconstruct(F(1), qr, vr, hr)
    return {"integer_joint_tables": tables, "candidate_margin_diagonal_arrays": candidates,
            "feasible_arrays_reconstructed": feasible,
            "fibre_counts": [1, 2, 3], "row_counts": [1, 2], "denominators": [1, 2, 3]}


def degeneracies_and_obstruction():
    zero = [[F(0), F(0)] for _ in range(2)]
    reconstruct(F(0), [F(0), F(0)], zero, zero)
    # One fibre: only the prescribed diagonal can carry any mass.
    reconstruct(F(1), [F(1)], [[F(1, 3)], [F(2, 3)]], [[F(1, 3)], [F(2, 3)]])
    require(bool(diagnose(F(1), [F(1)], [[F(1)]], [[F(0)]])),
            "singleton-fibre residual was accepted")
    q, v, h = [F(1, 2), F(1, 2)], [[F(1, 2), F(1, 2)]], [[F(1, 2), F(0)]]
    for y in range(2):
        require(max(F(0), q[y] + v[0][y] - 1) <= h[0][y] <= min(q[y], v[0][y]),
                "claimed cellwise Frechet premise failed")
    failures = diagnose(F(1), q, v, h)
    require(failures == ["forbidden-fibre Hall cut at 1"], "wrong obstruction")
    return {"zero_total": "reconstructed", "one_fibre_zero_residual": "reconstructed",
            "one_fibre_positive_residual": "rejected",
            "cellwise_frechet_insufficient": failures,
            "violating_cut_lhs": "1", "residual_total": "1/2"}


def input_validation_controls():
    malformed = [
        ("float total", (1.0, [1], [[1]], [[1]])),
        ("boolean source mass", (1, [True], [[1]], [[1]])),
        ("float cell mass", (1, [1], [[1.0]], [[1]])),
        ("boolean coincidence", (1, [1], [[1]], [[True]])),
        ("non-array source", (1, 1, [[1]], [[1]])),
        ("non-array row", (1, [1], [1], [[1]])),
        ("negative mass", (-1, [-1], [[-1]], [[-1]])),
        ("marginal total mismatch", (2, [1], [[1]], [[1]])),
        ("row-count mismatch", (1, [1], [[1]], [])),
        ("fibre-count mismatch", (1, [1], [[1, 0]], [[1]])),
    ]
    for name, arguments in malformed:
        require(bool(diagnose(*arguments)), "invalid input accepted: " + name)
        try:
            reconstruct(*arguments)
        except ValueError:
            pass
        else:
            raise RuntimeError("invalid reconstruction accepted: " + name)

    # Nonzero residual mass, zero-demand fibre, unused off-diagonal edges,
    # and only integer inputs. All output entries, including zero, are exact.
    arguments = (4, [2, 1, 1], [[1, 0, 1], [0, 2, 0]], [[0, 0, 1], [0, 0, 0]])
    witness = reconstruct(*arguments)
    require(all(type(x) is F for layer in witness for row in layer for x in row),
            "integer-only reconstruction leaked a non-Fraction value")
    require(any(x > 0 for u, layer in enumerate(witness)
                for row in layer for y, x in enumerate(row) if u != y),
            "integer-only control had no residual transport")
    return {"malformed_controls_rejected": len(malformed),
            "malformed_controls": [name for name, _ in malformed],
            "integer_only_nonzero_residual": "reconstructed",
            "every_output_entry_is_fraction": True}


def k2_score_reconstruction():
    # Entries are (root phases a5,a7,(row35,column35)), Q49, V245, mass.
    # This is one explicit mixture, not an extremum computation.
    raw = [((1, 2, (3, 4)), 9, (2, 9), 2),
           ((1, 2, (3, 4)), 17, (0, 5), 3),
           ((1, 2, (3, 4)), 5, (4, 17), 5),
           ((1, 2, (3, 4)), 9, (1, 9), 7),
           ((0, 6, (0, 6)), 48, (0, 48), 11),
           ((0, 6, (0, 6)), 3, (2, 48), 13),
           ((0, 6, (0, 6)), 48, (4, 3), 17),
           ((4, 0, (1, 5)), 0, (1, 0), 19),
           ((4, 0, (1, 5)), 1, (3, 1), 23),
           ((2, 3, (2, 3)), 22, (2, 22), 29)]
    total = sum(entry[3] for entry in raw)
    mixture = [(z, u, cell, F(weight, total)) for z, u, cell, weight in raw]
    groups = defaultdict(list)
    for z, u, cell, weight in mixture:
        groups[z].append((u, cell, weight))
    score = [[F(0) for _ in range(49)] for _ in range(5)]
    rebuilt_score = [[F(0) for _ in range(49)] for _ in range(5)]
    reconstructed = []
    support_count = 0
    for z, group in groups.items():
        alpha = sum(weight for _, _, weight in group)
        q = [F(0) for _ in range(49)]
        v = [[F(0) for _ in range(49)] for _ in range(5)]
        h = [[F(0) for _ in range(49)] for _ in range(5)]
        for u, (r, y), weight in group:
            q[u] += weight
            v[r][y] += weight
            if u == y:
                h[r][y] += weight
        joint = reconstruct(alpha, q, v, h)
        for u in range(49):
            for r in range(5):
                for y in range(49):
                    if joint[u][r][y]:
                        reconstructed.append((z, u, (r, y), joint[u][r][y]))
                        support_count += 1
        for r in range(5):
            for y in range(49):
                a5, a7, cell35 = z
                base = 1 + (r == a5) + (y % 7 == a7) + ((r, y % 7) == cell35)
                score[r][y] += alpha * base**2 + (2 * base + 1) * (q[y] + v[r][y]) + 2 * h[r][y]
    for r in range(5):
        for y in range(49):
            def value_at(entries):
                value = F(0)
                for (a5, a7, cell35), u, cell, weight in entries:
                    load = (1 + (r == a5) + (y % 7 == a7)
                            + ((r, y % 7) == cell35) + (y == u) + ((r, y) == cell))
                    value += weight * load**2
                return value
            direct, rebuilt = value_at(mixture), value_at(reconstructed)
            require(score[r][y] == direct == rebuilt, "K=2 score reconstruction mismatch")
            rebuilt_score[r][y] = rebuilt
    return {"input_layouts": len(mixture), "root_groups": len(groups),
            "output_layouts": support_count, "row_cells_checked": 245,
            "includes_row_zero": True, "coefficient_identity": "verified exactly",
            "rank_bound_46_over_9": "not established"}


def main():
    result = {"coupling_criterion": "exact necessary and sufficient conditions",
              "small_exhaustive_check": exhaustive_small(),
              "degeneracies_and_obstruction": degeneracies_and_obstruction(),
              "input_validation": input_validation_controls(),
              "k2_reconstruction": k2_score_reconstruction(),
              "scope": "finite checker plus mathematical proof; no Lean certificate; no new universal rank bound"}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
