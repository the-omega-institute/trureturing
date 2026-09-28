#!/usr/bin/env python3
"""Exact finite certificates for Context Geometry sections 84 and 85.

Python >=3.10, standard library only. Run from any working directory:
  python3 /path/to/verify.py [--output /path/to/results.json]
The program verifies the specified models, not all stationary controllers.
"""
import argparse
from fractions import Fraction as Q
from itertools import product
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("Exact verification requires assertions; remove -O/PYTHONOPTIMIZE.")


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def mul(a, b):
    out = [[0] * len(b[0]) for _ in a]
    for i, row in enumerate(a):
        for k, x in enumerate(row):
            if x:
                for j, y in enumerate(b[k]):
                    if y:
                        out[i][j] += x * y
    return out


def add(*arrays):
    return [[sum(entries) for entries in zip(*rows)] for rows in zip(*arrays)]


def scale(a, c):
    return [[c * x for x in row] for row in a]


def power(a, n):
    r = eye(len(a))
    for _ in range(n):
        r = mul(r, a)
    return r


def columns(vectors):
    return [list(row) for row in zip(*vectors)]


class RowBasis:
    def __init__(self):
        self.rows = {}

    def insert(self, vector):
        v = list(map(Q, vector))
        for p in sorted(self.rows):
            if v[p]:
                c = v[p]
                v = [x - c * y for x, y in zip(v, self.rows[p])]
        p = next((i for i, x in enumerate(v) if x), None)
        if p is None:
            return False
        c = v[p]
        self.rows[p] = [x / c for x in v]
        return True


def rank(a):
    b = RowBasis()
    for row in a:
        b.insert(row)
    return len(b.rows)


def blocks(*arrays):
    sizes = [len(a) for a in arrays]
    n = sum(sizes)
    out = [[0] * n for _ in range(n)]
    offset = 0
    for a in arrays:
        for i, row in enumerate(a):
            out[offset + i][offset:offset + len(a)] = row
        offset += len(a)
    return out


def local_basis(n):
    return [[1] * n] + [[int(j == i) - int(j == n - 1) for j in range(n)]
                        for i in range(n - 1)]


def verify_linear_models():
    dims = (5, 3, 2, 2)
    points = list(product(*(range(n) for n in dims)))
    indices = list(product(*(range(n) for n in dims)))
    bases = [local_basis(n) for n in dims]
    tensors = {s: [product_value(bases[j][s[j]][x[j]] for j in range(4))
                   for x in points] for s in indices}
    fixed = [s for s in indices if s[0] == 0 and sum(i != 0 for i in s) >= 2]
    rest = list(product(range(3), range(2), range(2)))[1:]
    moving = [(a, *s) for s in rest for a in range(1, 5)]
    selected = fixed + moving
    k = columns([tensors[s] for s in selected])
    m = [[int(x[j] == a) for x in points] for j, n in enumerate(dims) for a in range(n)]
    assert rank(m) == 9 and rank(k) == 51
    assert mul(m, k) == [[0] * 51 for _ in m]
    d = [[-1, -1, -1, -1], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0]]
    assert power(d, 5) == eye(4)
    f = add(eye(4), d, power(d, 4))
    assert mul(f, f) == add(f, eye(4))
    assert sum(f[i][i] for i in range(4)) == 2
    ck = blocks(eye(7), *([d] * 11))
    cv = blocks(eye(11), *([d] * 10))
    shifted_k = [k[points.index(((x[0] - 1) % 5, *x[1:]))] for x in points]
    assert shifted_k == mul(k, ck)
    bridge = [[0] * 51 for _ in range(51)]
    for i in range(7):
        bridge[i][i] = 1
    for i in range(40):
        bridge[11 + i][7 + i] = 1
    assert rank(bridge) == 47 and mul(bridge, ck) == mul(cv, bridge)
    cw = blocks(eye(11), *([d] * 11))
    # Explicit surjections from the split coordinates of W = U^11.
    qk = [eye(55)[i] for i in list(range(4, 11)) + list(range(11, 55))]
    qv = eye(55)[:51]
    assert rank(qk) == rank(qv) == 51
    assert mul(qk, cw) == mul(ck, qk)
    assert mul(qv, cw) == mul(cv, qv)
    # Five phase-dependent maps J_r = C_V^r J C_K^(-r), with J = identity.
    maps = [mul(power(cv, r), power(ck, (-r) % 5)) for r in range(5)]
    for r in range(5):
        inverse = mul(power(ck, r), power(cv, (-r) % 5))
        assert mul(inverse, maps[r]) == eye(51)
        assert mul(maps[(r + 1) % 5], ck) == mul(cv, maps[r])
    # A signed perturbation invisible to all one-register marginals.
    v = tensors[(1, 1, 0, 0)]
    filtered = [value if x[0] == 0 else 0 for x, value in zip(points, v)]
    assert mul(m, columns([v])) == [[0] for _ in m]
    after = [row[0] for row in mul(m, columns([filtered]))]
    assert any(after)
    # Actual probability pair, with identical single-register marginals.
    p_plus = [Q(1, 60) + Q(x, 120) for x in v]
    p_minus = [Q(1, 60) - Q(x, 120) for x in v]
    assert min(p_plus + p_minus) > 0 and sum(p_plus) == sum(p_minus) == 1
    assert mul(m, columns([p_plus])) == mul(m, columns([p_minus]))
    conditional = []
    for distribution in (p_plus, p_minus):
        branch = sum(p for x, p in zip(points, distribution) if x[0] == 0)
        conditional.append([sum(p for x, p in zip(points, distribution)
                                if x[0] == 0 and x[1] == b) / branch for b in range(3)])
    assert conditional == [[Q(1, 2), Q(1, 3), Q(1, 6)],
                           [Q(1, 6), Q(1, 3), Q(1, 2)]]
    # Nonzero elementary matrices: E_i C^(i-j) E_j generate M_5.
    c = [[int(i == (j + 1) % 5) for j in range(5)] for i in range(5)]
    for i, j in product(range(5), repeat=2):
        ei = [[int(a == b == i) for b in range(5)] for a in range(5)]
        ej = [[int(a == b == j) for b in range(5)] for a in range(5)]
        expected = [[int(a == i and b == j) for b in range(5)] for a in range(5)]
        assert mul(mul(ei, power(c, (i - j) % 5)), ej) == expected
    return {"marginal_rank": 9, "kernel_dimension": 51,
            "K_fixed_moving": [7, 44], "V_fixed_moving": [11, 40],
            "equivariant_bridge_rank": 47, "common_cover_dimension": 55,
            "phase_reference_branches": 5, "joint_linear_dimension": 255,
            "filter_witness_marginals": after, "matrix_units_checked": 25,
            "conditional_B_given_A_zero": [[str(x) for x in row] for row in conditional]}


def product_value(values):
    result = 1
    for value in values:
        result *= value
    return result


def verify_controller():
    states = [("S", 0)] + [(kind, b) for kind in ("F", "G", "WF", "WG1", "WG2")
                          for b in range(5)] + [("H", x) for x in range(25)]

    def rotate(q):
        kind, b = q
        return q if kind == "S" else (kind, (b + (5 if kind == "H" else 1)) %
                                      (25 if kind == "H" else 5))

    def step(q, digit, symmetric=True):
        kind, b = q
        if kind == "S":
            return "WG2", digit
        if kind in ("WF", "WG1", "WG2"):
            return {"WF": "F", "WG1": "G", "WG2": "WG1"}[kind], b
        if kind == "H":
            return q
        offset = (digit - b) % 5
        if kind == "G":
            return [("WF", b), ("WG2", (b + 2) % 5),
                    ("H", 5 * ((b + 1) % 5) + 3),
                    ("H", 5 * ((b + 1) % 5) + 4), ("WG2", (b + 2) % 5)][offset]
        return [("WF", (b - 2) % 5), ("H", 5 * b + 2),
                ("H", 5 * ((b + 2) % 5)), ("H", 5 * ((b + 2) % 5) + 1),
                ("H", 5 * b if symmetric else 0)][offset]

    def run(x, symmetric):
        q, phase, reads, waits, trace = ("S", 0), x, 0, 0, []
        for _ in range(30):
            trace.append((q, phase))
            if q[0] == "H":
                assert q[1] == x
                return trace, reads, waits
            if q[0].startswith("W"):
                phase = (phase + 1) % 25
                waits += 1
                q = step(q, 0, symmetric)
            else:
                reads += 1
                q = step(q, phase // 5, symmetric)
        raise AssertionError("execution did not terminate")

    runs = [run(x, True) for x in range(25)]
    assert all(runs[x] == run(x, False) for x in range(25))
    assert {q for trace, _, _ in runs for q, _ in trace} == set(states)
    assert max(r for _, r, _ in runs) == 4 and max(w for _, _, w in runs) == 6
    for q, digit in product(states, range(5)):
        assert step(rotate(q), (digit + 1) % 5) == rotate(step(q, digit))
    # Formal response experiment: read symbols and unit waits are typed partial
    # transitions; a word of the wrong type has zero response. Halt output is fixed.
    index = {q: i for i, q in enumerate(states)}
    ops = []
    for a in range(6):
        op = []
        for q in states:
            enabled = q[0].startswith("W") if a == 5 else q[0] in ("S", "F", "G")
            op.append(index[step(q, a % 5)] if enabled else None)
        ops.append(op)
    basis = RowBasis()
    queue = []
    for x in range(25):
        row = [int(q == ("H", x)) for q in states]
        inserted = basis.insert(row)
        assert inserted
        queue.append((row, "", x))
    head = 0
    while head < len(queue):
        row, word, output = queue[head]
        head += 1
        for a, op in enumerate(ops):
            previous = [row[j] if j is not None else 0 for j in op]
            if basis.insert(previous):
                queue.append((previous, ("W" if a == 5 else str(a)) + word, output))
    assert len(basis.rows) == 51
    return {"states": len(states), "physical_inputs": 25, "all_states_reachable": True,
            "max_reads": 4, "max_unit_waits": 6, "physical_runs_unchanged": True,
            "state_digit_covariance_checks": 255, "typed_response_rank": 51,
            "response_witnesses": [{"word": w, "halt": h} for _, w, h in queue]}


def verify_generalizations():
    families = []
    # Last family shows that the smallest common cover need not itself be regular.
    for n, rest, fixed_states in ((3, (2, 2), 1), (4, (2, 2, 2), 1),
                                  (5, (3, 2, 2), 1), (7, (3, 3, 3), 1),
                                  (3, (3, 2), 3)):
        dims = (n, *rest)
        points = list(product(*(range(d) for d in dims)))
        m = [[int(x[j] == a) for x in points]
             for j, d in enumerate(dims) for a in range(d)]
        size_y = product_value(rest)
        local = sum(d - 1 for d in rest)
        hidden = size_y - 1 - local
        dimension = len(points) - rank(m)
        assert dimension == n * (size_y - 1) - local
        cycles, remainder = divmod(dimension - fixed_states, n)
        assert remainder == 0 and cycles >= 0
        defect = size_y - 1 - cycles
        assert n * defect == fixed_states + local
        common_rank = min(hidden, fixed_states + cycles) + (n - 1) * min(size_y - 1, cycles)
        common_cover = max(hidden, fixed_states + cycles) + (n - 1) * max(size_y - 1, cycles)
        assert common_rank + common_cover == 2 * dimension
        families.append({"cycle_order": n, "other_register_sizes": list(rest),
                         "response_fixed_states": fixed_states, "response_free_cycles": cycles,
                         "dimension": dimension, "common_rank": common_rank,
                         "common_cover": common_cover, "natural_W_dimension": n * (size_y - 1)})
    # C4: a two-label parity reference suffices for X=1+sign, Y=1+1.
    chi_x = [2, 0, 2, 0]
    chi_y = [2, 2, 2, 2]
    assert [a * a for a in chi_x] == [a * b for a, b in zip(chi_x, chi_y)]
    # Nonabelian check: G=S3, X=regular, Y=trivial^6.
    from itertools import permutations
    group = list(permutations(range(3)))
    def compose(g, h):
        return tuple(g[h[i]] for i in range(3))
    def inverse(g):
        return tuple(g.index(i) for i in range(3))
    def regular(g):
        return [[int(a == compose(g, b)) for b in group] for a in group]
    for g, r in product(group, repeat=2):
        # Branch map J_r=C_X(r^-1), because Y has trivial action.
        assert mul(regular(inverse(compose(g, r))), regular(g)) == regular(inverse(r))
    for g in group:
        assert mul(regular(g), regular(inverse(g))) == eye(6)
    return {"product_families": families, "C4_parity_reference_dimension": 2,
            "S3_reference_labels": 6, "S3_covariance_pairs": 36,
            "scope": "Response orbit models are not synthesized optimal physical controllers."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = {"arithmetic": "exact integers and fractions", "linear": verify_linear_models(),
              "controller": verify_controller(),
              "generalizations": verify_generalizations(),
              "scope": "Specified finite models only; no universal controller search or Lean claim."}
    data = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(data, encoding="utf-8")
    else:
        print(data, end="")


if __name__ == "__main__":
    main()
