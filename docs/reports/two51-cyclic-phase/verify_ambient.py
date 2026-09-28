#!/usr/bin/env python3
"""Exact certificates for Context Geometry section 86.

Python >=3.10, standard library only; companion verify.py must be beside this
file. Run from any cwd with optional --output PATH. Split-coordinate Euclidean
orthogonality is not physical-coordinate positivity or an execution protocol.
"""
import argparse
from fractions import Fraction as Q
import importlib.util
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("Exact verification requires assertions; remove -O/PYTHONOPTIMIZE.")


# Resolve the companion by location for both CLI execution and file-based import.
_spec = importlib.util.spec_from_file_location(
    "two51_cyclic_certificate", Path(__file__).with_name("verify.py"))
if _spec is None or _spec.loader is None:
    raise ImportError("Cannot load the companion exact linear algebra certificate.")
_helpers = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_helpers)
add, blocks, columns, eye, local_basis, mul, power, rank, scale = (
    getattr(_helpers, name) for name in
    ("add", "blocks", "columns", "eye", "local_basis", "mul", "power", "rank", "scale"))


def transpose(a):
    return [list(row) for row in zip(*a)]


def difference(a, b):
    return add(a, scale(b, -1))


def turn(c, s, d=None, phase=0):
    """R(c,s) in S,A,B coordinates; phase conjugates the A component."""
    a = [[0] * 55 for _ in range(55)]
    for i in range(47):
        a[i][i] = 1
    pos = eye(4) if d is None else power(d, phase % 5)
    neg = eye(4) if d is None else power(d, (-phase) % 5)
    for i in range(4):
        a[47+i][47+i] = c
        a[51+i][51+i] = c
        for j in range(4):
            a[47+i][51+j] = -s * pos[i][j]
            a[51+i][47+j] = s * neg[i][j]
    return a


def verify_ambient():
    d = [[-1, -1, -1, -1], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0]]
    cs = blocks(eye(7), *([d] * 10))
    cw, ck, cv = blocks(cs, d, eye(4)), blocks(cs, d), blocks(cs, eye(4))
    qk = eye(55)[:51]
    qv = eye(55)[:47] + eye(55)[51:]
    nk, nv = transpose(eye(55)[51:]), transpose(eye(55)[47:51])
    t = turn(0, 1)
    assert mul(t, turn(0, -1)) == eye(55)
    assert power(t, 4) == eye(55) and rank(t) == 55
    assert mul(transpose(t), t) == eye(55)
    assert mul(qv, t) == qk and mul(qk, power(t, 3)) == qv
    assert mul(t, nk) == scale(nv, -1)
    assert mul(qk, cw) == mul(ck, qk)
    assert mul(qv, cw) == mul(cv, qv)
    assert rank(difference(ck, cv)) == 4
    assert rank(difference(mul(t, cw), mul(cw, t))) == 8
    rotations = []
    for c, s in [(Q(1), Q(0)), (Q(3, 5), Q(4, 5)),
                 (Q(0), Q(1)), (Q(-1), Q(0)), (Q(0), Q(-1))]:
        r = turn(c, s)
        assert c*c + s*s == 1
        assert mul(r, turn(c, -s)) == eye(55)
        lift_rank = rank(mul(mul(qv, r), nk))
        assert lift_rank == (0 if c == 0 else 4)
        rotations.append({"cos": str(c), "sin": str(s), "lift_dependence_rank": lift_rank})
    for r in range(5):
        tr, tr1 = turn(0, 1, d, r), turn(0, 1, d, r+1)
        fr = blocks(eye(47), power(d, (-r) % 5))
        fr1 = blocks(eye(47), power(d, (-r-1) % 5))
        assert mul(tr, turn(0, -1, d, r)) == eye(55)
        assert mul(qv, tr) == mul(fr, qk)
        assert mul(tr1, cw) == mul(cw, tr)
        assert mul(fr1, ck) == mul(cv, fr)
    return {"ambient_dimension": 55, "quotient_dimension": rank(qk),
            "turn_order": 4, "turn_rank": rank(t),
            "fixed_C5_commutator_rank": 8, "quotient_action_difference_rank": 4,
            "phase_covariance_cases": 5, "rational_rotation_cases": rotations}


def verify_operation_algebra():
    # Natural U tensor B_rest coordinates: U-position major, rest index minor.
    # Rest indices 0..3 span L (single-register differences); 4..10 span H.
    ub = local_basis(5)
    def tensor(u, j):
        return [u[a] * int(k == j) for a in range(5) for k in range(11)]
    split_vectors = ([tensor(ub[0], j) for j in range(4, 11)]
                     + [tensor(ub[i], j) for j in range(10) for i in range(1, 5)]
                     + [tensor(ub[i], 10) for i in range(1, 5)]
                     + [tensor(ub[0], j) for j in range(4)])
    p = columns(split_vectors)
    assert rank(p) == 55
    d = [[-1, -1, -1, -1], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0]]
    cw = blocks(eye(7), *([d] * 11), eye(4))
    # Physical cyclic shift agrees with the split C5 action exactly.
    shifted = [p[((a-1) % 5)*11+j] for a in range(5) for j in range(11)]
    assert shifted == mul(p, cw)
    nk = [tensor(ub[0], j) for j in range(4)]
    nv = [tensor(ub[i], 10) for i in range(1, 5)]
    assert rank(nk) == rank(nv) == 4
    assert columns(nk) == mul(p, transpose(eye(55)[51:]))
    assert columns(nv) == mul(p, transpose(eye(55)[47:51]))
    def unit_image(v, i, j):
        return [v[j*11+k] if a == i else 0 for a in range(5) for k in range(11)]
    def generated(vectors):
        return [unit_image(v, i, j) for v in vectors for i in range(5) for j in range(5)]
    ranks = [rank(generated(n)) for n in (nk, nv)]
    assert ranks == [20, 5]
    return {"physical_basis_rank": 55, "kernel_dimensions": [4, 4],
            "matrix_units": 25, "generated_dimensions": ranks,
            "scope": "Specified kernels and full position algebra M5(R) tensor I11."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = {"arithmetic": "exact integers and fractions", "ambient": verify_ambient(),
              "operation_algebra": verify_operation_algebra(),
              "scope": "Linear constructions only; no positivity, execution-cost, or full controller equivalence claim."}
    data = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(data, encoding="utf-8")
    else:
        print(data, end="")


if __name__ == "__main__":
    main()
