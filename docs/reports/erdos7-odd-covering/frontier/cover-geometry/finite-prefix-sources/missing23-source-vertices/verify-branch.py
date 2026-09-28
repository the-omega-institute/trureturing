"""Exact finite checks for the two-leaf-head exchange; no full source geometry.

The all-depth claim follows from the companion head-placement proof. This
checks exhaustive local head positions with signed backgrounds, zero weights,
and asymmetric branch fields, plus the actual source and physical-index maps.
Only explicit adjacent project files are read; results are written to stdout.
"""
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import json


def need(ok, message):
    if not ok:
        raise ValueError(message)


LEAVES = (4, 13, 22, 7, 16, 25)
OLD = (0, 7, 28, 28, 28, 28)
NEW = (0, 28, 28, 7, 28, 28)
SWAPPED = OLD[3:] + OLD[:3]
MIXED = tuple((4 * a + 3 * b) // 7 for a, b in zip(OLD, SWAPPED))
LAYOUTS = tuple(product(range(-1, 6), ((-1, -1),) + tuple(product(range(6), range(4)))))


def direct(weights, background, field, c27, c135):
    return max(sum(weights[l] * field[l // 3][j]
                   * max(0, background[l // 3][j] + c27 * (l == h27)
                         + c135 * (l == h135 and j == col))
                   for l, j in product(range(6), range(4)))
               for h27, (h135, col) in LAYOUTS)


def summarized(weights, background, field, c27, c135):
    mass = tuple(sum(weights[3 * b:3 * b + 3]) for b in range(2))
    peak = tuple(max(weights[3 * b:3 * b + 3]) for b in range(2))
    baseline = sum(mass[b] * field[b][j] * max(0, background[b][j])
                   for b, j in product(range(2), range(4)))
    increments = []
    for b27, (b135, col) in product(range(-1, 2), ((-1, -1),) + tuple(product(range(2), range(4)))):
        value = sum(peak[b] * field[b][j]
                    * (max(0, background[b][j] + c27 * (b == b27)
                           + c135 * (b == b135 and j == col))
                       - max(0, background[b][j]))
                    for b, j in product(range(2), range(4)))
        increments.append(value)
    return baseline + max(increments)


def verify(root):
    tube_path = root / "tube.json"
    raw = tube_path.read_bytes()
    need(sha256(raw).hexdigest() == "10cc4fb16f5c4db94fbdb227c9a6a524ca7bc34e52ba3881d6f9dcfda30a0b64",
         "pinned all-physical-domain margin")
    tube = json.loads(raw)
    delta = F(tube["uniform_certified_margin_lower"])
    need(delta == F(116, 15625), "safe common certified margin")
    need(all(7 * v == 4 * a + 3 * b for v, a, b in zip(MIXED, OLD, SWAPPED)),
         "exact synthetic mixture in units 1/42")
    summaries = lambda w: tuple((sum(w[i:i + 3]), max(w[i:i + 3])) for i in (0, 3))
    need(summaries(NEW) == summaries(MIXED) == ((56, 28), (63, 28)),
         "new and synthetic branch mass/peak equality")
    need(MIXED[0] > 0 and OLD[0] == NEW[0] == 0,
         "synthetic vector is not an actual fixed-carrier source")

    backgrounds = (
        ((-16, -8, -2, 0), (-16, -8, -2, 0)),
        ((1, -9, 0, 7), (-4, 2, -5, 1)),
        ((0, 0, 0, 0), (4, -3, 8, -12)),
        ((-13, -7, -1, 5), (9, 0, -11, 2)),
    )
    fields = (
        ((1, 1, 1, 1), (1, 1, 1, 1)),
        ((0, 3, 2, 0), (1, 0, 4, 5)),
        ((11, 9, 6, 3), (3, 6, 9, 11)),
        ((0, 0, 0, 0), (1, 2, 3, 4)),
    )
    coefficients = ((0, 0), (0, 7), (7, 0), (1, 1), (7, 7), (14, 35))
    cases = 0
    minimum_gap = None
    digest = sha256()
    for bg, field, (c27, c135) in product(backgrounds, fields, coefficients):
        values = tuple(direct(w, bg, field, c27, c135) for w in (OLD, SWAPPED, NEW, MIXED))
        need(all(value == summarized(w, bg, field, c27, c135)
                 for w, value in zip((OLD, SWAPPED, NEW, MIXED), values)),
             "full local enumeration agrees with branch mass/peak formula")
        a, s, b, v = values
        need(b == v and 7 * b <= 4 * a + 3 * s, "convex branch exchange")
        need(s == direct(OLD, bg[::-1], field[::-1], c27, c135),
             "synthetic branch-swap equivariance")
        gap = 4 * a + 3 * s - 7 * b
        minimum_gap = gap if minimum_gap is None else min(minimum_gap, gap)
        digest.update(json.dumps((bg, field, c27, c135, values), separators=(",", ":")).encode())
        cases += 1

    crt = {(x % 27, x % 5): x for x in range(135)}
    s27 = tuple(x + 3 if x % 9 == 4 else x - 3 if x % 9 == 7 else x for x in range(27))
    s135 = tuple(crt[s27[x % 27], x % 5] for x in range(135))
    need(sorted(s135) == list(range(135)), "full-carrier bijection")
    for modulus in (3, 9, 27, 5, 15, 45, 135):
        images = [{s135[x] % modulus for x in range(135) if x % modulus == r}
                  for r in range(modulus)]
        need(all(len(s) == 1 for s in images) and len({next(iter(s)) for s in images}) == modulus,
             "unknown head cylinder type preserved")
    carrier = tuple(x for x in range(135) if x % 3 and x % 9 != 1 and x % 27 != 4
                    and x % 5 and x % 15 != 2 and x % 45 != 8)
    need({s135[x] for x in carrier} != set(carrier), "swap does not preserve native carrier")
    domain = tuple(product((1, 2), range(1, 5), (2, 4, 5, 7, 8), (1, 4, 7, 8, 11, 13, 14)))
    fixed = []
    physical_checks = 0
    for xi in domain:
        target = xi[:2] + (7 if xi[2] == 4 else 4 if xi[2] == 7 else xi[2],) + xi[3:]
        for x in range(135):
            need(all((x % m == a) == (s135[x] % m == b)
                     for m, a, b in zip((3, 5, 9, 15), xi, target)),
                 "all selected-head incidences transport together")
            physical_checks += 1
        if xi == target:
            fixed.append(xi)
    need(len(fixed) == 168 and all(xi[2] in (2, 5, 8) for xi in fixed), "fixed physical subdomain")

    face = (7, 13, 16, 22, 25)
    face_checks = 0
    for lam in ((F(1, 5),) * 5, (F(1, 15), F(2, 15), F(3, 15), F(4, 15), F(5, 15))):
        for positive3, positive5, x in product((False, True), (False, True), carrier):
            col = F(1) if positive5 else F(4, 5) - F(x % 5 == 1, 4) - F(x % 3 == 2 and x % 5 == 1, 5)
            term = lambda h: col * (1 if positive3 else F(2, 3) - F(x % 27 == h, 2))
            z = dict(zip(face, (p / 2 for p in lam)))
            actual = col * (1 if positive3 else F(2, 3) - z.get(x % 27, 0))
            need(actual == sum(p * term(h) for h, p in zip(face, lam)), "joint face interpolation")
            face_checks += 1
    return {
        "scope": "Fixed source chart and t1=1/20,e=0. Structural local enumeration, not full current/query geometry or new Lean verification.",
        "pinned_tube_sha256": sha256(raw).hexdigest(),
        "source_leaf_order": LEAVES, "weight_unit": "1/42",
        "old": OLD, "new": NEW, "synthetic_mixture": MIXED,
        "local_parameter_cases": cases, "local_head_layouts_per_case": len(LAYOUTS),
        "local_result_sha256": digest.hexdigest(), "minimum_scaled_exchange_gap": minimum_gap,
        "physical_labels": len(domain), "physical_incidence_checks": physical_checks,
        "fixed_physical_labels": len(fixed), "certified_physical_tuples": len(fixed) ** 6,
        "fraction_of_full_physical_domain": str(F(len(fixed), len(domain)) ** 6),
        "certified_pure3_face_support": face, "face_sample_cell_checks": face_checks,
        "uniform_margin_lower": str(delta),
        "remaining_boundary": "Tuples containing physical9 projection4 or7 are not certified at new source vertices. The general result requires the head-placement and positive-component proof in the companion report, including all complete tails.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--package", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    print(json.dumps(verify(args.package), sort_keys=True, indent=2))
