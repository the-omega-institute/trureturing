"""Finite source-budget transport and interpolation checks; no geometry or directory traversal."""
from fractions import Fraction as F
from itertools import product
from hashlib import sha256
from pathlib import Path
import json


def need(ok, message):
    if not ok:
        raise ValueError(message)


ROWS = (2, 5, 7, 8, 11, 13, 14, 16, 17, 20, 22, 23, 25, 26)
MODS = (3, 9, 27, 5, 15, 45, 135)
XI = tuple(product((1, 2), (1, 2, 3, 4), (2, 4, 5, 7, 8), (1, 4, 7, 8, 11, 13, 14)))
REGIONS = tuple(product((False, True), repeat=2))
QUINARY = ((1, 0), (2, 0), (3, 0), (4, 0), (1, 1))
C = tuple(x for x in range(135) if x % 3 and x % 9 != 1 and x % 27 != 4
          and x % 5 and x % 15 != 2 and x % 45 != 8)
CRT = {(x % 27, x % 5): x for x in range(135)}


def reserve(z, t, e):
    ga = sum(z[h] for h in ROWS if h % 3 == 2)
    gr = sum(z[h] for h in ROWS if h % 9 == 8)
    de = {h: F(h == 1, 5) + t[h] for h in range(1, 5)}
    beff = sum(1 - z[x % 27] for x in C if x % 3 == 2 and x % 5 == 1)
    return F(135, 4) + ga + (9 - ga) * de[2] + gr + (3 - gr) * de[3] + F(9, 5) - beff * (F(1, 5) - e)


def parameters(h, j, i):
    return ({r: F(r == h, 2) for r in ROWS},
            {r: F(r == j, 20) for r in range(1, 5)}, F(i, 20))


def weight(z, t, e, region, x):
    a = F(1) if region[0] else F(2, 3) - z[x % 27]
    b = F(1) if region[1] else F(4, 5) - F(x % 5 == 1, 5) - t[x % 5] - (F(1, 5) - e) * (x % 3 == 2 and x % 5 == 1)
    return a * b


def projection_count(x, xi):
    return sum(x % m == r for m, r in zip((3, 5, 9, 15), xi))


generators = []
for a, b in ((13, 22), (7, 16), (16, 25), (2, 11), (11, 20), (5, 14), (14, 23), (8, 17), (17, 26)):
    generators.append((f"leaf_{a}_{b}", tuple(b if x == a else a if x == b else x for x in range(27))))
generators.append(("branch_2_5", tuple(x + 3 if x % 9 == 2 else x - 3 if x % 9 == 5 else x for x in range(27))))

checks = {"finite_prefix_maps": 0, "partition_checks": 0, "vertex_reserve_checks": 0,
          "vertex_cell_weight_checks": 0, "physical_projection_cell_checks": 0}
need(len(C) == 44 and len(XI) == 280, "declared fixed carrier and physical domain")
for name, m3 in generators:
    need(sorted(m3) == list(range(27)), name + ": ternary bijection")
    need(all(m3[x] % m == m3[x % m] % m for m in (1, 3, 9, 27) for x in range(27)), name + ": prefix compatibility")
    m135 = tuple(CRT[m3[x % 27], x % 5] for x in range(135))
    need({m135[x] for x in C} == set(C), name + ": same common carrier")
    need(all(m135[x] % 15 == x % 15 for x in range(135)), name + ": fixed mod15")
    for modulus in MODS:
        images = [{m135[x] % modulus for x in range(135) if x % modulus == a} for a in range(modulus)]
        need(all(len(s) == 1 for s in images) and len({next(iter(s)) for s in images}) == modulus, name + ": cylinder transport")
        checks["partition_checks"] += 1
    for h, (j, i) in product(ROWS, QUINARY):
        old, new = parameters(h, j, i), parameters(m3[h], j, i)
        need(reserve(*old) == reserve(*new), name + ": reserve transport")
        checks["vertex_reserve_checks"] += 1
        for reg, x in product(REGIONS, C):
            need(weight(*old, reg, x) == weight(*new, reg, m135[x]), name + ": weight transport")
            checks["vertex_cell_weight_checks"] += 1
    transported = set()
    for xi in XI:
        target = (xi[0], xi[1], m3[xi[2]] % 9, xi[3])
        transported.add(target)
        for x in C:
            need(projection_count(x, xi) == projection_count(m135[x], target), name + ": labelled projection transport")
            checks["physical_projection_cell_checks"] += 1
    need(transported == set(XI), name + ": full physical domain preserved")
    checks["finite_prefix_maps"] += 1

orbits, unseen = [], set(ROWS)
while unseen:
    orbit, todo = set(), [min(unseen)]
    while todo:
        r = todo.pop()
        if r in orbit:
            continue
        orbit.add(r)
        todo.extend(m[r] for _, m in generators)
    unseen -= orbit
    orbits.append(sorted(orbit))
need(orbits == [[2, 5, 11, 14, 20, 23], [7, 16, 25], [8, 17, 26], [13, 22]], "four verified row orbits")

# Verify one interior point's complete 14-by-5 product decomposition exactly.
z = {h: F(n, 210) for n, h in enumerate(ROWS, 1)}
t, e = {h: F(h, 200) for h in range(1, 5)}, F(1, 400)
need(sum(z.values()) == F(1, 2) and sum(t.values()) == F(1, 20) and 0 <= e <= t[1], "interior budget")
vertices = [(h, j, i) for h, (j, i) in product(ROWS, QUINARY)]
lambdas = {(h, j, i): 40 * z[h] * (e if i else t[j] - e * (j == 1)) for h, j, i in vertices}
need(all(v >= 0 for v in lambdas.values()) and sum(lambdas.values()) == 1, "joint coefficient simplex")
need(reserve(z, t, e) == sum(lambdas[v] * reserve(*parameters(*v)) for v in vertices), "joint reserve decomposition")
for reg, x in product(REGIONS, C):
    need(weight(z, t, e, reg, x) == sum(lambdas[v] * weight(*parameters(*v), reg, x) for v in vertices), "joint region decomposition")

# The newly transferable edge changes only the pure-3 budget.
edge_samples = []
for lam in (F(0), F(1, 7), F(1, 2), F(4, 5), F(1)):
    ze = {h: (lam / 2 if h == 13 else (1 - lam) / 2 if h == 22 else F(0)) for h in ROWS}
    te = {h: F(h == 1, 20) for h in range(1, 5)}
    need(reserve(ze, te, F(0)) == F(135, 4), "edge reserve constant")
    for reg, x in product(REGIONS, C):
        need(weight(ze, te, F(0), reg, x) == lam * weight(*parameters(13, 1, 0), reg, x)
             + (1 - lam) * weight(*parameters(22, 1, 0), reg, x), "edge weight identity")
    edge_samples.append(str(lam))

# Counterexamples are exact; their ordinary general derivations live in the note.
counterexamples = {
    "one_vertex_good_extension": {"R": "1", "H": "0", "S(theta)": "0"},
    "one_vertex_bad_extension": {"R": "1", "H": "0", "S(theta)": "2*theta", "midpoint_D": "0"},
    "switch_actual_models": {"R": "1", "H": "0", "S1(theta)": "2*theta", "S2(theta)": "2*(1-theta)", "midpoint_min_S": "1"},
    "separate_affinity": {"W(u,v)": "u*v", "W(0,1)": "0", "W(1,0)": "0", "W(1/2,1/2)": "1/4"},
    "ratio_not_convex": {"D0": "3", "H0": "2", "D1": "1", "H1": "0", "midpoint_ratio": "1/2", "average_vertex_ratio": "1/3"},
}
need(F(1, 2) > (F(2, 3) + 0) / 2, "ratio counterexample")

source = Path(__file__).resolve().parent.parent / "missing23-eta14" / "source_model.py"
source_sha = sha256(source.read_bytes()).hexdigest()
need(source_sha == "e3296d181686c0f1925e755583fdc4df2ffeb2bacbc36a77a2396bbe3b4a9135", "pinned source-model identity")
result = {
    "scope": "Finite prefix and parameter algebra, no geometry, no new current/query estimate, no Lean verification.",
    "fixed_chart": {"a": 2, "b": 4, "c": 1, "r": 8, "d": 2, "k": 1},
    "common_carrier": list(C), "carrier_size": len(C), "physical_labels_per_stage": len(XI),
    "pinned_source_model_sha256": source_sha,
    "source_paper_sha256": '73f78621a297650176cb796f763b9279eae9533efedbbb58405efc885ef41bb9',
    "checks": checks, "row_orbits_under_verified_generators": orbits,
    "joint_vertices_before_transport": len(vertices), "representatives_under_verified_group": len(orbits) * len(QUINARY),
    "representative_reserves": [{"row_orbit": orb, "j": j, "i": i, "reserve": str(reserve(*parameters(orb[0], j, i)))} for orb, (j, i) in product(orbits, QUINARY)],
    "interior_point_joint_interpolation": {"vertex_coefficients": len(lambdas), "region_cell_checks": len(REGIONS) * len(C), "reserve": str(reserve(z, t, e))},
    "edge_samples": edge_samples, "edge_reserve": "135/4",
    "newly_transferred_certificate": "z=22 and z13+z22=1/2, all other z=0, t=(1/20)e1, overlap e=0; conditional on the all-280^6 z13 common-G16 certificate and its fixed-law domination hypotheses",
    "counterexamples": counterexamples,
    "boundary": "The twenty representatives are obligations under this verified symmetry reduction, not twenty proved logically independent or necessary numerical computations. General parameter/interpolation and arbitrary-height transport are proved in the companion note.",
}
print(json.dumps(result, sort_keys=True, indent=2))
