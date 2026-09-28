"""Exact source-weight and tail checks around the certified five-leaf face.

Only explicit adjacent inputs are read. No directory scan, full geometry,
or Lean verification is performed; output is deterministic JSON on stdout.
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


ROWS = (2, 5, 7, 8, 11, 13, 14, 16, 17, 20, 22, 23, 25, 26)
FACE = (7, 13, 16, 22, 25)
REGIONS = tuple(product((False, True), repeat=2))
C = tuple(x for x in range(135) if x % 3 and x % 9 != 1 and x % 27 != 4
          and x % 5 and x % 15 != 2 and x % 45 != 8)
T0 = {j: F(j == 1, 20) for j in range(1, 5)}
R0 = F(135, 4)


def weight(z, t, e, region, x):
    a = 1 if region[0] else F(2, 3) - z[x % 27]
    b = 1 if region[1] else F(4, 5) - F(x % 5 == 1, 5) - t[x % 5] - (F(1, 5) - e) * (x % 3 == 2 and x % 5 == 1)
    return a * b


def verify(root):
    raw = (root / "branch.json").read_bytes()
    pin = "963b1f1e95b6c8af3d444c382bec6b3ec61ec41bbc035868a7a1b3a06316a209"
    need(sha256(raw).hexdigest() == pin, "pinned five-leaf source-face certificate")
    branch = json.loads(raw)
    need(tuple(branch["certified_pure3_face_support"]) == FACE
         and branch["fixed_physical_labels"] == 168, "restricted domain")
    delta = F(branch["uniform_margin_lower"])
    g0 = 14 * R0 - delta
    radius = F(1, 18000)
    tube_rho = (1 + F(3, 17) * radius) * (1 + radius / 11)
    tube_slack = 14 * R0 - tube_rho * g0
    need(tube_slack == F(255839334607, 631125000000000) and tube_slack > 0,
         "strict raw-coordinate tube margin")

    face_points = [
        {h: F(h == 13, 2) for h in ROWS},
        {h: F(h == 7, 2) for h in ROWS},
        {h: F(FACE.index(h) + 1, 30) if h in FACE else F(0) for h in ROWS},
    ]
    cases = checks = 0
    for edge, tau, h, (j, overlap) in product(face_points, (F(0), radius, F(1, 2), F(1)),
                                             ROWS, ((1, 0), (2, 0), (3, 0), (4, 0), (1, 1))):
        z = {r: (1 - tau) * edge[r] + tau * F(r == h, 2) for r in ROWS}
        t = {r: (1 - tau) * T0[r] + tau * F(r == j, 20) for r in range(1, 5)}
        e = tau * F(overlap, 20)
        need(sum(z.values()) == F(1, 2) and sum(t.values()) == F(1, 20)
             and min(z.values()) >= 0 and min(t.values()) >= 0 and 0 <= e <= t[1], "legal raw budgets")
        bad3 = 1 - 2 * sum(z[r] for r in FACE)
        bad5 = 1 - 20 * (t[1] - e)
        rho3 = 1 + F(3, 17) * bad3
        ref = {r: F(2, 3) - (F(2, 3) - z[r]) / rho3 if r in FACE else F(0) for r in ROWS}
        need(sum(ref.values()) == F(1, 2) and min(ref.values()) >= 0
             and all(ref[r] >= z[r] for r in FACE), "legal five-leaf reference")
        a = (12 - 20 * t[1]) / 11
        b = (8 - 20 * t[1] + 20 * e) / 7
        rho = max(rho3 * a, b)
        need(a <= 1 + bad5 / 11 and b == 1 + bad5 / 7, "joint quinary bad mass")
        ga = sum(z[r] for r in ROWS if r % 3 == 2)
        gr = sum(z[r] for r in ROWS if r % 9 == 8)
        reserve = R0 + F(6, 5) * ga + (9 - ga) * t[2] + gr + (3 - gr) * t[3] + (9 - ga) * e
        need(reserve >= R0, "reserve lower bound")
        ratios = []
        for region, x in product(REGIONS, C):
            w, wref = weight(z, t, e, region, x), weight(ref, T0, F(0), region, x)
            need(0 <= w <= rho * wref and wref > 0, "four-region source domination")
            ratios.append(w / wref)
            checks += 1
        need(max(ratios) == rho, "attained maximum region/cell ratio")
        if tau <= radius:
            need(rho <= tube_rho and 14 * reserve - rho * g0 >= tube_slack, "uniform tube")
        cases += 1

    prefixes = []
    for h3, h5 in ((12, 8), (13, 8), (11, 8), (12, 7), (11, 9)):
        alpha, beta = F(1, 3 ** (h3 - 3)), F(1, 5 ** (h5 - 2))
        bound = max((1 + F(3, 17) * alpha) * (1 + beta / 11), 1 + beta / 7)
        slack = 14 * R0 - bound * g0
        prefixes.append({"H3": h3, "H5": h5, "additional_phase_conditions": h3 + h5 - 5,
                         "alpha": str(alpha), "beta": str(beta), "weight_ratio_upper": str(bound),
                         "slack_lower": str(slack), "strictly_positive": slack > 0})
    need(F(prefixes[0]["slack_lower"]) == F(87611182897, 199691894531250),
         "15-condition complete-tail margin")
    need(all(p["strictly_positive"] == (i < 2) for i, p in enumerate(prefixes)), "negative screens")
    need(set(FACE) == {h for h in ROWS if h % 3 == 1}, "root1 among retained ternary leaves")
    return {
        "scope": "Fixed discrete chart, physical domain Xi0^6 only. Exact rational samples and analytic tail constants, no full geometry or new Lean verification.",
        "branch_certificate_sha256": pin, "certified_physical_tuples": branch["certified_physical_tuples"],
        "source_face_support": FACE, "common_G_upper": str(g0), "uniform_face_margin_lower": str(delta),
        "raw_tube_radius": str(radius), "tube_weight_ratio_upper": str(tube_rho),
        "tube_slack_lower": str(tube_slack), "finite_source_cases": cases, "finite_region_cell_checks": checks,
        "prefix_certificates_and_negative_controls": prefixes,
        "boundary": "The 15-condition certificate restricts completed pure3 phases4..12 to the five retained root1 leaves and pure5 phases3..8 to column1 outside c75. All legal higher tails are included. Failed lower screens are not infeasibility or lower bounds on the number of necessary conditions.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--package", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    print(json.dumps(verify(args.package), sort_keys=True, indent=2))
