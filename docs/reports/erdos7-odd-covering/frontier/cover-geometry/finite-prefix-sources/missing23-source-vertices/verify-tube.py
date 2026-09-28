"""Reuse pinned source certificates and check a continuous positive-weight tube.

The proof for arbitrary parameters is in the companion report. This program
checks the certificate union, its common margin, and exact rational examples.
It performs no geometry, directory traversal, or Lean verification.
"""
from contextlib import redirect_stdout
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from pathlib import Path
import argparse
import io
import json
import runpy


def need(ok, message):
    if not ok:
        raise ValueError(message)


PINS = {
    "missing23-xi7-ordinary": "69e188e3b91d7dad85f117f071835d6805dd50617a238b2479308b2fd7878c1e",
    "missing23-xi7-q": "e7b8b3a971e67976ac58a222cc05ec6be16cfeb9751c4367d13ebb110f8ec27b",
    "missing23-xi7-remaining": "b3259a86677ffc4926e1ab85e8c979b32cd05b6aad30b1c6df60c114dab401c4",
    "missing23-late280": "b25d9f4b0cd07a848afd7279a785e1a3fffefa4c03ea45a0214cde6fa834294a",
    "missing23-eta11-1-4": "22e4666f83e564cd545f1be1cf6aaf83072cfe910e35eecf569b7c66f0e11ef2",
    "missing23-eta11-rest": "939c8e92c09f14d4d74da6c8f0f9d50f5e5137be0615844870acf0b5d1fdfa45",
    "missing23-eta13-rest": "67e46905acc60676982757deed4138b833412d43a6c878788fdaf6124570f73c",
}


def pinned(path, expected):
    raw = path.read_bytes()
    need(sha256(raw).hexdigest() == expected, "pinned input: " + path.name)
    return raw


def verify(root):
    base = root.parent
    data = {name: json.loads(pinned(base / name / "coverage.json", pin))
            for name, pin in PINS.items()}
    ordinary = data["missing23-xi7-ordinary"]
    bounds = json.loads(pinned(base / "missing23-xi7-ordinary" / "bounds.json",
                              "5f506cd32264ae3c247c3055b2dd84004625d6fb7fa7aebec22fac2f365b7065"))
    current = {tuple(r["xi7"]): F(r["current7"]) for r in bounds["current7"]}
    losses = sum(map(F, ordinary["common_loss_uppers"]))
    h = F(ordinary["common_H16"])
    actual = {tuple(r["xi7"]): r for r in ordinary["actual_zero_comparisons"]}
    slacks = []
    for row in ordinary["certified"]:
        xi = tuple(row["xi7"])
        if row["route"] == "full7":
            live = F(135, 4) - current[xi] - losses
            slacks.append(14 * live - h)
        else:
            need(row["route"] == "actual-zero7", "known ordinary route")
            a = actual[xi]
            live = F(135, 4) - current[xi] - sum(map(F, a["loss_uppers"]))
            slack = 14 * live - F(a["H16"])
            need(slack == F(a["slack_lower"]) and live == F(a["live_lower"]),
                 "actual ordinary certificate arithmetic")
            slacks.append(slack)
    need(len(slacks) == 255 and min(slacks) > 0, "ordinary255 strict margins")
    margins = {"ordinary255": min(slacks)}
    old = ["missing23-late280", "missing23-eta11-1-4",
           "missing23-eta11-rest", "missing23-eta13-rest"]
    need([data[n]["covered_prefix_pairs"] for n in old] == [1600, 3200, 6400, 67200],
         "four previously proved disjoint old-source domains")
    need(sum(data[n]["covered_prefix_pairs"] for n in old) == 280 ** 2,
         "old source complete prefix-pair count")
    for name in old:
        margins[name] = F(data[name]["minimum_micro_slack"], 10 ** 6)
    q = data["missing23-xi7-q"]
    remaining = data["missing23-xi7-remaining"]
    margins["q_and_qprime"] = F(q["minimum_slack_lower_micro"], 10 ** 6)
    members = [m for g in remaining["groups"] for m in g["members"]]
    margins["remaining22"] = min(F(m["minimum_slack_lower_micro"], 10 ** 6) for m in members)
    need(margins["remaining22"] == F(remaining["minimum_slack_lower_micro"], 10 ** 6),
         "remaining22 minimum over every member")
    parts = [{tuple(r["xi7"]) for r in ordinary["certified"]},
             {(1, 4, 7, 14)}, {tuple(q["xi7"]), tuple(q["transported_xi7"])},
             {tuple(m["xi7"]) for m in members}]
    domain = set(product((1, 2), range(1, 5), (2, 4, 5, 7, 8), (1, 4, 7, 8, 11, 13, 14)))
    need([len(p) for p in parts] == [255, 1, 2, 22], "certificate partition sizes")
    need(set.union(*parts) == domain and sum(map(len, parts)) == len(domain),
         "disjoint complete280 first labels")
    delta = min(margins.values())
    need(delta == F(7424, 10 ** 6), "common certified lower margin, not a true minimum")

    source = root / "verify.py"
    pinned(source, "67cc8a7ec2784fdc30b1f9e8245ca9992b146c872613dd95ce2275aca63aa70d")
    with redirect_stdout(io.StringIO()):
        model = runpy.run_path(str(source))
    rows, carrier, regions = model["ROWS"], model["C"], model["REGIONS"]
    r0 = F(135, 4)
    g0 = 14 * r0 - delta
    radius = F(1, 50000)
    rho_radius = (1 + F(3, 5) * radius) * (1 + radius / 11)
    guaranteed_slack = 14 * r0 - rho_radius * g0
    need(guaranteed_slack > 0, "uniform tube radius remains strict")
    checks, cases = 0, 0
    for u, tau, row, (j, overlap) in product(
            (F(0), F(2, 7), F(1)), (F(0), radius, F(1, 2), F(1)),
            rows, model["QUINARY"]):
        endpoint = model["parameters"](row, j, overlap)
        ze = {h: u / 2 if h == 13 else (1 - u) / 2 if h == 22 else F(0) for h in rows}
        z = {h: (1 - tau) * ze[h] + tau * endpoint[0][h] for h in rows}
        t = {h: (1 - tau) * F(h == 1, 20) + tau * endpoint[1][h] for h in range(1, 5)}
        e = tau * endpoint[2]
        rho3 = (8 - 6 * (z[13] + z[22])) / 5
        barz = {h: F(2, 3) - (F(2, 3) - z[h]) / rho3 if h in (13, 22)
                else F(0) for h in rows}
        need(all(barz[h] >= z[h] for h in (13, 22)) and sum(barz.values()) == F(1, 2),
             "feasible reference on the certified edge")
        rho = max(rho3 * (12 - 20 * t[1]) / 11, (8 - 20 * t[1] + 20 * e) / 7)
        edge_t = {h: F(h == 1, 20) for h in range(1, 5)}
        ga = sum(z[h] for h in rows if h % 3 == 2)
        gr = sum(z[h] for h in rows if h % 9 == 8)
        reserve = r0 + F(6, 5) * ga + (9 - ga) * t[2] + gr + (3 - gr) * t[3] + (9 - ga) * e
        need(reserve == model["reserve"](z, t, e) and reserve >= r0, "reserve identity")
        ratios = []
        for reg, x in product(regions, carrier):
            w = model["weight"](z, t, e, reg, x)
            wref = model["weight"](barz, edge_t, F(0), reg, x)
            need(0 <= w <= rho * wref and wref > 0, "common positive weight domination")
            ratios.append(w / wref)
            checks += 1
        need(max(ratios) == rho, "exact maximum over four region weights")
        if tau <= radius:
            need(rho <= rho_radius and 14 * reserve - rho * g0 >= guaranteed_slack,
                 "uniform explicit tube bound")
        cases += 1
    return {
        "scope": "One fixed chart. Reuses the pinned all280^6 common positive-functional certificates; no geometry and no new Lean verification.",
        "coverage_pins": PINS, "partition_sizes": list(map(len, parts)),
        "complete_parameter_tuples": 280 ** 6,
        "reported_margin_lowers": {k: str(v) for k, v in margins.items()},
        "uniform_certified_margin_lower": str(delta),
        "margin_boundary": "Minimum of the retained certified lower bounds, not the exact minimum of actual slack or of all sharp numerical routes.",
        "reserve_lower": str(r0), "common_G_upper": str(g0),
        "tube_radius_in_raw_parameter_interpolation": str(radius),
        "uniform_weight_multiplier": str(rho_radius),
        "uniform_tube_slack_lower": str(guaranteed_slack),
        "finite_parameter_cases": cases, "finite_region_cell_checks": checks,
        "general_result": "For any point of the certified edge and any permitted parameter point of the same chart, every raw-coordinate interpolation with 0<=tau<=1/50000 is certified by positive-weight domination. General proof is in the report; the finite checks are examples.",
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--package", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    print(json.dumps(verify(args.package), sort_keys=True, indent=2))
