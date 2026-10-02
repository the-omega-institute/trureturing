"""New finite controls for pure powers plus ternary squarefree pair labels.

All families are given as actual distinct numerical moduli and one CRT residue.
Only the explicit output path is written. No external inputs or filesystem discovery.
"""
import argparse
from fractions import Fraction as F
from functools import reduce
from itertools import product
from operator import mul
from pathlib import Path
import json

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--output", type=Path, required=True)
args = parser.parse_args()

checks = []

def ck(name, condition):
    if not condition:
        raise RuntimeError(name)
    checks.append(name)

def rat(x):
    x = F(x)
    return {"numerator": x.numerator, "denominator": x.denominator}

def prod(xs):
    return reduce(mul, xs, 1)

def crt(parts):
    modulus = prod(parts)
    residue = sum(a * (modulus // m) * pow(modulus // m, -1, m)
                  for m, a in parts.items()) % modulus
    return modulus, residue

rows = []
q_ref = (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
hs = (0, 5, 4, 3, 3, 3, 3, 3, 3, 3, 3)
for i, q in enumerate(q_ref):
    if i == 0:
        fee = F(0)
    else:
        h = hs[i]
        fee = F(3 * i, 2 * 3 ** h * (q - 1 - h * i))
        candidates = [(F(3 * i, 2 * 3 ** k * (q - 1 - k * i)), k)
                      for k in range((q - 2) // i + 1)]
        ck(f"fixed_threshold_minimum_q{q}", fee == min(candidates)[0])
    rows.append({"q": q, "d_bound": i, "h": hs[i], "fee": fee})
sum10 = sum((x["fee"] for x in rows[:10]), F(0))
sum11 = sum((x["fee"] for x in rows[:11]), F(0))
ck("complete10_budget", sum10 == F(161, 324))
ck("complete10_positive_gap", F(1, 2) - sum10 == F(1, 324))
ck("complete11_this_budget_fails", sum11 == F(179, 324) and sum11 > F(1, 2))
tail11 = F(3, 2) * F(1, 3 ** 4) / (1 - F(1, 3))
ck("two_degenerate_geometric_tail", tail11 == F(1, 36))
ck("two_degenerate_no5_gap", F(1, 2) - F(1, 6) - tail11 == F(11, 36))
ck("two_degenerate_protected5_gap", F(1, 2) - F(1, 18) - F(1, 6) - tail11 == F(1, 4))
ck("forest_geometric_budget", F(3, 2) * F(1, 3 ** 3) / (1 - F(1, 9)) == F(1, 16))

def pure(p, e, a):
    m, r = crt({p ** e: a})
    return {"modulus": m, "residue": r, "kind": "pure", "p": p, "e": e}

def pair(q, r, k, t, a, b):
    parts = {q: a, r: b}
    if k:
        parts[3 ** k] = t
    m, x = crt(parts)
    return {"modulus": m, "residue": x, "kind": "pair", "q": q, "r": r, "k": k}

families = [
    {"name": "blocked_history_with_two_pure_depths", "order": (7, 5),
     "heights": {3: 3, 5: 2, 7: 2},
     "originals": [pure(3, 1, 0), pure(5, 1, 4), pure(5, 2, 8),
                   pure(7, 1, 6), pure(7, 2, 12)]
                  + [pair(7, 5, k, 1, 0, k) for k in range(4)]},
    {"name": "path_with_pure_and_disjoint_ternary_phases", "order": (5, 7, 11),
     "heights": {3: 2, 5: 2, 7: 1, 11: 1},
     "originals": [pure(3, 1, 0), pure(3, 2, 1), pure(5, 1, 4),
                   pure(5, 2, 8), pure(7, 1, 6), pure(11, 1, 10)]
                  + [pair(q, r, k, (2*k+edge) % (3 ** k),
                          (k+edge) % q, (2*k+edge) % r)
                     for edge, (q, r) in enumerate(((5, 7), (7, 11)))
                     for k in range(3)]},
    {"name": "triangle_with_complete_first_three_ternary_layers", "order": (5, 7, 11),
     "heights": {3: 2, 5: 2, 7: 1, 11: 1},
     "originals": [pure(3, 1, 0), pure(5, 1, 4), pure(5, 2, 8),
                   pure(7, 1, 6), pure(11, 1, 10)]
                  + [pair(q, r, k, (k+edge) % (3 ** k),
                          (2*k+edge) % q, (k+2*edge) % r)
                     for edge, (q, r) in enumerate(((5, 7), (5, 11), (7, 11)))
                     for k in range(3)]},
]

def audit_family(fam):
    name, order, heights, labels = (fam[k] for k in ("name", "order", "heights", "originals"))
    ck(name + ":distinct_labels", len({o["modulus"] for o in labels}) == len(labels))
    ck(name + ":odd_nonunit", all(o["modulus"] > 1 and o["modulus"] % 2 for o in labels))
    moduli = {p: p ** h for p, h in heights.items()}
    period = prod(moduli.values())
    ck(name + ":all_labels_resolved", all(period % o["modulus"] == 0 for o in labels))
    T = moduli[3]
    domains = {q: tuple(range(moduli[q])) for q in order}
    pure_labels = {p: [o for o in labels if o["kind"] == "pure" and o["p"] == p] for p in heights}
    allowed = {p: tuple(x for x in range(moduli[p])
                         if all(x % o["modulus"] != o["residue"] for o in pure_labels[p]))
               for p in heights}
    alpha = F(len(allowed[3]), T)
    sigma = {q: 1 - F(len(allowed[q]), moduli[q]) for q in order}
    for q in order:
        ck(name + f":pure_mass_{q}", sigma[q] <= F(1, q - 1))
    ck(name + ":pure3_mass", alpha >= F(1, 2))
    assigned = {q: [] for q in order}
    neighbors = {q: set() for q in order}
    for o in labels:
        if o["kind"] == "pair":
            earlier, later = sorted((o["q"], o["r"]), key=order.index)
            assigned[later].append(o)
            neighbors[later].add(earlier)
    d = {q: len(neighbors[q]) for q in order}
    for q in order:
        for k in range(heights[3] + 1):
            ck(name + f":inventory_{q}_{k}", sum(o["k"] == k for o in assigned[q]) <= d[q])
    def active(o, t):
        return t % (3 ** o["k"]) == o["residue"] % (3 ** o["k"])
    c = {q: [sum(active(o, t) for o in assigned[q]) for t in range(T)] for q in order}
    good = [t for t in allowed[3] if all(c[q][t] <= q - 2 for q in order)]
    bad = {q: [t for t in allowed[3] if c[q][t] >= q - 1] for q in order}
    betas = {}
    for q in order:
        if not d[q]:
            betas[q] = F(0)
            continue
        local = [alpha]
        for h in range((q - 2) // d[q] + 1):
            z = sum((F(sum(active(o, t) for t in allowed[3]), T)
                     for o in assigned[q] if o["k"] >= h), F(0))
            bound = z / (q - 1 - h * d[q])
            geometric = F(3 * d[q], 2 * 3 ** h * (q - 1 - h * d[q]))
            ck(name + f":actual_bad_bound_{q}_{h}", F(len(bad[q]), T) <= bound)
            ck(name + f":geometric_bound_{q}_{h}", bound <= geometric)
            local.append(bound)
        betas[q] = min(local)
    good_mass = F(len(good), T)
    ck(name + ":joint_good_budget", good_mass >= alpha - sum(betas.values(), F(0)))

    # Independent full original CRT predicate: enumerate integers, not a product formula.
    survivor_by_t = [0] * T
    for x in range(period):
        if all(x % o["modulus"] != o["residue"] for o in labels):
            survivor_by_t[x % T] += 1
    total_private = period // T
    integral_lower = F(0)
    local_histories = 0
    for t in allowed[3]:
        lower = prod(max(F(0), 1 - F(c[q][t], q) - sigma[q]) for q in order)
        ck(name + f":literal_fibre_{t}", F(survivor_by_t[t], total_private) >= lower)
        integral_lower += lower / T
        # Sequential independent check on every legal earlier word.
        previous = [()]
        for i, q in enumerate(order):
            next_previous = []
            for hist in previous:
                old = dict(zip(order[:i], hist))
                actual_good_values = []
                for xq in allowed[q]:
                    conflict = False
                    for o in assigned[q]:
                        if not active(o, t):
                            continue
                        earlier = o["q"] if o["r"] == q else o["r"]
                        if old[earlier] % earlier == o["residue"] % earlier and xq % q == o["residue"] % q:
                            conflict = True
                            break
                    if not conflict:
                        actual_good_values.append(xq)
                ck(name + f":history_{local_histories}",
                   F(len(actual_good_values), moduli[q]) >= max(F(0), 1 - F(c[q][t], q) - sigma[q]))
                local_histories += 1
                next_previous.extend(hist + (x,) for x in actual_good_values)
            previous = next_previous
        ck(name + f":CRT_agrees_with_sequential_{t}", len(previous) == survivor_by_t[t])
    actual_mass = F(sum(survivor_by_t), period)
    rho_product = prod(F(q - 2, q * (q - 1)) for q in order)
    ck(name + ":integrated_lower_bound", actual_mass >= integral_lower)
    ck(name + ":good_mass_lower_bound", actual_mass >= good_mass * rho_product)
    if name.startswith("blocked_history"):
        ck(name + ":genuine_bad_count_fibre", c[5][1] == 4 and 1 in bad[5])
        no_current = all(any(x5 % o["modulus"] == o["residue"] for o in pure_labels[5])
                         or any(active(o, 1) and o["residue"] % 7 == 0 and x5 % 5 == o["residue"] % 5
                                for o in assigned[5]) for x5 in domains[5])
        ck(name + ":fully_deleted_earlier_history", no_current and 0 in allowed[7])
    return {"name": name, "order": order, "heights": heights, "period": period,
            "originals": labels, "predecessors": d, "pure3_mass": rat(alpha),
            "actual_bad_masses": {str(q): rat(F(len(bad[q]), T)) for q in order},
            "good_ternary_mass": rat(good_mass), "actual_full_survivor": rat(actual_mass),
            "integrated_local_lower": rat(integral_lower), "good_mass_lower": rat(good_mass * rho_product),
            "legal_history_checks": local_histories}

fixture_results = [audit_family(f) for f in families]
result = {
    "status": "all_new_exact_controls_passed", "check_count": len(checks),
    "scope": "Finite actual-label controls and rational table; the universal claims require the companion mathematical proof.",
    "table": [{**x, "fee": rat(x["fee"])} for x in rows],
    "complete10_budget": rat(sum10), "complete11_same_budget": rat(sum11),
    "uniform_good_mass": {"complete10": rat(F(1, 324)), "two_degenerate_no5": rat(F(11, 36)),
                          "two_degenerate_protected5": rat(F(1, 4)), "forest_reuse": rat(F(7, 16))},
    "fixtures": fixture_results,
}
out = args.output
out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({"output": str(out), "status": result["status"], "check_count": len(checks),
                  "fixtures": [{k: f[k] for k in ("name", "period", "actual_full_survivor", "good_ternary_mass", "legal_history_checks")}
                               for f in fixture_results]}, indent=2))
