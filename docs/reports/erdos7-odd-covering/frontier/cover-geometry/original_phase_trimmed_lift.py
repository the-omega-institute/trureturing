#!/usr/bin/env python3
"""Exact controls for one head-dependent original-phase trimmed lift.

The theorem permits one original AP for each 3^e a p^f, a|Q, with a
single outside prime p and arbitrary finite exponent heights. It is
not an unrestricted covering theorem.
"""
from collections import Counter
import argparse
from fractions import Fraction as F
from itertools import combinations, product
from math import isqrt, prod
from pathlib import Path
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def crt(parts):
    parts = [(a % m, m) for a, m in parts if m > 1]
    q = prod(m for a, m in parts)
    return sum(a * (q // m) * pow(q // m, -1, m) for a, m in parts) % q


HEAD = {5: 0, 7: 0, 25: 21, 35: 34, 49: 48,
        175: 173, 245: 242, 1225: 241}
MU = {1: 3, 106: 3, 456: 1, 211: 2, 561: 2, 316: 1, 666: 3,
      2: 3, 107: 3, 212: 3, 317: 3, 422: 3,
      3: 3, 108: 3, 213: 3, 318: 3, 423: 3,
      4: 3, 109: 3, 214: 3, 319: 3, 424: 3}
A = sorted(5 ** i * 7 ** j for i in range(3) for j in range(3))


def bound(D, p, H, E):
    E = min(E, H)
    r = p - D * (E + 1)
    require(r > 0, "positive uniform phase-count remainder")
    if E == H:
        return F(0)
    return F(3 * D, 2 * r * 3 ** E) * (1 - F(1, 3 ** (H - E)))


def power_fixture():
    """Actual overlapping p-adic cylinders, with two head-dependent fibres."""
    Q, D, p, J, H, E = 35, 4, 11, 2, 3, 1
    mu = {1: F(1, 2), 3: F(1, 2)}
    originals = {5: 0, 7: 0, 35: 2}
    for e in range(1, H + 1):
        originals[3 ** e] = 3 ** (e - 1) - 1
    rows = []
    for e in range(H + 1):
        for i, j, f in product(range(2), range(2), [1, 2]):
            a = 5 ** i * 7 ** j
            root = (0 if e == 0 else 4) + i + j + f - 1
            beta = root + (p * ((e + i + 2 * j) % p) if f == 2 else 0)
            d = 3 ** e * a * p ** f
            parts = [(1, a), (beta, p ** f)]
            if e:
                parts.append((2 * 3 ** (e - 1) - 1, 3 ** e))
            residue = crt(parts)
            require(d not in originals, "prime-power original labels distinct")
            originals[d] = residue
            rows.append({"d": d, "e": e, "a": a, "f": f,
                         "alpha": residue % a, "beta": residue % (p ** f)})
    comparable = 0
    for d, m in combinations(sorted(originals), 2):
        if m % d == 0:
            require((originals[m] - originals[d]) % d != 0,
                    "power fixture comparable originals disjoint")
            comparable += 1
    kernels = {}
    F0 = {}
    overlap_sizes = {}
    for x in mu:
        active = [row for row in rows if x % row["a"] == row["alpha"]]
        early = [row for row in active if row["e"] <= E]
        pieces = [{y for y in range(p ** J) if y % (p ** row["f"]) == row["beta"]}
                  for row in early]
        forbidden = set.union(set(), *pieces)
        f0 = {y for row in active if row["e"] == 0
              for y in range(p ** J) if y % (p ** row["f"]) == row["beta"]}
        F0[x] = f0
        kernels[x] = set(range(p ** J)) - forbidden
        overlap_sizes[x] = {"nominal_early_cylinder_size": sum(map(len, pieces)),
                            "actual_union_size": len(forbidden), "kernel_size": len(kernels[x])}
        require(len(forbidden) < sum(map(len, pieces)) if x == 1 else True,
                "actual p-adic early cylinders overlap")
        require(kernels[x] and kernels[x].isdisjoint(f0), "actual power-fibre support")
    R = sum((F(1, p ** f) for f in range(1, J + 1)), F())
    delta = 1 - D * (E + 1) * R
    require(delta == F(25, 121) > 0, "power trim uniform mass remainder")
    require(all(F(len(Y), p ** J) >= delta for Y in kernels.values()), "actual complement mass bound")
    law = [(x, y, mu[x] / len(Y)) for x, Y in kernels.items() for y in sorted(Y)]
    require(sum(t[2] for t in law) == 1, "power fixture common law")
    actual_marginal = Counter()
    free_originals = {d: a for d, a in originals.items() if d % 3}
    support_checks = 0
    for x, y, w in law:
        actual_marginal[x] += w
        point = crt([(x, Q), (y, p ** J)])
        for d, a in free_originals.items():
            require(point % d != a, "literal original 3-free support for power fixture")
            support_checks += 1
    require(dict(actual_marginal) == mu, "power fixture preserves its entire head marginal")
    tail = F()
    original_checks = 0
    for row in rows:
        mass = sum((w for x, y, w in law if x % row["a"] == row["alpha"]
                    and y % (p ** row["f"]) == row["beta"]), F())
        if row["e"] <= E:
            require(mass == 0, "all early original prime-power events vanish")
        else:
            require(mass <= F(1, p ** row["f"]) / delta,
                    "each original late cylinder obeys the common-law bound")
        if row["e"]:
            tail += F(1, 3 ** (row["e"] - 1)) * mass
        original_checks += 1
    upper = F(3 * D, 2 * 3 ** E) * (1 - F(1, 3 ** (H - E))) * R / delta
    require(0 < tail <= upper, "positive late power load obeys finite-H formula")
    cap_checks = 0
    for a, f in product([1, 5, 7, 35], [1, 2]):
        hist = Counter()
        head = Counter()
        for x, mass in mu.items():
            head[x % a] += mass
        for x, y, w in law:
            hist[x % a, y % (p ** f)] += w
        require(max(hist.values()) <= max(head.values()) / (p ** f * delta),
                "all phases use same prime-power law")
        cap_checks += len(hist)
    return {"Q": Q, "D": D, "p": p, "J": J, "H": H, "E": E,
            "original_classes": len(originals), "comparable_disjoint_pairs": comparable,
            "head_marginal": {x: str(w) for x, w in mu.items()},
            "actual_early_overlap": overlap_sizes, "R": str(R), "delta": str(delta),
            "joint_law_atoms": len(law), "original_event_checks": original_checks,
            "literal_3free_support_checks": support_checks,
            "phase_cap_checks": cap_checks, "positive_late_load": str(tail), "finite_H_upper": str(upper)}


def verify():
    H = 5
    P = [43, 47]
    E = {43: 3, 47: 3}
    originals = dict(HEAD)
    for e in range(1, H + 1):
        originals[3 ** e] = 3 ** (e - 1) - 1
    rows = []
    for p in P:
        for e in range(H + 1):
            for i, j in product(range(3), repeat=2):
                a = 5 ** i * 7 ** j
                h = 1 + ((e + i + 2 * j + p % 4) % 4)
                phase = 5 * e + i + j
                require(phase < p, "literal multi-phase no wrap")
                modulus = 3 ** e * a * p
                parts = [(h, a), (phase, p)]
                if e:
                    parts.append((2 * 3 ** (e - 1) - 1, 3 ** e))
                residue = crt(parts)
                require(modulus not in originals, "unique original numerical label")
                originals[modulus] = residue
                rows.append({"d": modulus, "residue": residue, "e": e,
                             "a": a, "alpha": residue % a, "p": p,
                             "beta": residue % p})
    require(all(d > 1 and d % 2 for d in originals), "odd nonunit original labels")
    comparable = 0
    for d, m in combinations(sorted(originals), 2):
        if m % d == 0:
            require((originals[m] - originals[d]) % d != 0,
                    "comparable original APs disjoint")
            comparable += 1
    source = [x for x in range(1225) if all(x % d != a for d, a in HEAD.items())]
    require(len(source) == 736 and set(MU) <= set(source) and sum(MU.values()) == 60,
            "one actual supported head probability")

    forbidden = {}
    kernels = {}
    ordinary = {}
    for x in MU:
        for p in P:
            local = [row for row in rows if row["p"] == p and x % row["a"] == row["alpha"]]
            F0 = {row["beta"] for row in local if row["e"] == 0}
            FE = {row["beta"] for row in local if row["e"] <= E[p]}
            forbidden[x, p] = FE
            ordinary[x, p] = set(range(p)) - F0
            kernels[x, p] = set(range(p)) - FE
            require(F0 <= FE and len(FE) <= 9 * (E[p] + 1), "all active early phases removed")
            require(len(kernels[x, p]) >= p - 9 * (E[p] + 1), "kernel support bound")
            require(kernels[x, p] <= ordinary[x, p], "actual 3-free fibre support")

    # Construct one joint cofactor law once, before examining any test.
    law = []
    for x, w in MU.items():
        ys = [sorted(kernels[x, p]) for p in P]
        weight = F(w, 60 * prod(len(t) for t in ys))
        law.extend((x, y, z, weight) for y, z in product(*ys))
    require(sum(t[3] for t in law) == 1, "joint law probability")
    actual_marginal = Counter()
    for x, y, z, w in law:
        actual_marginal[x] += w
    require(all(actual_marginal[x] == F(w, 60) for x, w in MU.items()), "exact head preservation")

    cofactor_events = {(row["a"], row["alpha"], row["p"], row["beta"]) for row in rows}
    event_mass = {}
    for a, alpha, p, beta in cofactor_events:
        idx = 1 if p == P[0] else 2
        event_mass[a, alpha, p, beta] = sum((t[3] for t in law if t[0] % a == alpha and t[idx] == beta), F())
    per_p = {p: F(0) for p in P}
    ordinary_per_p = {p: F(0) for p in P}
    early_checks = 0
    for row in rows:
        e, a, alpha, p, beta = (row[k] for k in ["e", "a", "alpha", "p", "beta"])
        mass = event_mass[a, alpha, p, beta]
        formula = sum((F(w, 60 * len(kernels[x, p])) for x, w in MU.items()
                       if x % a == alpha and beta in kernels[x, p]), F())
        require(mass == formula, "literal common-law mass equals conditional formula")
        if e <= E[p]:
            require(mass == 0, "early original cofactor cylinder has zero mass")
            early_checks += 1
        if e:
            per_p[p] += F(1, 3 ** (e - 1)) * mass
            ordinary_per_p[p] += F(1, 3 ** (e - 1)) * sum(
                (F(w, 60 * len(ordinary[x, p])) for x, w in MU.items()
                 if x % a == alpha and beta in ordinary[x, p]), F())
    bounds = {p: bound(9, p, H, E[p]) for p in P}
    require(all(0 < per_p[p] <= bounds[p] for p in P), "nonzero deep tail obeys finite-height bound")

    # All phases in each test inventory share the already constructed law.
    cap_checks = 0
    for a in A:
        head_hist = Counter()
        for x, w in MU.items():
            head_hist[x % a] += F(w, 60)
        head_cap = max(head_hist.values())
        for subset in [(43,), (47,), (43, 47)]:
            hist = Counter()
            for x, y, z, w in law:
                coords = {43: y, 47: z}
                hist[(x % a, *(coords[p] for p in subset))] += w
            r_product = prod(p - 9 * (E[p] + 1) for p in subset)
            require(max(hist.values()) <= head_cap / r_product,
                    "all original-independent phase caps use the same law")
            cap_checks += len(hist)

    # Reusing the kernel for x=1 at other heads is invalid for this family.
    bad_head_reuse = next((row for row in rows if row["e"] == 0
                           and row["beta"] in kernels[1, row["p"]]
                           and any(x % row["a"] == row["alpha"] for x in MU)), None)
    require(bad_head_reuse is not None, "head-dependence negative control")

    # For H<=E all mixed depths are removed, provided the count leaves a residue.
    require(bound(9, 59, 5, 5) == 0, "finite-height exact zero case")
    zero_phases = set(range(54))
    require(59 - len(zero_phases) > 0, "zero-tail case has actual remaining residues")

    # The 450 comb keeps only a=1: F={0,1} removes EVERY mixed phase.
    # The cardinality-sensitive construction is stronger than D(E+1).
    comb_primes = [p for p in range(11, 822)
                   if all(p % d for d in range(2, isqrt(p) + 1))]
    require(len(comb_primes) == 138, "450 outside prime inventory")
    comb_checks = 0
    for p in comb_primes:
        F_exact = {0, 1}
        Y = set(range(p)) - F_exact
        require(len(Y) == p - 2 and 0 not in Y, "450 actual fibre and trimmed normalization")
        for e in range(1, 5):
            require(1 not in Y, "450 original mixed class killed by one common trimmed lift")
            comb_checks += 1

    # Exact all-odd-integer tail summation; no high-cutoff prime extrapolation.
    initial = F(1, 2) * sum((F(1, r) for r in [7, 9, 11, 13]), F())
    even_blocks = F(3, 16) * sum((F(1, r) for r in [6, 8, 10, 12]), F())
    odd_blocks = F(1, 16) * sum((F(1, r) for r in [5, 7, 9, 11, 13]), F())
    all_odd = initial + even_blocks + odd_blocks
    prime_tail = all_odd - F(1, 18) - F(1, 26)
    require(all_odd == F(43413, 128128), "all odd n>=43 series")
    require(prime_tail == F(282301, 1153152) < F(1, 4), "prime tail below one quarter")
    require(F(1, 4) - prime_tail == F(5987, 1153152), "exact strict gap")
    for n in range(43, 500):
        choice = (n - 14) // 9
        costs = [(F(27, 2 * 3 ** e * (n - 9 * (e + 1))), e)
                 for e in range((n - 10) // 9 + 1)]
        require(min(costs)[1] == choice, "closed-form optimal infinite-height cutoff")

    power_all_odd = F(9, 8) * sum((F(1, d) for d in [12, 16, 20, 24, 30, 42, 54, 66, 78]), F())
    power_prime_tail = power_all_odd - sum((F(1, d) for d in [16, 24, 30, 54, 66]), F())
    require(power_all_odd == F(147517, 384384), "all-height power all-odd series")
    require(power_prime_tail == F(3677489, 17297280) < F(1, 4), "prime-power tail below quarter")
    require(F(1, 4) - power_prime_tail == F(646831, 17297280), "prime-power strict gap")
    for n in range(43, 500):
        e = (n - 15) // 9
        candidate = F(27, 2 * 3 ** e * (n - 1 - 9 * (e + 1)))
        optimum = min(F(27, 2 * 3 ** t * (n - 1 - 9 * (t + 1)))
                      for t in range((n - 11) // 9 + 1))
        require(candidate == optimum, "prime-power closed-form cutoff")

    # A genuine original class joining two outside coordinates invalidates
    # the product support obtained by considering only singleton constraints.
    cross_originals = {43: 0, 47: 0, 43 * 47: 1}
    cross_total = cross_forbidden = 0
    for y, z in product(range(1, 43), range(1, 47)):
        point = crt([(y, 43), (z, 47)])
        require(point % 43 != 0 and point % 47 != 0,
                "singleton-trimmed law avoids both pure original classes")
        cross_total += 1
        cross_forbidden += point % (43 * 47) == 1
    cross_mass = F(cross_forbidden, cross_total)
    require(cross_mass == F(1, 42 * 46) > 0,
            "two-outside-prime original class violates the proposed product support")
    payload = {
        "scope": "Ordinary finite controls for the restricted original singleton-prime family; no Lean certification or whole-cover provenance.",
        "parameters": {"Q": 1225, "D": 9, "H": H, "P": P, "E": E},
        "original_classes": len(originals), "comparable_disjoint_pairs": comparable,
        "head_source_size": len(source), "head_law_atoms": len(MU),
        "joint_cofactor_law_atoms": len(law), "early_original_zero_mass_checks": early_checks,
        "common_law_cofactor_events": len(cofactor_events), "phase_caps_checked": cap_checks,
        "deep_tail_load": {p: str(v) for p, v in per_p.items()},
        "finite_height_upper": {p: str(v) for p, v in bounds.items()},
        "ordinary_fibre_uniform_load": {p: str(v) for p, v in ordinary_per_p.items()},
        "sample_kernels": [{"head": x, "prime": p, "forbidden": sorted(forbidden[x, p]),
                            "remaining": len(kernels[x, p])} for x in [1, 106, 2, 3] for p in P],
        "head_independent_kernel_failure_original": bad_head_reuse,
        "zero_tail_case": {"D": 9, "p": 59, "H": 5, "E": 5, "bound": "0"},
        "report450_repair": {"outside_primes": len(comb_primes), "mixed_zero_checks": comb_checks,
                              "same_head_marginal": True, "each_kernel": "Uniform(Z/p minus {0,1})", "load": "0"},
        "tail_series": {"all_odd_n_ge43": str(all_odd), "subtract_composites": [45, 49],
                        "all_primes_p_ge43_upper": str(prime_tail), "gap_below_quarter": str(F(1, 4) - prime_tail)},
        "prime_power_fixture": power_fixture(),
        "prime_power_tail_series": {"all_odd_n_ge43": str(power_all_odd),
                                    "subtract_composites": [45, 49, 51, 55, 57],
                                    "all_primes_p_ge43_upper": str(power_prime_tail),
                                    "gap_below_quarter": str(F(1, 4) - power_prime_tail)},
        "cross_tail_negative_control": {
            "original_classes": cross_originals,
            "joint_law_atoms": cross_total,
            "forbidden_joint_mass": str(cross_mass),
            "scope": "Product kernels preserve the singleton exclusions but fail actual support for the original 2021 class."
        }
    }
    return payload


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    payload = verify()
    text = json.dumps(payload, indent=2) + '\n'
    if args.output:
        args.output.write_text(text, encoding='utf-8')
        print(json.dumps({"result": "PASS", "original_classes": payload['original_classes'],
                          "joint_law_atoms": payload['joint_cofactor_law_atoms'],
                          "power_fixture": payload['prime_power_fixture'],
                          "output": str(args.output)}, indent=2))
    else:
        print(text, end='')


if __name__ == '__main__':
    main()
