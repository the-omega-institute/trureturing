#!/usr/bin/env python3
"""Independent exact counterexamples to SRCT's repeated-layer gain bound.

External source (not imported or copied):
https://github.com/OMPSHUNYAYA/Shunyaya-Residual-Capacity-Theory
revision 95531a4849fdd0a072e5cf943abd96ac7fe136bf,
01_Theorem_and_Proof/
SRCT_Modulus9_Exactly_Twice_Obstruction_Theorem_v1_15_43.md,
Corollary 7.2, Lemma 9.2, and the definitions in Section 9.

The claim tested is Delta D_true >= F * C_dec, where repeated p-layers
use F = 192*p**t and theta = (221/192)*(1+1/p)**t.  D_true is computed
from actual residue sets and one maximum capacity for each ORIGINAL
numerical divisor label.  The alleged lower bound never defines D_true.

The first case enumerates the entire 467775-point core period and takes
the single top-layer class 4 (mod 243), projecting to 4 (mod 27).
The second case retains the base class 1 (mod 15) through eight layers;
its large period uses exact constant-fiber counts, checked independently
against direct enumeration for one layer.  The coprime support 13*17
is enumerated separately and combined with each core capacity by CRT.

Scope: these are counterexamples to a published proof ingredient, not
covering systems or a resolution of Erdős #7.  No Lean claim is made.
Run with python3 -I -O; every check uses require rather than assert.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
import json
from math import gcd, prod


SOURCE_REVISION = "95531a4849fdd0a072e5cf943abd96ac7fe136bf"
BASE_FACTORS = ((3, 3), (5, 2), (7, 1), (11, 1))
BASE = prod(p**e for p, e in BASE_FACTORS)
SUPPORT = 13 * 17
THETA0 = Fraction(221, 192)
R0 = Fraction(7, 48)
BASE_EXCLUDED = frozenset((1, 3, 5, 7, 9, 11))
FULL_EXCLUDED = BASE_EXCLUDED | {13, 17}
CHECKS = 0


def require(condition, message):
    global CHECKS
    if not condition:
        raise ValueError(message)
    CHECKS += 1


def divisors(factors):
    return tuple(sorted(prod(p**j for (p, _), j in zip(factors, powers))
                        for powers in product(*(range(e + 1) for _, e in factors))))


def valuation(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def active_points(period):
    return tuple(x for x in range(period)
                 if all(x % p for p, _ in BASE_FACTORS) and x % 9 not in (1, 2))


def capacities(points, labels):
    return {m: max(Counter(x % m for x in points).values(), default=0)
            for m in labels}


def deficit(active, caps, excluded):
    return active - sum(c for m, c in caps.items() if m not in excluded)


def direct_pair(t, modulus, residue):
    factors = ((3, 3 + t),) + BASE_FACTORS[1:]
    period = BASE * 3**t
    labels = divisors(factors)
    require(period % modulus == 0, "TAKE modulus divides the actual period")
    parent = active_points(period)
    child = tuple(x for x in parent if x % modulus != residue % modulus)
    before = capacities(parent, labels)
    after = capacities(child, labels)
    require(set(before) == set(after) == set(labels), "all original divisor labels counted")
    require(all(after[m] <= before[m] for m in labels), "capacity monotonicity on real sets")
    removed = len(parent) - len(child)
    require(before[modulus] >= removed, "actual TAKE does not exceed its capacity")
    if t and valuation(modulus, 3) == 3 + t:
        # A top-layer class fixes all additional 3-adic digits, rather than
        # removing the full lift of its projected class.
        require(removed == sum(x % (modulus // 3**t) == residue % (modulus // 3**t)
                               for x in active_points(BASE)),
                "top-layer TAKE is one localized lift of its projected cell")
    return {"period": period, "active": len(parent), "child_active": len(child),
            "caps": before, "child_caps": after, "take": modulus, "residue": residue}


def renewal_shape(pair):
    caps, child = pair["caps"], pair["child_caps"]
    q = pair["take"]
    G = pair["active"] - pair["child_active"]
    u = caps[q] - G
    X = sum(caps[m] - child[m] for m in caps if m not in BASE_EXCLUDED | {q})
    Y = sum(caps[m] - child[m] for m in caps if m != 1)
    D = deficit(pair["active"], caps, BASE_EXCLUDED)
    Dp = deficit(pair["child_active"], child, BASE_EXCLUDED | {q})
    require(Dp - D == u + X, "renewal coordinates derived from actual capacities")
    require(sum(caps.values()) - sum(child.values()) == G + Y,
            "raw capacity decrease includes the identity capacity")
    return (u, X, Y, G)


def support_capacities():
    points = tuple(z for z in range(SUPPORT) if gcd(z, SUPPORT) == 1)
    caps = capacities(points, (1, 13, 17, SUPPORT))
    require(caps == {1: 192, 13: 16, 17: 12, 221: 1},
            "independent enumeration of the 13 and 17 coordinates")
    return len(points), caps


def full_state(active, core_caps, excluded, support_active, support_caps):
    # CRT gives an independent product of the actual residue populations.
    # Each original label is d*r, not an artificial duplicate family label.
    lifted = {d * r: c * support_caps[r]
              for d, c in core_caps.items() for r in support_caps}
    require(len(lifted) == len(core_caps) * len(support_caps),
            "the coprime factorization of every original label is unique")
    active_full = active * support_active
    repair = sum(c for m, c in lifted.items() if m not in excluded)
    return {"active": active_full, "raw_capacity_sum": sum(lifted.values()),
            "available_capacity_sum": repair, "deficit": active_full - repair,
            "original_divisor_labels": len(lifted)}


def compressed_uniform_pair(base_pair, t):
    """Count actual capacities above a fixed base-supported residual set.

    If a divisor fixes g<=3 ternary digits, each eligible base residue has
    3**t lifts.  If g>3, fixing the additional g-3 digits leaves exactly
    3**(3+t-g) lifts of each eligible base residue modulo its clamped label.
    Maximizing over residues therefore gives the capacity below.  No
    shadow-free family rank or deficit-gain formula is used.
    """
    labels = divisors(((3, 3 + t),) + BASE_FACTORS[1:])

    def lift(caps):
        result = {}
        for m in labels:
            g = valuation(m, 3)
            extra = max(0, g - 3)
            base_label = m // 3**extra
            result[m] = caps[base_label] * 3**(t - extra)
        return result

    return {"period": BASE * 3**t,
            "active": base_pair["active"] * 3**t,
            "child_active": base_pair["child_active"] * 3**t,
            "caps": lift(base_pair["caps"]),
            "child_caps": lift(base_pair["child_caps"]),
            "take": base_pair["take"], "residue": base_pair["residue"]}


def summarize_core(pair):
    return {"period": pair["period"], "take_modulus": pair["take"],
            "take_residue": pair["residue"], "active": pair["active"],
            "child_active": pair["child_active"],
            "raw_capacity_sum": sum(pair["caps"].values()),
            "child_raw_capacity_sum": sum(pair["child_caps"].values()),
            "deficit": deficit(pair["active"], pair["caps"], BASE_EXCLUDED),
            "child_deficit": deficit(pair["child_active"], pair["child_caps"],
                                     BASE_EXCLUDED | {pair["take"]}),
            "original_divisor_labels": len(pair["caps"])}


def compare(name, base_pair, lifted_pair, t, support_active, support_caps):
    shape = renewal_shape(base_pair)
    u, X, Y, G = shape
    F = 192 * 3**t
    theta = THETA0 * Fraction(4, 3)**t
    R_model = R0 + Fraction(t, 3)
    C_dec = u + X + (theta - 1) * Y - R_model * G
    parent = full_state(lifted_pair["active"], lifted_pair["caps"], FULL_EXCLUDED,
                        support_active, support_caps)
    child = full_state(lifted_pair["child_active"], lifted_pair["child_caps"],
                       FULL_EXCLUDED | {lifted_pair["take"]}, support_active, support_caps)
    # This is the true gain: two independently computed original-label sums.
    true_gain = child["deficit"] - parent["deficit"]
    modeled_lower_bound = F * C_dec
    require(modeled_lower_bound > true_gain, "the claimed universal lower bound is false")
    return {"name": name, "base": summarize_core(base_pair),
            "renewal_shape_u_X_Y_G": shape, "repeated_prime": 3, "repeated_layers": t,
            "lifted_core": summarize_core(lifted_pair),
            "full_period": lifted_pair["period"] * SUPPORT,
            "full_parent": parent, "full_child": child,
            "F": F, "theta": str(theta), "R_model": str(R_model),
            "true_gain": true_gain, "true_gain_over_F": str(Fraction(true_gain, F)),
            "C_dec": str(C_dec), "claimed_lower_bound_F_times_C_dec": str(modeled_lower_bound),
            "claimed_minus_true": str(modeled_lower_bound - true_gain),
            "normalized_gap": str(C_dec - Fraction(true_gain, F)),
            "claim_holds": False}


def main():
    require(BASE == 51975 and gcd(BASE, SUPPORT) == 1, "canonical source core and support")
    support_active, support_caps = support_capacities()

    base27 = direct_pair(0, 27, 4)
    localized = direct_pair(2, 243, 4)
    require(renewal_shape(localized) == renewal_shape(base27),
            "the core and localized TAKE have the same actual renewal shape")
    first = compare("direct_top_layer_27_to_243", base27, localized, 2,
                    support_active, support_caps)
    require(first["renewal_shape_u_X_Y_G"] == (0, 182, 802, 1200), "exact localized base shape")
    require(first["true_gain"] == 59402 and first["true_gain_over_F"] == "29701/864",
            "direct original-label localized gain")
    require(first["C_dec"] == "2491/54" and first["claimed_minus_true"] == "20310",
            "two-layer localized contradiction")

    base15 = direct_pair(0, 15, 1)
    direct_one = direct_pair(1, 15, 1)
    compressed_one = compressed_uniform_pair(base15, 1)
    require(direct_one == compressed_one, "compressed counts equal independent complete one-layer enumeration")
    repeated = compressed_uniform_pair(base15, 8)
    second = compare("base_supported_15_through_eight_layers", base15, repeated, 8,
                     support_active, support_caps)
    require(second["renewal_shape_u_X_Y_G"] == (0, 30, 510, 1800), "exact base-supported shape")
    require(second["true_gain_over_F"] == "3725/32" and second["C_dec"] == "4214675/13122",
            "eight-layer original-label gain contradiction")
    top_labels = [m for m in base15["caps"] if m % 27 == 0]
    top_drop = sum(base15["caps"][m] - base15["child_caps"][m] for m in top_labels)
    require(top_drop == 0, "base15 has zero capacity decrease on all original top3 labels")
    second["base_top3_raw_capacity_drop"] = top_drop
    result = {"schema": "srct-repeated-layer-counterexample-v1", "status": "PASS",
              "external_repository": "https://github.com/OMPSHUNYAYA/Shunyaya-Residual-Capacity-Theory",
              "external_revision": SOURCE_REVISION,
              "external_claim": "v1.15.43 Lemma 9.2: Delta D_true >= F*C_dec",
              "normalized_initial_classes": [[0, p] for p in (3, 5, 7, 11, 13, 17)] + [[1, 9], [2, 9]],
              "cases": [first, second], "checks": CHECKS,
              "scope": "Actual original-label capacity counterexamples to the stated repeated-layer lower bound. "
                       "These partial families do not cover; this does not settle Erdős #7 or formally verify a Lean theorem."}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
