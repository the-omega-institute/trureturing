"""Finite source-faithful checks for the TM67 parameter frontier.

This is arithmetic evidence for the complete composition image and the
explicit policy.  It is not an all-policy search, a controller search, a
Lean certificate, or a physical/source-production check.
"""

import argparse
import json
from collections import defaultdict
from pathlib import Path


def ceildiv(a, b):
    return (a + b - 1) // b


def params(cap):
    h, delta = divmod(cap, 4)
    L = ceildiv(h, 4)
    N = h - 2 * L
    s = 4 * L - h
    t = s // 2
    Q = 3 * L - 3 - 2 * t
    return h, delta, L, N, s, t, Q


def points(cap):
    h = cap // 4
    return [(z, w) for z in range(2, h + 1)
            for w in range(z + 1, 2 * z)]


def supplier(cap, z, w):
    h, _, L, _, _, _, _ = params(cap)
    if w > h:
        return 1
    if z <= 2 * L:
        return 1 + (z - 1) % L
    x, y = z - 2 * L, w - 2 * L
    return (x + 1) // 2 if x % 2 == y % 2 else (y + 1) // 2


def target(cap, z, w):
    h = cap // 4
    if w > h:
        return ("Z", z)
    c = (4 * (2 * z - w), 4 * (w - z))
    return ("T2", z, w, c) if z + w <= h else ("T1", z, w, c)


def prefix(cap, z, w, small_boundary):
    h, _, L, N, _, _, _ = params(cap)
    i = supplier(cap, z, w)
    if i == 1 or (small_boundary and i != 2):
        accepted = 4 * w <= cap
        return i, "OA" if accepted else "OR", 4 * w if accepted else 4 * z, 0
    if not small_boundary and 2 * L + 2 * i - 2 >= h:
        accepted = 4 * w <= cap
        return i, "OA" if accepted else "OR", 4 * w if accepted else 4 * z, 0
    if small_boundary:
        c = 2 * L + 2
        e = cap - 4 * (c + 1) + 1
        d = ceildiv(e, 2)
    else:
        c = 2 * L + 2 * i - 2
        e = cap - 4 * c
        d = max(e - 3, ceildiv(e, 2))
    accepted_context = 4 * z + d <= cap
    if accepted_context:
        accepted_rho = 4 * w + e <= cap
        return (i, "AA" if accepted_rho else "AR",
                4 * w + e if accepted_rho else 4 * z + d, d)
    accepted_rho = 4 * w <= cap
    return i, "RA" if accepted_rho else "RR", 4 * w if accepted_rho else 4 * z, 0


def dictionaries(cap, small_boundary):
    table = defaultdict(dict)
    collisions = []
    for z, w in points(cap):
        i, branch, entry, _ = prefix(cap, z, w, small_boundary)
        key = (i, branch)
        old = table[key].get(entry)
        new = target(cap, z, w)
        if old is not None and old != new:
            collisions.append([key, entry, old, new])
        table[key][entry] = new
    expected = defaultdict(set)
    observed = defaultdict(set)
    for z, w in points(cap):
        expected[supplier(cap, z, w)].add(target(cap, z, w))
    for (i, _), entries in table.items():
        observed[i].update(entries.values())
    missing = {str(i): len(expected[i] - observed[i])
               for i in expected if expected[i] - observed[i]}
    return table, collisions, missing


def check_cap(cap):
    h, delta, L, N, s, t, Q = params(cap)
    small = N in (3, 4)
    table, collisions, missing = dictionaries(cap, small)
    assert not collisions, (cap, collisions[:1])
    assert not missing, (cap, missing)
    branch_sizes = {f"{i}:{branch}": len(entries)
                    for (i, branch), entries in sorted(table.items())}
    if N <= 2:
        assert max((len(x) for x in table.values()), default=0) >= 1
        material = 0
        call_bound = None
    elif N in (3, 4):
        e = 4 * (N - 3) + delta + 1
        material = ceildiv(e, 2)
        assert material == ceildiv(e, 2)
        call_bound = None
    else:
        material = cap - 8 * L - 11
        tail_q = Q
        call_bound = 2 + (tail_q - 1).bit_length()
        # The actual source (2,3) is in the symbol-2 branch and accepts d_2.
        c2 = 2 * L + 2
        e2 = cap - 4 * c2
        d2 = max(e2 - 3, ceildiv(e2, 2))
        assert d2 == material and 4 * 2 + d2 <= cap
        assert h >= 2 * L + 5
        epsilon = s - 2 * t
        j = L - t
        R = L + j
        c = 4 * L - 2 * t - 2
        assert R + 1 <= c <= h - 1 + epsilon
        assert c - R + j - 1 == Q
        # Every genuinely emitted i>=2 branch has at most Q entries;
        # omitted and symbol-1 branches have at most 2Q entries.
        for (i, branch), entries in table.items():
            if branch in ("AA", "AR", "RA", "RR"):
                assert len(entries) <= Q, (cap, i, branch, len(entries), Q)
            else:
                assert len(entries) <= 2 * Q, (cap, i, branch, len(entries), Q)
        worst = 0
        for (i, branch), entries in table.items():
            prefix_calls = 1 if branch in ("OA", "OR") else 2
            worst = max(worst, prefix_calls + (len(entries) - 1).bit_length())
        assert worst <= call_bound, (cap, worst, call_bound)
    return {
        "H": cap,
        "h": h,
        "delta": delta,
        "L": L,
        "N": N,
        "s": s,
        "t": t,
        "Q": Q,
        "material_formula": material,
        "call_bound": call_bound,
        "composition_points": len(points(cap)),
        "branch_sizes": branch_sizes,
    }


def recompute(first=8, last=803):
    cases = [check_cap(cap) for cap in range(first, last + 1)]
    regimes = defaultdict(int)
    for case in cases:
        N = case["N"]
        regimes["N<=2" if N <= 2 else "N=3,4" if N in (3, 4) else "N>=5"] += 1
    tail = [case for case in cases if case["N"] >= 5]
    return {
        "scope": "TM67 complete U_H arithmetic image and explicit policy",
        "H_range": [first, last],
        "parameter_cases": len(cases),
        "composition_cases": sum(c["composition_points"] for c in cases),
        "regime_cases": dict(regimes),
        "tail_cases": len(tail),
        "tail_material_minimum_values": sorted({c["material_formula"] for c in tail})[:8],
        "tail_call_bound_values": sorted({c["call_bound"] for c in tail}),
        "all_branch_entry_collisions": 0,
        "all_missing_targets": 0,
        "limits": [
            "This is finite arithmetic falsifier evidence, not an all-policy or controller search.",
            "Universal Euler-word/bracketing coverage uses Atomic360 and TM30/TM47 behavior congruence.",
            "No paid, physical, supplier-production, Lean, or kernel claim is made."
        ],
        "selected_cases": [cases[i] for i in (0, 19, 35, 36, 51, 52, 55, 56, 795)],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path,
                        default=Path(__file__).with_suffix(".json"))
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    text = json.dumps(recompute(), ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    if args.write:
        args.certificate.write_text(text, encoding="utf-8")
    else:
        assert args.certificate.read_text(encoding="utf-8") == text
    print("TM67 parameter frontier arithmetic: PASS (796 caps, 5,333,200 points)")


if __name__ == "__main__":
    main()
