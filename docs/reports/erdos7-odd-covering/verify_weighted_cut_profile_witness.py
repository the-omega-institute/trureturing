#!/usr/bin/env python3
"""Check a feasible weighted-cut necessary profile at N=11486475.

The checked inequalities are only necessary conditions for a covering:
for p^a || N and 1 <= k <= a,

    sum_{v_p(m) >= a-k+1} p^(a-v_p(m)) >= p^k.

The certificate also checks the reciprocal-density prerequisite.  It is a
profile feasibility witness, not a covering and not a proof that the
Erdos--Selfridge problem has a solution at this N.
"""

import json
from math import prod
from pathlib import Path

ROOT = Path(__file__).resolve().parent
N = 11486475
FACTORS = {3: 3, 5: 2, 7: 1, 11: 1, 13: 1, 17: 1}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def valuation(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def divisors(factors):
    ds = [1]
    for p, h in factors.items():
        ds = [d * p**e for d in ds for e in range(h + 1)]
    return sorted(ds)


def compute():
    labels = [17, 13, 221, 11, 2431, 7, 119, 17017, 5, 85, 1105,
              12155, 60775, 425425, 3, 51, 663, 7293, 9, 3828825,
              459459, 1640925, 11486475]
    all_divisors = divisors(FACTORS)
    require(len(all_divisors) == 192, "complete divisor count")
    require(len(labels) == 23 and len(set(labels)) == len(labels),
            "distinct witness labels")
    require(all(m > 1 and m % 2 == 1 and N % m == 0 for m in labels),
            "odd nonunit divisors of N")
    density_numerator = sum(N // m for m in labels)
    require(density_numerator >= N, "reciprocal density prerequisite")
    cuts = []
    for p, a in FACTORS.items():
        for k in range(1, a + 1):
            threshold = a - k + 1
            lhs = sum(p ** (a - valuation(m, p))
                      for m in labels if valuation(m, p) >= threshold)
            rhs = p**k
            require(lhs >= rhs, f"weighted cut p={p}, k={k}")
            cuts.append({"prime": p, "height": a, "k": k,
                         "threshold": threshold, "lhs": lhs, "rhs": rhs,
                         "slack": lhs - rhs})
    return {
        "N": N,
        "factorization": {str(p): h for p, h in FACTORS.items()},
        "labels": labels,
        "label_count": len(labels),
        "density_numerator": density_numerator,
        "density_denominator": N,
        "weighted_cuts": cuts,
        "scope": "necessary-profile feasibility only; labels are not a cover",
        "conclusion": "all checked weighted cuts and density prerequisite pass",
    }


def main():
    data = compute()
    cert = ROOT / "certificates/weighted_cut_profile_witness_certificate.json"
    require(json.loads(cert.read_text(encoding="utf-8")) == data,
            "fixed weighted-cut profile certificate")
    print(json.dumps({"result": "PASS", "N": N,
                      "label_count": data["label_count"],
                      "density": f"{data['density_numerator']}/{N}",
                      "cut_count": len(data["weighted_cuts"])},
                     sort_keys=True))


if __name__ == "__main__":
    main()
