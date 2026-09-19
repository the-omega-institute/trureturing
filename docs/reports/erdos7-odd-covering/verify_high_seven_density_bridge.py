#!/usr/bin/env python3
"""Exact DV hinge consumer on every finite seven height.

All original 357 parts divide 45*7^H, for arbitrary finite H. Original
11/13/17/19 heights and cofactors are retained. The adjacent ordinary proof
establishes support, comparison and universal quantifiers; this program
checks pinned source inputs, complete geometric sums and rational bounds.
No Lean proof or unrestricted covering conclusion is claimed. Standard
library only; checks remain enabled under python3 -I -O.
"""
from __future__ import annotations

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text

import argparse
from fractions import Fraction as F
from itertools import product
import json
from math import prod
from pathlib import Path
import runpy


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def unique(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, "duplicate JSON key")
        out[key] = value
    return out


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def verify(source_path, upstream_path):
    root = Path(__file__).resolve().parent
    # Reuse the existing hash-bound DV consumer, including its upstream
    # section digest and full source geometry/old-test inventory checks.
    base = runpy.run_path(str(root / "verify_density_bridge.py"))["verify"](
        source_path, upstream_path)
    M0 = F(base["inputs"]["M"])
    D0 = F(base["density_domination_D"])
    H0 = {int(k): F(v) for k, v in base["inputs"]["hinges"].items()}
    H0[1] = M0 - 1
    require(sorted(H0) == [1] + list(range(4, 13)), "source hinge domain")

    def source_hinge(t):
        if t <= 1:
            return M0 - t
        for a, b in zip(sorted(H0), sorted(H0)[1:]):
            if a <= t <= b:
                return ((b-t)*H0[a] + (t-a)*H0[b])/(b-a)
        raise ArithmeticError("hinge query outside the retained source domain")

    primes = (3, 5, 7, 11, 13)
    rho = dict(zip(primes, (F(5, 9), F(4, 5), F(6, 7), F(10, 11), F(12, 13))))
    R = (rho[3]+F(1, 3)+F(1, 9))*(rho[5]+F(1, 5))*F(1, 42)
    R *= (rho[11]+F(1, 10))*(rho[13]+F(1, 12))
    require(R == F(5809, 240240), "complete high-seven label budget")
    # Literal finite exponent enumeration independently checks the product
    # convention, including pure-exclusion factors at exponent zero.
    ranges = (range(3), range(2), range(2, 7), range(4), range(3))
    finite = sum((prod(rho[p] if e == 0 else F(1, p**e)
                       for p, e in zip(primes, es))
                  for es in product(*ranges)), F(0))
    factors = [sum((rho[p] if e == 0 else F(1, p**e) for e in es), F(0))
               for p, es in zip(primes, ranges)]
    require(finite == prod(factors) < R, "all 360 finite original tail labels")
    beta = D0*R
    q0 = 1-beta
    D7 = D0/q0
    M7 = M0/q0
    require(beta == F(200175, 869464) and q0 == F(669289, 869464) > 0,
            "positive extension mass, all physical heights")
    require(D7 == F(306306000, 24763693), "actual-law density bridge")

    def extended_hinge(t):
        if t <= 1:
            return M7-t
        return (source_hinge(t)+beta)/q0

    # The actual physical17 cap is 2. Its complete comparison factor is
    # P(F=1)=15/17, P(F=n)=32/17^n for n>=2.
    probabilities = {n: F(15, 17) if n == 1 else F(32, 17**n)
                     for n in range(1, 8)}
    tail_mass = F(2, 17**7)  # F >= 8
    tail_mean = tail_mass*F(129, 16)
    require(sum(probabilities.values())+tail_mass == 1, "full comparison mass")
    require(sum(n*v for n, v in probabilities.items())+tail_mean == F(9, 8),
            "full comparison mean")
    excess8 = tail_mean-8*tail_mass
    require(excess8 == F(1, 8*17**7), "complete excess above eight")

    def charge(hinge, mean):
        rows = {n: pn*n*hinge(F(8, n)) for n, pn in probabilities.items()}
        tail = mean*tail_mean-8*tail_mass
        require(tail >= 0 and all(v >= 0 for v in rows.values()),
                "nonnegative charge contributions")
        b17 = hinge(F(8))/8
        b19 = (sum(rows.values())+tail)/10
        return {"b17": b17, "b19": b19, "total": b17+b19,
                "19_low_terms": rows, "19_full_tail": tail}

    core = charge(source_hinge, M0)
    high = charge(extended_hinge, M7)
    b0 = core["total"]
    b7 = high["total"]
    require(b0+F(19, 80)*D0*R > F(1, 80*17**7),
            "charge upper expression increases with actual deleted mass")
    require(b0 == F(261627396289452999368807449626177,
                    1900544377402598245753456000000000), "core hinge charge")
    require(b7 == (b0+F(19, 80)*D0*R-beta/(80*17**7))/q0 < 1,
            "same-source unnormalized two-budget charge")

    # These hinge minorants lie below j_tau on every positive integer.
    # After sqrt(tau) they decrease from zero, proving the whole tail.
    shapes = {81: (65, {4: 13}), 121: (105, {4: 9, 5: 2, 6: 6})}
    expected = {
        81: F(3546376647013190559753919296342943,
              2060148625836608295061920000000000),
        121: F(586481926980399541577236545508217779699,
               149717887422095550035593219104000000000)}
    deficits = {}
    for tau, (cap, coefficients) in shapes.items():
        endpoint = 9 if tau == 81 else 11
        def minorant(n):
            return cap-sum(c*max(F(0), n-j) for j, c in coefficients.items())
        for n in range(1, endpoint+1):
            require(0 <= max(F(0), minorant(n)) <= min(cap, max(0, tau-n*n)),
                    "capped hinge minorant at every integer below the tail")
        require(minorant(F(endpoint)) == 0 and sum(coefficients.values()) > 0,
                "nonpositive decreasing entire minorant tail")
        cost0 = sum(c*H0[j] for j, c in coefficients.items())
        cost7 = sum(c*extended_hinge(F(j)) for j, c in coefficients.items())
        C = (cap-cost0-cap*b0)/D0
        test_price = sum(coefficients.values())+F(19*cap, 80)
        forbidden_price = cap*(1-F(1, 80*17**7))
        direct = (cap-cost7-cap*b7)/D7
        bound = C-test_price*R-forbidden_price*R
        require(direct == bound == expected[tau] > 0,
                "positive actual deficit and two-budget cancellation")
        deficits[tau] = {"cap": cap, "hinge_coefficients": coefficients,
                         "core_deficit_lower": C, "test_tail_price": test_price,
                         "forbidden_tail_price": forbidden_price,
                         "equal_tail_positive_threshold": C/(test_price+forbidden_price),
                         "high7_deficit_lower": bound}
    require(deficits[81]["high7_deficit_lower"] > F(1721417864, 10**9),
            "strict displayed81 lower bound")
    require(deficits[121]["high7_deficit_lower"] > F(3917246877, 10**9),
            "strict displayed121 lower bound")
    return encode({
        "schema": "erdos7-high-seven-density-bridge-v1",
        "scope": "Every original357 part divides45*7^H for arbitrary finiteH; all original11/13/17/19 heights and cofactors; actual AP13 and the same killed17/19 rows; no unrestricted3/5 or later-prime conclusion; ordinary proof and rational checks, not Lean",
        "source_sha256": base["source_sha256"],
        "upstream_sections_sha256": base["upstream_sections_sha256"],
        "inputs": {"M0": M0, "D0": D0, "hinges": H0},
        "pure_support_fractions": rho,
        "complete_high7_budget": R, "finite_label_count": 360,
        "finite_label_sum": finite, "remaining_label_sum": R-finite,
        "extension": {"deleted_mass_upper": beta, "retained_mass_lower": q0,
                      "density_domination": D7, "mean_upper": M7},
        "comparison17": {"low_probabilities": probabilities,
                         "tail_from8_mass": tail_mass, "tail_from8_mean": tail_mean,
                         "excess_above8": excess8},
        "core_charge": core, "high7_charge": high, "deficits": deficits})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    root = Path(__file__).resolve().parent
    parser.add_argument("--source-certificate", type=Path,
                        default=root / 'certificates/actual_deletion_profile_certificate.json')
    parser.add_argument("--upstream-profile", type=Path,
                        default=root / 'certificates/marked_head_profile_certificate.json')
    parser.add_argument("--write", type=Path)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    result = verify(args.source_certificate, args.upstream_profile)
    if args.check:
        require(result == json.loads(read_artifact_text(args.check), object_pairs_hook=unique),
                "saved high-seven certificate matches reconstruction")
    if args.write:
        write_certificate_text(args.write, json.dumps(result, indent=2)+"\n")
    print(json.dumps({"retained_mass_lower": result["extension"]["retained_mass_lower"],
                      "two_stage_charge_upper": result["high7_charge"]["total"],
                      "deficits": {k: v["high7_deficit_lower"]
                                   for k, v in result["deficits"].items()}}))


if __name__ == "__main__":
    main()
