#!/usr/bin/env python3
"""Rational overlap check for the joint Axler prime-valuation cutoff.

The analytic theta bound, totient bound and verified primorial endpoint are
published inputs, not proved by this program. The log enclosures below use
the existing rational atanh-series implementation; no float decides a sign.
"""

import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True

from kernel_tail import floor_to_scale, log_interval


def rational(x):
    return [x.numerator, x.denominator]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    endpoint = 29996208012611
    analytic_endpoint = 29996161880813
    theta_error = Q(33277, 10**8)
    a0 = Q(94243, 10**7)
    epsilon = Q(315367, 10**12)
    log_endpoint = floor_to_scale(log_interval(Q(endpoint))[0])
    theta_lower = endpoint * (1 - theta_error / log_endpoint**2)
    log_theta_lower = floor_to_scale(log_interval(theta_lower)[0])
    gap = epsilon * log_theta_lower**3 - a0
    threshold = 1 / (1 + epsilon)
    pair_factor = (1 - Q(1, 13**6)) * (1 - Q(1, 23**5))
    if not (endpoint > analytic_endpoint and log_endpoint > 31
            and theta_lower > 1 and gap > 0):
        raise ValueError("the supplied literature cutoff does not overlap")
    if not pair_factor < threshold:
        raise ValueError("the 13 and 23 joint stopping condition failed")
    report = {
        "schema": "axler-joint-cutoff-v1",
        "status": "RATIONAL_OVERLAP_VERIFIED",
        "published_inputs": {
            "source": "https://arxiv.org/pdf/2110.13478v3",
            "finite_range": "Lemma 2.3: Robin for 5041 <= n <= N_K",
            "K": 999999476056,
            "p_K": endpoint,
            "analytic_prime_endpoint": analytic_endpoint,
            "totient_bound": "Equations (3.4)-(3.5): n/phi(n) < e^gamma*(L+a0/L^2)",
            "theta_bound": "Equation (3.3), citing Broadbent et al., Table 15",
            "a0": rational(a0),
            "theta_error": rational(theta_error),
        },
        "log_p_K_lower": rational(log_endpoint),
        "log_theta_p_K_lower": rational(log_theta_lower),
        "epsilon": rational(epsilon),
        "epsilon_times_lower_cube_minus_a0": rational(gap),
        "product_threshold": rational(threshold),
        "joint_prime_pair": {
            "primes": [13, 23],
            "positive_exponent_upper_bounds": [5, 4],
            "factor": rational(pair_factor),
            "threshold_minus_factor": rational(threshold - pair_factor),
        },
        "sources_sha256": {
            name: hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
            for name in ("axler_cutoff.py", "kernel_tail.py")
        },
        "scope": "Exact arithmetic at the published overlap endpoint; no revalidation of the published large computations and no Lean proof.",
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"],
                      "product_threshold": report["product_threshold"]}))


if __name__ == "__main__":
    main()
