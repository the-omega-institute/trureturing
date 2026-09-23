#!/usr/bin/env python3
"""Reconstruct a reachable ambiguity pair from its literal congruences.

Uses Python 3.9+ standard-library exact arithmetic. The two prescribed
chains share numerical moduli and next-stage labels, but two earlier
residues differ. This is an information counterexample, not a cover.
"""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from math import gcd, lcm
from pathlib import Path
import json


PURE = ((5, 0), (9, 1), (49, 1))
EARLIER = (
    ((21, 1), (1323, 2), (735, 541), (945, 596)),
    ((21, 1), (1323, 2), (735, 247), (945, 407)),
)
NEXT = ((33, 1), (55, 46), (539, 443), (165, 136),
        (1617, 247), (2695, 1766))
OLD_PERIOD = 27 * 5 * 49
PERIOD = OLD_PERIOD * 11


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def digest(value):
    return sha256(json.dumps(encode(value), sort_keys=True,
                            separators=(",", ":")).encode()).hexdigest()


def density(alpha, threshold, forbidden):
    if not forbidden:
        return 1 / (1 - min(alpha, threshold))
    require(alpha > 0, "A forbidden atom has positive forbidden mass")
    return max(alpha - threshold, 0) / (alpha * (1 - threshold))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    families = [PURE + earlier + NEXT for earlier in EARLIER]
    for labels in families:
        require(len(labels) == len({m for m, _ in labels}) == 13,
                "Thirteen distinct original numerical moduli")
        require(all(m > 1 and m % 2 and 0 <= a < m for m, a in labels),
                "Canonical residues at odd nonunit moduli")
        require(lcm(*(m for m, _ in labels)) == PERIOD,
                "Full original period, with all prime powers retained")
        for (m, a), (n, b) in combinations(labels, 2):
            require(not ((m % n == 0 or n % m == 0) and
                         (a - b) % gcd(m, n) == 0),
                    "No original AP is contained in another")
        require(all(14553 % m != a for m, a in labels),
                "Common literal avoiding integer")

    states = [n for n in range(OLD_PERIOD)
              if all(n % m != a for m, a in PURE)]
    require(len(states) == 4608, "Full old pure-survivor carrier")
    coordinates = {n: (n % 27, n % 5, n % 49) for n in states}
    rows = defaultdict(list)
    for n in states:
        rows[coordinates[n][:2]].append(n)
    require(len(rows) == 96 and {len(r) for r in rows.values()} == {48},
            "Exact product root law and complete seven coordinate")

    bad, alpha = [], []
    for earlier in EARLIER:
        forbidden = {n: any(n % m == a for m, a in earlier) for n in states}
        loads = {}
        for row in rows.values():
            load = F(sum(forbidden[n] for n in row), len(row))
            loads.update((n, load) for n in row)
        bad.append(forbidden)
        alpha.append(loads)

    inv = pow(OLD_PERIOD, -1, 11)
    next_rows = {}
    for n in states:
        records = []
        for t in range(11):
            full = n + OLD_PERIOD * (((t - n) * inv) % 11)
            mask = sum((1 << i) for i, (m, a) in enumerate(NEXT)
                       if full % m == a)
            require(mask == 0 or mask & (mask - 1) == 0,
                    "Distinct fixed current colors")
            records.append((full, mask))
        next_rows[n] = records
    next_alpha = {n: F(sum(mask != 0 for _, mask in records), 11)
                  for n, records in next_rows.items()}

    d, e = F(1, 96), F(1, 2)
    base = F(1, len(states))
    laws, killed, event_laws, full_event_laws = [], [], [], []
    costs, cross_moments, earlier_costs, marginal_hashes = [], [], [], []
    row_histograms = []
    for j in range(2):
        law = {n: base * density(alpha[j][n], d, bad[j][n]) for n in states}
        surviving = {n: law[n] if not bad[j][n] else F(0) for n in states}
        require(sum(law.values()) == 1 and min(law.values()) > 0,
                "Positive normalized prescribed output")
        require(all(sum(law[n] for n in row) == F(1, 96)
                    for row in rows.values()), "Each original root row is normalized")
        laws.append(law)
        killed.append(surviving)
        earlier_cost = sum(law[n] for n in states if bad[j][n])
        require(earlier_cost == F(73, 2280), "Common exact earlier loss")
        earlier_costs.append(earlier_cost)
        row_histograms.append(sorted(Counter(alpha[j][row[0]]
                                             for row in rows.values()).items()))

        events, full_events = defaultdict(F), defaultdict(F)
        physical = first_hit = cross = F(0)
        for n in states:
            current_mass = current_bad_mass = F(0)
            earlier_mask = sum(1 << i for i, (m, a) in enumerate(PURE + EARLIER[j])
                               if n % m == a)
            for full, mask in next_rows[n]:
                events[mask] += law[n] / 11
                full_events[earlier_mask | (mask << 7)] += law[n] / 11
                k = density(next_alpha[n], e, mask != 0) / 11
                current_mass += k
                if mask:
                    current_bad_mass += k
                    physical += law[n] * k
                    first_hit += surviving[n] * k
                if n % 735 == EARLIER[j][2][1] and full % 55 == 46:
                    cross += law[n] / 11
            require(current_mass == 1, "Literal eleven row normalization")
            require(current_bad_mass == max(next_alpha[n] - e, 0) / (1 - e),
                    "Actual next union gives the clipped charge")
        event_laws.append(dict(sorted(events.items())))
        full_event_laws.append(dict(sorted(full_events.items())))
        costs.append({"physical_next_charge": physical,
                      "genuine_next_first_hit": first_hit,
                      "earlier_survival": sum(surviving.values())})
        cross_moments.append(cross)
        proper = {}
        for size in (1, 2):
            for indices in combinations(range(3), size):
                marginal = defaultdict(F)
                for n in states:
                    marginal[tuple(coordinates[n][i] for i in indices)] += law[n]
                proper[indices] = dict(sorted(marginal.items()))
        marginal_hashes.append({str(k): digest(v) for k, v in proper.items()})
        if j == 0:
            first_proper = proper
        else:
            require(proper == first_proper, "Every full proper-coordinate marginal")

    require(event_laws[0] == event_laws[1] and len(event_laws[0]) == 7,
            "Entire incoming six-AP event-vector law")
    require(full_event_laws[0] != full_event_laws[1],
            "The stronger thirteen-AP vector equality is explicitly false")
    require(costs[0]["physical_next_charge"] == F(13, 117040), "First physical fee")
    require(costs[1]["physical_next_charge"] == F(1, 8360), "Second physical fee")
    require(costs[1]["physical_next_charge"] - costs[0]["physical_next_charge"]
            == F(1, 117040), "Physical ambiguity gap")
    require([c["genuine_next_first_hit"] for c in costs] == [0, F(1, 8360)],
            "Actual killed-law distinction")
    require(cross_moments == [F(13, 117040), 0], "Earlier/current event witness")

    for n in states:
        x, z, y = coordinates[n]
        a, b = x % 3 == 1, x == 2
        c, f = y % 7 == 1, y == 2
        expected = F(8, 665) * (int(a) - 6 * int(b)) * (
            int(z == 1) - int(z == 2)) * (int(c) - 6 * int(f))
        require((laws[0][n] - laws[1][n]) / base == expected,
                "Exact nonzero three-coordinate zero-margin interaction")

    # Check additional thresholds from the proved interval by reusing only
    # literal row unions, not the interaction formula or its predicted fees.
    parameter_checks = []
    for td in (F(1, 192), F(1, 96), F(1, 72)):
        for te in (F(3, 11), F(1, 2), F(6, 11) - F(1, 1000)):
            gamma = (F(6, 11) - te) / (1 - te)
            values = []
            for j in range(2):
                fee = hit = F(0)
                for n in states:
                    mass = base * density(alpha[j][n], td, bad[j][n])
                    beta = max(next_alpha[n] - te, 0) / (1 - te)
                    fee += mass * beta
                    hit += mass * beta * (not bad[j][n])
                values.append((fee, hit))
            require(values[1][0] - values[0][0] == gamma * td / (112 * (1 - td)),
                    "Parameter-interval physical formula")
            require(values[0][1] == 0 and values[1][1] == gamma / (768 * (1 - td)),
                    "Parameter-interval first-hit formula")
            parameter_checks.append({"delta7": td, "delta11": te, "values": values})

    result = {
        "scope": "Two legal families; same numerical palette and next APs, different earlier residues",
        "original_families": families, "prime_order": [3, 5, 7, 11],
        "full_coordinate_moduli": [27, 5, 49, 11], "full_period": PERIOD,
        "thresholds": {"7": d, "other_primes": e},
        "old_atom_count": len(states), "incoming_extended_atoms_per_family": len(states) * 11,
        "common_avoiding_integer": 14553, "earlier_row_load_histograms": row_histograms,
        "old_law_digests": [digest(sorted(law.items())) for law in laws],
        "proper_marginal_digests": marginal_hashes,
        "common_next_event_vector_law": event_laws[0],
        "whole_original_event_law_digests": [digest(v) for v in full_event_laws],
        "earlier_physical_charges": earlier_costs, "costs": costs,
        "cross_moment_735_and_55": cross_moments,
        "physical_fee_gap": F(1, 117040), "first_hit_gap": F(1, 8360),
        "parameter_checks": parameter_checks,
        "producer_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.output.write_text(json.dumps(encode(result), indent=2, sort_keys=True) + "\n")
    print("Exact literal-family, marginal, event-law, physical and killed checks passed.")


if __name__ == "__main__":
    main()
