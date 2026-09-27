#!/usr/bin/env python3
"""Construct odd zero-phase moduli encoding exact independent-set counts.

The reduction takes an explicit graph vertex list and has polynomial
binary input/output size. The optional
inclusion-exclusion counter and finite checks are exponential diagnostics.
Only the ordinary proof supplies the unbounded complexity statement.
"""

import argparse
import itertools
import json
import math
import sys
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def construct(vertex_count, edges):
    require(isinstance(vertex_count, int) and not isinstance(vertex_count, bool)
            and vertex_count >= 0, "vertex_count must be nonnegative")
    normalized = []
    for edge in edges:
        require(len(edge) == 2, "an edge must have two endpoints")
        i, j = edge
        require(all(isinstance(v, int) and not isinstance(v, bool) for v in edge),
                "endpoints must be integers")
        require(0 <= i < vertex_count and 0 <= j < vertex_count and i != j,
                "endpoints must be distinct valid vertices")
        normalized.append(tuple(sorted((i, j))))
    require(len(set(normalized)) == len(normalized), "duplicate edge")
    normalized.sort()
    q = 3 ** (vertex_count + 1) * math.prod(range(1, 2 * vertex_count, 2))
    blocks = [2 + q * (2 * i + 1) for i in range(vertex_count)]
    moduli = [blocks[i] * blocks[j] for i, j in normalized]
    period = math.lcm(*moduli)
    ambient_period = math.prod(blocks)
    return {
        "vertex_count": vertex_count,
        "edges": [list(edge) for edge in normalized],
        "recovery_modulus": q,
        "coprime_blocks": blocks,
        "moduli": moduli,
        "residues": [0] * len(moduli),
        "lcm": period,
        "ambient_period": ambient_period,
        "lift_factor": ambient_period // period,
    }


def recover(instance, survivor_count):
    require(isinstance(survivor_count, int) and not isinstance(survivor_count, bool)
            and 0 <= survivor_count <= instance["lcm"],
            "survivor count must be an integer in [0, lcm]")
    return (survivor_count * instance["lift_factor"]) % instance["recovery_modulus"]


def count_residues_by_inclusion_exclusion(moduli):
    """Exact exponential count from numerical moduli alone, not graph states."""
    period = math.lcm(*moduli)
    terms = [(1, 1)]
    for modulus in moduli:
        terms.extend([(math.lcm(d, modulus), -sign) for d, sign in terms])
    return sum(sign * (period // d) for d, sign in terms)


def count_independent_sets(vertex_count, edges):
    return sum(all(not ((mask >> i) & 1 and (mask >> j) & 1) for i, j in edges)
               for mask in range(1 << vertex_count))


def check():
    checks = 0
    graphs = 0
    intersection_terms = 0
    max_output_bits = 0
    for vertex_count in range(6):
        all_edges = list(itertools.combinations(range(vertex_count), 2))
        for graph_bits in range(1 << len(all_edges)):
            edges = [edge for j, edge in enumerate(all_edges) if graph_bits >> j & 1]
            instance = construct(vertex_count, edges)
            blocks, moduli = instance["coprime_blocks"], instance["moduli"]
            invariants = [
                instance["recovery_modulus"] > 2 ** vertex_count,
                all(b > 1 and b % 2 == 1 for b in blocks),
                all(math.gcd(a, b) == 1 for a, b in itertools.combinations(blocks, 2)),
                len(set(moduli)) == len(moduli),
                all(m > 1 and m % 2 == 1 for m in moduli),
                instance["ambient_period"] % instance["lcm"] == 0,
                all(1 % m != 0 for m in moduli),
            ]
            for condition in invariants:
                require(condition, "arithmetic invariant failed")
                checks += 1
            count = count_residues_by_inclusion_exclusion(moduli)
            require(0 < count <= instance["lcm"], "positive survivor count failed")
            checks += 1
            require(recover(instance, count) == count_independent_sets(vertex_count, edges),
                    "independent-set recovery failed")
            checks += 1
            if vertex_count <= 2:
                direct = sum(all(r % m != 0 for m in moduli)
                             for r in range(instance["lcm"]))
                require(count == direct, "direct period enumeration failed")
                checks += 1
            graphs += 1
            intersection_terms += 2 ** len(moduli)
            max_output_bits = max(max_output_bits, instance["ambient_period"].bit_length())
    return {
        "graphs": graphs,
        "vertex_counts": [0, 1, 2, 3, 4, 5],
        "active_checks": checks,
        "inclusion_exclusion_terms": intersection_terms,
        "largest_ambient_period_bits": max_output_bits,
        "finite_check_scope": "all labeled simple graphs through five vertices",
        "unbounded_claim": "requires the ordinary polynomial reduction proof",
    }


def main():
    # Exact periods may have more digits than Python's default text limit.
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--graph", type=Path, help="JSON with vertices=[0,...,n-1] and edges")
    parser.add_argument("--survivor-count", type=int, help="recover #IS from an oracle result")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    require(args.check != (args.graph is not None), "choose exactly one of --graph and --check")
    require(not args.check or args.survivor_count is None,
            "--survivor-count requires --graph")
    if args.check:
        result = check()
    else:
        graph = json.loads(args.graph.read_text())
        vertices = graph["vertices"]
        require(isinstance(vertices, list) and
                all(type(v) is int and v == i for i, v in enumerate(vertices)),
                "vertices must explicitly list 0,...,n-1")
        result = construct(len(vertices), graph["edges"])
        if args.survivor_count is not None:
            result["independent_set_count"] = recover(result, args.survivor_count)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
