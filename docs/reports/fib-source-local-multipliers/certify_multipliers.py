#!/usr/bin/env python3
"""Apply the archived log enclosures to new source-local multiplier queries."""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import math
import re
import sys
import types
from fractions import Fraction
from pathlib import Path
from zipfile import ZipFile


SUPPLIER_SHA256 = "e77735e9fd3dac38ca36933c3ac36776c70b0a1fe52d278256f4d7e507f3f58a"
SUPPLIER_MEMBER = "reference_event_sweep.py"
CATALOG_MEMBER = "data/certified_regular_returns_X1000.csv"


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, math.isqrt(n) + 1))


def next_prime(n: int) -> int:
    n += 1
    while not is_prime(n):
        n += 1
    return n


def local_abundancy(p: int, exponent: int) -> Fraction:
    return Fraction(p ** (exponent + 1) - 1, (p - 1) * p**exponent)


def fraction_pair(value: Fraction) -> list[str]:
    return [str(value.numerator), str(value.denominator)]


def load_supplier(archive: Path):
    with ZipFile(archive) as bundle:
        code = bundle.read(SUPPLIER_MEMBER)
        catalog = bundle.read(CATALOG_MEMBER)
    if hashlib.sha256(code).hexdigest() != SUPPLIER_SHA256:
        raise ValueError("log enclosure supplier does not match the pinned source")
    supplier = types.ModuleType("_fib_exact_log_supplier")
    sys.modules[supplier.__name__] = supplier
    exec(compile(code, SUPPLIER_MEMBER, "exec"), supplier.__dict__)
    rows = list(csv.DictReader(io.StringIO(catalog.decode())))
    indexed = {int(row["return_index"]): row for row in rows}
    if len(indexed) != len(rows):
        raise ValueError("duplicate source indices")
    return supplier, indexed, hashlib.sha256(catalog).hexdigest()


def parse_factorization(text: str) -> dict[int, int]:
    if re.fullmatch(r"\d+\^\d+(?: \* \d+\^\d+)*", text) is None:
        raise ValueError("unsupported factorization")
    pairs = [(int(p), int(e)) for p, e in re.findall(r"(\d+)\^(\d+)", text)]
    if len({p for p, _ in pairs}) != len(pairs):
        raise ValueError("duplicate prime factor")
    if any(e < 1 or not is_prime(p) for p, e in pairs):
        raise ValueError("factorization is not a positive prime factorization")
    return dict(sorted(pairs))


def run_query(supplier, row: dict[str, str], query: dict, bits: int) -> dict:
    factors = parse_factorization(row["ca_factorization"])
    n = math.prod(p**e for p, e in factors.items())

    def nested_log(integer: int):
        inner = supplier.dyadic_enclosure(
            supplier.log_interval(Fraction(integer), bits + 10), bits
        )
        if inner.lower <= 0:
            raise ValueError("log-log comparison requires an integer greater than one")
        return supplier.dyadic_enclosure(
            supplier.Interval(
                supplier.log_interval(inner.lower, bits + 10).lower,
                supplier.log_interval(inner.upper, bits + 10).upper,
            ),
            bits,
        )

    original = nested_log(n)

    def evaluate(move: dict[int, int]) -> dict:
        multiplier = Fraction(1)
        new_n = n
        for p, k in sorted(move.items()):
            exponent = factors.get(p, 0)
            if not is_prime(p) or exponent + k < 0:
                raise ValueError("illegal prime-exponent move")
            multiplier *= local_abundancy(p, exponent + k) / local_abundancy(p, exponent)
            if k >= 0:
                new_n *= p**k
            else:
                new_n //= p ** (-k)
        target = nested_log(new_n)
        gap = supplier.dyadic_enclosure(
            supplier.Interval(
                multiplier * original.lower - target.upper,
                multiplier * original.upper - target.lower,
            ),
            bits,
        )
        sign = 1 if gap.lower > 0 else -1 if gap.upper < 0 else 0
        return {
            "move": [[p, k] for p, k in sorted(move.items())],
            "new_N": str(new_n),
            "abundancy_ratio": fraction_pair(multiplier),
            "gap_lower": fraction_pair(gap.lower),
            "gap_upper": fraction_pair(gap.upper),
            "sign": sign,
        }

    absent = []
    candidate = 2
    while len(absent) < 2:
        if candidate not in factors:
            absent.append(candidate)
        candidate = next_prime(candidate)
    first, second = absent
    pool = list(factors) + [first, second]
    insertions = [evaluate({p: 1}) for p in pool]
    deletions = [evaluate({p: -1}) for p in factors]
    for p in factors:
        if supplier.log_interval(Fraction(n // p), bits).lower <= 1:
            raise ValueError("source is not proper for every deletion comparison")

    if query["pairs"] == "all":
        requested = [(p, q) for i, p in enumerate(pool) for q in pool[i:]]
    else:
        requested = query["pairs"]
        if not isinstance(requested, list):
            raise ValueError("pairs must be all or a list of prime pairs")
        if any(not isinstance(pair, list) or len(pair) != 2 for pair in requested):
            raise ValueError("invalid pair query")
    reused_pairs = query.get("reused_pairs", [])
    if not isinstance(reused_pairs, list):
        raise ValueError("reused_pairs must be a list")
    if any(not isinstance(pair, list) or len(pair) != 2
           or any(type(p) is not int for p in pair) for pair in reused_pairs):
        raise ValueError("invalid reused pair")
    reused = {tuple(sorted(pair)) for pair in reused_pairs}
    if not reused <= {tuple(sorted(pair)) for pair in requested}:
        raise ValueError("reused pair is outside the requested pair pool")
    pairs = []
    for p, q in requested:
        if type(p) is not int or type(q) is not int:
            raise ValueError("prime pair entries must be integers")
        if tuple(sorted((p, q))) in reused:
            continue
        move = {p: 1}
        move[q] = move.get(q, 0) + 1
        pairs.append(evaluate(move))
    comparisons = insertions + deletions + pairs
    return {
        "source_return_index": int(row["return_index"]),
        "source_N": str(n),
        "factorization": row["ca_factorization"],
        "present_primes": list(factors),
        "first_two_absent_primes": [first, second],
        "pair_query": query["pairs"],
        "reused_pairs": reused_pairs,
        "comparison_count": len(comparisons),
        "undecided_comparison_count": sum(value["sign"] == 0 for value in comparisons),
        "insertions": insertions,
        "deletions": deletions,
        "pairs": pairs,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--queries", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--bits", type=int, default=80)
    args = parser.parse_args()
    if args.bits < 32:
        raise ValueError("at least 32 enclosure bits are required")
    supplier, rows, catalog_hash = load_supplier(args.archive.resolve())
    query_bytes = args.queries.read_bytes()
    queries = json.loads(query_bytes)
    if not isinstance(queries, list) or not queries:
        raise ValueError("queries must be a nonempty list")
    results = []
    for query in queries:
        index = query["source_return_index"]
        if type(index) is not int or index not in rows:
            raise ValueError("unknown source return index")
        results.append(run_query(supplier, rows[index], query, args.bits))
    report = {
        "schema": "source-local-multiplier-comparisons-v1",
        "supplier_script_sha256": SUPPLIER_SHA256,
        "catalog_sha256": catalog_hash,
        "query_sha256": hashlib.sha256(query_bytes).hexdigest(),
        "bits": args.bits,
        "gap": "R * log(log(source_N)) - log(log(new_N))",
        "scope": "finite requested comparisons; prime-pool reduction is stated in README",
        "comparison_count": sum(result["comparison_count"] for result in results),
        "results": results,
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"comparisons": report["comparison_count"],
                      "undecided": sum(r["undecided_comparison_count"] for r in results)}))


if __name__ == "__main__":
    main()
