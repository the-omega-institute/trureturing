#!/usr/bin/env python3
"""Finite regression for rough-to-canonical normalization and frontiers."""
import sys
sys.dont_write_bytecode = True

import argparse
from copy import deepcopy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

from robin_frontier import build


def is_prime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def factor(n):
    factors = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            exponent = 0
            while n % p == 0:
                n //= p
                exponent += 1
            factors.append((p, exponent))
        p += 1
    if n > 1:
        factors.append((n, 1))
    return factors


def rough(n, y):
    return all(p > y for p, _ in factor(n))


def geom(p, exponent):
    return sum((Fraction(1, p ** j) for j in range(exponent + 1)), Fraction(0))


def canonical(n, y):
    exponents = sorted((a for p, a in factor(n) if p > y), reverse=True)
    primes = []
    candidate = y + 1
    while len(primes) < len(exponents):
        if is_prime(candidate):
            primes.append(candidate)
        candidate += 1
    number = 1
    weight = Fraction(1)
    for p, exponent in zip(primes, exponents):
        number *= p ** exponent
        weight *= geom(p, exponent)
    return number, weight


def run(y, bound):
    certificate = build(y, bound)
    frontier = [
        (entry["number"], Fraction(*entry["weight"]))
        for entry in certificate["frontier"]
    ]
    tested = 0
    for n in range(1, bound + 1):
        if not rough(n, y):
            continue
        tested += 1
        normalized, weight = canonical(n, y)
        original_weight = Fraction(1)
        for p, exponent in factor(n):
            if p > y:
                original_weight *= geom(p, exponent)
        if not (normalized <= n and weight >= original_weight):
            raise AssertionError((y, bound, n, normalized, weight, original_weight))
        if not any(frontier_number <= normalized and frontier_weight >= weight
                   for frontier_number, frontier_weight in frontier):
            raise AssertionError(("frontier does not dominate", y, bound, n,
                                  normalized, weight))
    return {"y": y, "bound": bound, "rough_inputs": tested,
            "states": len(certificate["states"]),
            "frontier": len(frontier), "status": "PASS"}


def margin_contract():
    """Exercise the actual CLI, including untrusted certificate rejection."""
    program = Path(__file__).with_name("robin_frontier_margin.py").resolve()
    certificate = build(7, 1000)
    valid = []
    rejected = []
    with tempfile.TemporaryDirectory(prefix="robin margin ") as directory:
        root = Path(directory)

        def invoke(data, core, name):
            source = root / (name + ".json")
            output = root / (name + "-result.json")
            source.write_text(json.dumps(data))
            completed = subprocess.run(
                [sys.executable, "-B", str(program), str(source),
                 "--core", str(core), "--out", str(output)],
                cwd=root, capture_output=True, text=True, check=False,
            )
            return completed, source, output

        for bound in (1, 1000):
            data = build(7, bound)
            for core, expected in ((10080, "PASS"), (5040, "OPEN")):
                name = "valid-{}-{}".format(bound, core)
                completed, source, output = invoke(data, core, name)
                if completed.returncode != 0:
                    raise AssertionError((name, completed.stderr))
                result = json.loads(output.read_text())
                if not (
                    result["status"] == expected
                    and result["frontier_check"]["status"] == "PASS"
                    and result["certificate_sha256"] ==
                    hashlib.sha256(source.read_bytes()).hexdigest()
                    and result["minimum"]["suffix"] == 1
                ):
                    raise AssertionError((name, "incorrect margin result"))
                if core == 5040 and any(not row["positive"] for row in
                                        result["rows"] if row["suffix"] > 1):
                    raise AssertionError((name, "nonempty suffix not certified"))
                valid.append({"core": core, "bound": bound, "status": expected})

        mutations = []
        data = deepcopy(certificate)
        data["frontier"][0]["weight"] = [1, 2]
        mutations.append(("altered-root-weight", data, 10080))
        data = deepcopy(certificate)
        data["frontier"] = []
        mutations.append(("empty-frontier", data, 10080))
        data = deepcopy(certificate)
        root_state = next(state for state in data["states"]
                          if state["key"] == data["root"])
        root_state["frontier"] = [{"number": 1, "weight": [1, 2]}]
        data["frontier"] = deepcopy(root_state["frontier"])
        mutations.append(("altered-state-and-root", data, 10080))
        data = deepcopy(certificate)
        child = next(i for i, state in enumerate(data["states"])
                     if state["key"] != data["root"])
        del data["states"][child]
        mutations.append(("missing-child-state", data, 10080))
        data = deepcopy(certificate)
        del data["primes"][1]
        mutations.append(("missing-prime", data, 10080))
        data = deepcopy(certificate)
        data["frontier"][0]["weight"] = [1, 0]
        mutations.append(("zero-denominator", data, 10080))
        mutations.append(("small-core", certificate, 11))
        mutations.append(("core-outside-cutoff", certificate, 5040 * 11))
        for name, data, core in mutations:
            completed, _, output = invoke(data, core, name)
            if completed.returncode == 0 or output.exists():
                raise AssertionError((name, "invalid input produced a result"))
            rejected.append(name)
    return {"status": "PASS", "valid_scans": valid, "rejected": rejected}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    results = [run(y, bound) for y, bound in
               ((1, 256), (2, 512), (7, 1000), (11, 2000))]
    report = {"status": "PASS", "cases": results,
              "margin_contract": margin_contract(),
              "scope": "Finite normalization and margin CLI regression only."}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
