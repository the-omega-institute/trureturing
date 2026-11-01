"""One bounded ordinary-loopy-polynomial experiment for arXiv:2609.07728v1, 11.4.

Uses the byte-identical MIT gp.py at upstream commit
e7e6b31111203dd6d1304b329b9aed8e0fac3d29. No additional dependencies.
All fixtures, pilot, stress controls and search execute in this one invocation.
This program's finite results are experimental evidence, not a theorem.
"""
import time

START = time.monotonic()
START_UTC = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())

import argparse
import hashlib
import itertools
import json
import platform
import resource
import signal
import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
SEALED = Path("/private/tmp/omega-next-source-intake-20260915.hNXvvf")
HASHES = {
    "gp.py": "5e4c7663d53fc02c654ac7e69116a40abbd4a029e780602cb262cedcd6cef026",
    "LICENSE.txt": "edba575257db964ddf6a476086929ff433b3435e17b19b43195ec5a5654b1564",
}
SOURCE_HASHES = {
    "loopy-polynomial-v1.html": "e38f48ed00c59fd2a80f59395a3b08c6a42ea0ead467ac5cce029b3886394332",
    "loopy-polynomial-v1.txt": "6cc23937d307b3489593ddcbd8d0d9b3052e3a7afe173626be80603f43243ced",
    "loopy-polynomial-abs.html": "37136fb76243d67b39d9386cdf98c5ff6752ad3f75f038065018611a04b09d83",
}


def canonical(poly):
    """The whole integer polynomial; no evaluation, digest or coarse key."""
    out = {}
    for (t, xs), coefficient in poly.items():
        if type(t) is not int or t < 0 or type(coefficient) is not int:
            raise ValueError("non-integral polynomial data or negative t exponent")
        if any(type(x) is not int or x < 0 for x in xs):
            raise ValueError("invalid x index")
        key = (t, tuple(sorted(xs)))
        out[key] = out.get(key, 0) + coefficient
    return tuple(sorted((key, c) for key, c in out.items() if c != 0))


def polynomial_json(key):
    return [{"t": t, "xs": list(xs), "coefficient": c} for (t, xs), c in key]


def graph(n, loops, multiplicities):
    edges = [(v, v) for v, count in enumerate(loops) for _ in range(count)]
    edges += [pair for pair, count in zip(itertools.combinations(range(n), 2),
                                        multiplicities) for _ in range(count)]
    return edges


def degree_multiset(n, edges):
    # Called only after full exact polynomial equality has been established.
    degrees = [0] * n
    for u, v in edges:
        degrees[u] += 1
        degrees[v] += 1
    return tuple(sorted(degrees))


def fixtures():
    # Expected polynomials come directly from Definition 1.1.
    yield "empty", 0, [], {(0, ()): 1}
    for m in range(3):
        yield "bouquet_" + str(m), 1, [(0, 0)] * m, {(0, (m,)): 1}
    for a, b in [(0, 0), (0, 2)]:
        yield "edgeless_" + str((a, b)), 2, graph(2, (a, b), (0,)), {(0, (a, b)): 1}
    for a, b in [(0, 0), (0, 2), (1, 2)]:
        yield "one_edge_" + str((a, b)), 2, graph(2, (a, b), (1,)), {
            (0, (a + b + 1,)): 1, (1, (a, b)): 1}
    for a, b in [(0, 0), (1, 2)]:
        yield "two_edges_" + str((a, b)), 2, graph(2, (a, b), (2,)), {
            (0, (a + b + 2,)): 1, (1, (a + b + 1,)): 1, (2, (a, b)): 1}
    yield "edge_and_isolate", 3, graph(3, (1, 2, 0), (1, 0, 0)), {
        (0, (0, 4)): 1, (1, (0, 1, 2)): 1}


class StopProbe(Exception):
    pass


class Mismatch(Exception):
    pass


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worker-start-epoch", type=float, required=True)
    args = parser.parse_args()
    output = HERE / "results.json"
    result = {
        "question": "Does ordinary L_G determine the degree sequence of an arbitrary graph G, loops included?",
        "source": {"arxiv": "2609.07728v1", "problem": "11.4",
                   "url": "https://arxiv.org/html/2609.07728v1",
                   "sealed_directory": str(SEALED), "sha256": SOURCE_HASHES,
                   "read_scope": "Definition 1.1, Proposition 2.9, degree convention and Section 6.5/Problem 11.4; not a whole-paper independent review"},
        "semantics": {"graphs": "Finite graphs, loops and parallel edges allowed; vertex count explicitly includes isolates.",
                      "polynomial": "Ordinary L in Z[t,x_0,x_1,...]; L_G=L_(G/e)+t L_(G-e); contracted nonloop retained as a loop; bouquet m -> x_m; disjoint union -> product.",
                      "degree": "One per endpoint, hence two per loop.",
                      "canonical_monomial": "(nonnegative integer t exponent, sorted x-index tuple retaining repeated x_0); full integer coefficient dictionary"},
        "reuse": {"repository": "https://github.com/hamurav/loopy-collisions",
                  "commit": "e7e6b31111203dd6d1304b329b9aed8e0fac3d29", "tag": "v1.2.0",
                  "license": "MIT, exact notice retained", "sha256": HASHES,
                  "discovery": "unchanged loopy_recursive",
                  "cross_check": "unchanged loopy_forest on controls, every pilot graph, stress controls and candidate only",
                  "independence": "Algorithmic cross-checks sharing one upstream source and authorship; no independent definition-derived evaluator or Lean certificate."},
        "domain": {"n": [0, 1, 2, 3, 4], "loop_entries": [0, 1, 2],
                   "loop_order": "nondecreasing tuples, lexicographic", "nonloop_multiplicities": [0, 1, 2],
                   "pair_order": "lexicographic upper-triangular unordered pairs",
                   "phases_per_bucket": ["all binary vectors in lexicographic order", "all ternary vectors containing 2 in lexicographic order"],
                   "bucket": "(n, loop tuple); release table only after both phases",
                   "bucket_basis": "Proposition 2.9: unique maximal-x-degree term determines n and loop multiset, excluding cross-bucket equality.",
                   "relabelling_basis": "Any labeled graph in the box can have its loops sorted by relabeling; every nonloop vector is retained. Counts are encodings, not nonisomorphic graphs.",
                   "degree_use": "Compute and compare two degree multisets only after full exact polynomial equality; no degree-based generation, filtering, buckets or order."},
        "bounds": {"invocations": 1, "retries": 0, "total_seconds": 300,
                   "stop_generation_seconds": 240, "controls_seconds": 30, "pilot_stress_seconds": 60,
                   "rss_stop_mib": 512, "finalization_reserve_seconds": 1},
        "platform": {"system": platform.system(), "machine": platform.machine(),
                     "python": sys.version, "rss_api": "resource.getrusage(RUSAGE_SELF).ru_maxrss",
                     "rss_raw_unit": "bytes" if sys.platform == "darwin" else "KiB" if sys.platform.startswith("linux") else "unsupported",
                     "rss_enforcement": "Peak RSS observed at evaluation/graph/control boundaries; no OS hard RSS enforcement."},
        "paths": {"implementation": str(Path(__file__).resolve()), "upstream_code": str(HERE / "gp.py"),
                  "license": str(HERE / "LICENSE.txt"), "output": str(output)},
        "producer": {"skill": "none; direct Codex CLI implementation", "subagents": 0,
                     "review_seats": 0, "prior_exposure": "repository and admitted plan; no peer results read"},
        "started_utc": START_UTC, "controls": [], "stress": [], "buckets": [],
        "counts": {"generated": 0, "recursive_completed": 0, "forest_completed": 0,
                   "processed": 0, "pilot_agreements": 0, "exact_table_lookups": 0,
                   "equal_polynomial_hits": 0, "degree_comparisons": 0, "unique_polynomials": 0,
                   "evaluation_calls_started": 0, "evaluation_calls_completed": 0,
                   "recursive_calls_started": 0, "recursive_calls_completed": 0,
                   "forest_calls_started": 0, "forest_calls_completed": 0},
        "last_generated_cursor": None, "last_processed_cursor": None, "pending_evaluation": None,
        "candidate": None, "pilot_and_stress_passed": False, "rss_observations": 0,
        "peak_rss_raw": 0, "stage_seconds": {},
        "limits": ["Finite experimental evidence only; no theorem, solution, priority or KPI claim.",
                   "No independent semantic review or renewed literature/priority search in this probe.",
                   "Candidate verification, if successful here, still requires a later separately bounded independent definition-derived evaluation and renewed source/reuse checks."]}
    counts = result["counts"]
    stage = "preflight"
    stage_start = START
    deadline = START + 299
    deadline_reason = "numeric_wall_cap_with_finalization_reserve"

    def alarm(_signum, _frame):
        raise StopProbe(deadline_reason)

    def boundary(generating=False):
        raw = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        result["rss_observations"] += 1
        result["peak_rss_raw"] = max(result["peak_rss_raw"], raw)
        factor = 1 if sys.platform == "darwin" else 1024
        if raw * factor >= 512 * 1024 * 1024:
            raise StopProbe("observed_rss_cap")
        now = time.monotonic()
        if now >= deadline:
            raise StopProbe(deadline_reason)
        if generating and now - START >= 240:
            raise StopProbe("generation_wall_cap")

    def set_stage(name, cap=None):
        nonlocal stage, stage_start, deadline, deadline_reason
        now = time.monotonic()
        result["stage_seconds"][stage] = now - stage_start
        stage, stage_start = name, now
        deadline = START + 299
        deadline_reason = "numeric_wall_cap_with_finalization_reserve"
        if cap is not None and now + cap < deadline:
            deadline, deadline_reason = now + cap, name + "_wall_cap"
        signal.setitimer(signal.ITIMER_REAL, max(0.000001, deadline - now))
        boundary()

    def evaluate(algorithm, n, edges, context):
        boundary()
        if any(type(u) is not int or type(v) is not int or not (0 <= u < n and 0 <= v < n)
               for u, v in edges):
            raise ValueError("edge endpoint outside declared vertex set")
        result["pending_evaluation"] = {"algorithm": algorithm, "n": n, "edges": edges, "context": context}
        counts["evaluation_calls_started"] += 1
        counts[algorithm + "_calls_started"] += 1
        key = canonical((gp.loopy_recursive if algorithm == "recursive" else gp.loopy_forest)(n, edges))
        counts["evaluation_calls_completed"] += 1
        counts[algorithm + "_calls_completed"] += 1
        result["pending_evaluation"] = None
        boundary()
        return key

    def agree(actual, expected, context):
        if actual != expected:
            result["mismatch"] = {"context": context, "actual": polynomial_json(actual),
                                  "expected": polynomial_json(expected)}
            raise Mismatch(context)

    def enumerate_n(n):
        pairs = list(itertools.combinations(range(n), 2))
        for loops in itertools.combinations_with_replacement(range(3), n):
            table = {}
            bucket = {"n": n, "loops": loops, "generated": 0, "processed": 0,
                      "simple_processed": 0, "multiplicity_two_processed": 0,
                      "equal_polynomial_hits": 0, "unique_polynomials": 0, "complete": False}
            result["buckets"].append(bucket)
            for phase, alphabet in [("simple", range(2)), ("multiplicity_two", range(3))]:
                for vector in itertools.product(alphabet, repeat=len(pairs)):
                    boundary(generating=True)
                    if phase == "multiplicity_two" and 2 not in vector:
                        continue
                    cursor = {"n": n, "loops": loops, "phase": phase, "nonloop_vector": vector}
                    edges = graph(n, loops, vector)
                    counts["generated"] += 1
                    bucket["generated"] += 1
                    result["last_generated_cursor"] = cursor
                    key = evaluate("recursive", n, edges, cursor)
                    counts["recursive_completed"] += 1
                    if n <= 3:
                        other = evaluate("forest", n, edges, cursor)
                        counts["forest_completed"] += 1
                        agree(other, key, "pilot " + str(cursor))
                        counts["pilot_agreements"] += 1
                    counts["exact_table_lookups"] += 1
                    previous = table.get(key)
                    if previous is None:
                        table[key] = (edges, cursor, key)
                        bucket["unique_polynomials"] += 1
                        counts["unique_polynomials"] += 1
                    else:
                        first_edges, first_cursor, first_key = previous
                        agree(key, first_key, "full polynomial table equality")
                        counts["equal_polynomial_hits"] += 1
                        bucket["equal_polynomial_hits"] += 1
                        first_degrees = degree_multiset(n, first_edges)
                        degrees = degree_multiset(n, edges)
                        counts["degree_comparisons"] += 1
                        if degrees != first_degrees:
                            result["candidate"] = {"status": "unverified", "n": n,
                                "graphs": [{"edges": first_edges, "cursor": first_cursor,
                                            "polynomial": polynomial_json(first_key), "degrees": first_degrees},
                                           {"edges": edges, "cursor": cursor,
                                            "polynomial": polynomial_json(key), "degrees": degrees}],
                                "checks": []}
                    counts["processed"] += 1
                    bucket["processed"] += 1
                    bucket[phase + "_processed"] += 1
                    result["last_processed_cursor"] = cursor
                    boundary()
                    if result["candidate"] is not None:
                        return False
            bucket["complete"] = True
        return True

    signal.signal(signal.SIGALRM, alarm)
    signal.setitimer(signal.ITIMER_REAL, max(0.000001, deadline - time.monotonic()))
    try:
        result["preparation_seconds"] = time.time() - args.worker_start_epoch
        if result["preparation_seconds"] > 360:
            raise StopProbe("preparation_deadline_no_numeric_evaluations")
        if sys.platform != "darwin" and not sys.platform.startswith("linux"):
            raise ValueError("RSS unit unsupported on this platform")
        result["implementation_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        for root, entries in [(HERE, HASHES), (SEALED, SOURCE_HASHES)]:
            for name, expected in entries.items():
                actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
                if actual != expected:
                    raise ValueError("sealed hash mismatch: " + name)
        result["sealed_hashes_verified"] = True
        import gp
        set_stage("definition_controls", 30)
        for name, n, edges, expected_dict in fixtures():
            expected = canonical(expected_dict)
            record = {"name": name, "n": n, "edges": edges,
                      "expected": polynomial_json(expected), "checks_completed": 0, "passed": False}
            result["controls"].append(record)
            variants = [("original", edges)]
            if n > 1 and edges:
                relabeled = [(n - 1 - u, n - 1 - v) for u, v in edges]
                variants += [("edge_reversal", list(reversed(edges))),
                             ("vertex_reversal", relabeled),
                             ("both_reversals", list(reversed(relabeled)))]
            for variant, variant_edges in variants:
                for algorithm in ("recursive", "forest"):
                    agree(evaluate(algorithm, n, variant_edges, name + "/" + variant), expected, name + "/" + variant + "/" + algorithm)
                    record["checks_completed"] += 1
            record["passed"] = True
            boundary()
        set_stage("pilot_and_stress", 60)
        pilot_complete = all(enumerate_n(n) for n in range(4))
        if pilot_complete:
            if counts["pilot_agreements"] != 292:
                raise ValueError("observed full pilot count differs from admitted 292")
            for loops in [(0, 0, 0, 0), (1, 0, 0, 0), (2, 2, 2, 2)]:
                edges = graph(4, loops, (2,) * 6)
                record = {"n": 4, "loops": loops, "edges": edges, "passed": False}
                result["stress"].append(record)
                key = evaluate("recursive", 4, edges, "stress " + str(loops))
                other = evaluate("forest", 4, edges, "stress " + str(loops))
                agree(other, key, "stress " + str(loops))
                record["polynomial"] = polynomial_json(key)
                record["passed"] = True
                boundary()
            result["pilot_and_stress_passed"] = True
            set_stage("n4_search")
            enumerate_n(4)
        candidate = result["candidate"]
        if candidate is not None:
            set_stage("candidate_verification")
            checked_degrees = []
            for index, item in enumerate(candidate["graphs"]):
                n, edges = candidate["n"], item["edges"]
                expected = canonical({(term["t"], tuple(term["xs"])): term["coefficient"] for term in item["polynomial"]})
                for variant, variant_edges in [("original", edges), ("edge_reversal", list(reversed(edges)))]:
                    for algorithm in ("recursive", "forest"):
                        agree(evaluate(algorithm, n, variant_edges, "candidate"), expected, "candidate polynomial")
                        candidate["checks"].append({"graph": index, "variant": variant, "algorithm": algorithm, "passed": True})
                # An explicit endpoint incidence count checks the original degree calculation.
                degrees = tuple(sorted(sum(int(u == vertex) + int(v == vertex) for u, v in edges) for vertex in range(n)))
                if degrees != item["degrees"] or sum(degrees) != 2 * len(edges):
                    raise Mismatch("candidate endpoint/degree mismatch")
                checked_degrees.append(degrees)
                candidate["checks"].append({"graph": index, "endpoint_degree_check": True})
            if checked_degrees[0] == checked_degrees[1]:
                raise Mismatch("candidate degree multisets are equal")
            boundary()
            candidate["status"] = "checked_by_shared_source_algorithms"
            result["outcome"] = "checked_candidate"
            result["termination_reason"] = "first_candidate_survived_required_in_cap_checks"
        else:
            result["outcome"] = "bounded_nonfinding"
            result["termination_reason"] = "fixed_range_exhausted"
    except StopProbe as exc:
        result["outcome"] = "candidate_unverified" if result["candidate"] else "resource_cap"
        result["termination_reason"] = str(exc)
    except Exception as exc:
        result["outcome"] = "detected_error"
        result["termination_reason"] = type(exc).__name__ + ": " + str(exc)
        if result["candidate"]:
            result["candidate"]["status"] = "rejected" if isinstance(exc, Mismatch) else "unverified"
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        now = time.monotonic()
        result["stage_seconds"][stage] = now - stage_start
        result["numeric_elapsed_seconds"] = now - START
        result["worker_elapsed_seconds_at_numeric_end"] = time.time() - args.worker_start_epoch
        result["peak_rss_mib"] = result["peak_rss_raw"] * (1 if sys.platform == "darwin" else 1024) / (1024 * 1024)
        result["coverage_by_n"] = [{"n": n, "generated": sum(b["generated"] for b in result["buckets"] if b["n"] == n),
            "processed": sum(b["processed"] for b in result["buckets"] if b["n"] == n),
            "simple_processed": sum(b["simple_processed"] for b in result["buckets"] if b["n"] == n),
            "multiplicity_two_processed": sum(b["multiplicity_two_processed"] for b in result["buckets"] if b["n"] == n)} for n in range(5)]
        result["prefix_interpretation"] = "All cursors through last_processed_cursor in the stated bucket/phase order completed comparison. last_generated_cursor and pending_evaluation distinguish unfinished work. Controls/stress excluded from coverage."
        result["finished_utc"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        temporary = output.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n")
        temporary.replace(output)
        print(json.dumps({"outcome": result["outcome"], "termination_reason": result["termination_reason"],
                          "processed": counts["processed"], "numeric_elapsed_seconds": result["numeric_elapsed_seconds"],
                          "peak_rss_mib": result["peak_rss_mib"], "output": str(output)}), flush=True)
    return 1 if result["outcome"] == "detected_error" else 0


if __name__ == "__main__":
    raise SystemExit(main())
