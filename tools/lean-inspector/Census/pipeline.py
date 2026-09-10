"""Report-only census, never a gate. status=complete means accounting completion
only. Observed rows are unclassified: never certified, never a closed reason,
and never AC-023. Lean owns registration queries and certification."""

from __future__ import annotations

import json
import pathlib
import argparse
import hashlib
import os
import re
import subprocess
import sys
import time


def parse_request(value):
    if not isinstance(value, dict) or set(value) != {"root", "report"}:
        raise ValueError("census request requires exactly root and report")
    if any(not isinstance(item, str) or not item for item in value.values()):
        raise ValueError("census request values must be nonempty strings")
    return value


def validate_summary(summary, *, requested, accounted):
    if summary["requested_keys"] != requested or summary["counts"]["accounted"] != accounted:
        raise ValueError("publication requested/accounted denominator mismatch")
    complete = accounted == requested
    if summary["status"] != ("complete" if complete else "partial"):
        raise ValueError("publication accounting status mismatch")
    certified_complete = complete and summary["counts"]["certified"] == accounted
    if summary["certified_complete"] is not certified_complete:
        raise ValueError("publication certified_complete does not use the full requested key set")


def validate_fixture_export(report):
    if report.get("source_commit") != "fixture-head":
        raise ValueError("explicit input is synthetic fixture only; production revisions are rejected")
    for node in report["nodes"]:
        if not re.fullmatch(r"LeanInformationAudit/Tests/(?:[A-Za-z_][A-Za-z_0-9]*/)*[A-Za-z_][A-Za-z_0-9]*\.lean",
                            node["repo_path"]):
            raise ValueError("explicit input requires a synthetic fixture module path")


def frozen_keys(report):
    result = []
    identities = set()
    for node in report["nodes"]:
        if node["freeze_status"] not in ("frozen", "proven-not-yet-frozen"):
            raise ValueError("invalid freeze status")
        if node["freeze_status"] != "frozen":
            continue
        module = node["repo_path"].removesuffix(".lean").replace("/", ".")
        for declaration in node["declarations"]:
            if declaration["kind"] != "theorem":
                continue
            identity = declaration["statement_id"]
            if identity in identities:
                raise ValueError("duplicate statement identity")
            identities.add(identity)
            result.append((module, declaration["declaration_name_key"], identity))
    return sorted(result)


def read_keys(data):
    value = json.loads(data)
    if not isinstance(value, list) or any(
            not isinstance(row, list) or len(row) != 3
            or any(not isinstance(item, str) or not item for item in row) for row in value):
        raise ValueError("expected module, structured declaration name, statement identity triples")
    return value


def read_inventory(path):
    from report_stream import fields
    metadata, modules = {}, []

    def nodes():
        for field, value in fields(path):
            if field == "nodes":
                modules.append(value["repo_path"].removesuffix(".lean").replace("/", "."))
                yield value
            else:
                metadata[field] = value
    keys = frozen_keys({"nodes": nodes()})
    return metadata, keys, sorted(modules)


def exported_path(log):
    receipts = [line for line in log.splitlines() if line.startswith("TRUTH_EXPORT ")]
    if len(receipts) != 1 or not receipts[0].partition(" out=")[2]:
        raise ValueError("truth-export did not emit exactly one output-path receipt")
    return pathlib.Path(receipts[0].partition(" out=")[2]).resolve()


def publication_result(path):
    if path is None:
        return {"status": "not_requested"}
    value = json.loads(pathlib.Path(path).read_bytes())
    return {"status": "published", "artifact": str(path),
            "certificate": value["certificate"],
            "query_receipt_digest": value["query_receipt_digest"]}


def execute(options):
    from phases import read, write
    from resources import run
    from streaming import canonical, file_stamp, freshness, replay, root_definitions
    import shutil

    repository = pathlib.Path(__file__).resolve().parents[3]
    directory = pathlib.Path(options.output).resolve()
    directory.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    state = {"status": "running", "rss_budget_gib": 4, "concurrency": 1, "phases": {},
             "replay": "not-run", "assumed_unverified": [], "publication": publication_result(None)}
    env = dict(os.environ)

    def save():
        state["wall_seconds"] = round(time.monotonic() - started, 3)
        write(directory / "run.json", state)

    def step(command, label, *, build=False, design_limit_gb=None, budget_gb=4, phase_path=None):
        print("CENSUS_STEP " + label, flush=True)
        census_seconds = sum(value["wall_seconds"] for value in state["phases"].values()
                             if value["rss_budget_gib"] is not None)
        result = run(command, directory / "logs", label, cwd=repository, env=env,
                     budget_gb=None if build else budget_gb, design_limit_gb=design_limit_gb,
                     wall_limit_s=max(1, 1200 - census_seconds), phase_path=phase_path)
        state["phases"][label] = result
        if build:
            log = (directory / "logs" / (label + ".log")).read_text()
            state["phases"][label]["built"] = len(re.findall(r"^.*\[\d+/\d+\] Built ", log, re.M))
        save()
        return result

    def io_phase(phase, label):
        return step([sys.executable, str(repository / "tools/lean-inspector/Census/phases.py"),
                     phase, str(repository), str(directory)], label)

    def lean(program, arguments, label, design_limit_gb=None):
        return step([lean_binary, "-DmaxRecDepth=100000", "-DmaxHeartbeats=0", "--run",
                     str(repository / "tools/lean-inspector/Census" / program), *map(str, arguments)],
                    label, design_limit_gb=design_limit_gb)

    try:
        if options.fixture_truth_export:
            validate_fixture_export(read(options.fixture_truth_export))
        step(["make", "lean-cache-ensure"], "cache_ensure", build=True)
        freshness(lambda command, label: step(command, label, build=True))
        # Resolve Lake's search paths once; time the Lean census process itself.
        env = json.loads(subprocess.check_output(["lake", "env", sys.executable, "-c",
            "import os,json;print(json.dumps(dict(os.environ)))"], cwd=repository, env=env))
        lean_binary = shutil.which("lean", path=env["PATH"])
        env["LEAN_NUM_THREADS"] = "1"
        env["LEAN_SRC_PATH"] = str(repository / "tools/lean-inspector") + os.pathsep + str(repository)
        if options.fixture_truth_export:
            report_path = pathlib.Path(options.fixture_truth_export).resolve()
            raw_report = pathlib.Path(options.lean_report).resolve()
        else:
            step(["git", "diff", "--exit-code", "HEAD", "--", "D5", "lean-toolchain",
                  "lake-manifest.json", "lakefile.toml", "Golden/Frozen/state", "tools/lean-inspector"], "pinned_inputs")
            raw_report = pathlib.Path(options.lean_report).resolve()
            verifier = str(repository / "tools/scripts/report/lean-report-input.sh")
            def verify_report(label):
                step(["bash", verifier, "verify", "--repository", str(repository),
                      "--report", str(raw_report)], label, build=True)
            regenerated = False
            try:
                verify_report("report_provenance")
            except RuntimeError:
                # Only the canonical producer may repair missing/stale input
                # attestations. Verify its result before truth-export consumes it.
                step(["make", "lean-report"], "report_regeneration", build=True)
                raw_report = repository / ".lake/build/stratalint/raw-lean-report.json"
                verify_report("report_provenance_regenerated")
                regenerated = True
            state["report_provenance"] = {"verified": True, "regenerated": regenerated,
                                          "report": str(raw_report)}
            step(["make", "truth-export", f"OUT={directory / 'truth'}", f"LEAN_REPORT={raw_report}"],
                 "truth_export", build=True)
            report_path = exported_path((directory / "logs/truth_export.log").read_text())
        report, all_keys, report_modules = read_inventory(report_path)
        head = report["source_commit"]
        if not options.fixture_truth_export and head != subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=repository, text=True).strip():
            raise ValueError("IE-C044 export revision differs from environment HEAD")
        keys = [key for key in all_keys if key[0] == options.prefix or key[0].startswith(options.prefix + ".")]
        if not keys:
            raise ValueError("no frozen theorem keys selected")
        with report_path.open("rb") as source:
            report_hash = hashlib.sha256()
            for block in iter(lambda: source.read(1024 * 1024), b""):
                report_hash.update(block)
            report_digest = "sha256:" + report_hash.hexdigest()
        request = {"head": head, "keys": keys, "report": str(report_path),
                   "report_sha256": report_digest}
        write(directory / "request.json", request)
        step([sys.executable, str(repository / "tools/lean-inspector/Census/phases.py"),
              "native", str(repository), str(directory)], "native_build", build=True)
        runtime = read(directory / "runtime.json")
        io_phase("enumerate", "tracked_domain")
        domain = read(directory / "domain.json")
        if options.fixture_truth_export:
            modules = report_modules
        else:
            modules = [m for m in domain if m == options.prefix or m.startswith(options.prefix + ".")]
        roots, assignment = root_definitions(modules, keys, [])
        write(directory / "membership-request.json", {"keys": keys, "roots": roots, "assignment": assignment,
              "discovery_roots": sorted(set(modules) | {"LeanInformationAudit.Census.Command"})})
        step([sys.executable, str(repository / "tools/lean-inspector/Census/extraction.py"),
              str(repository), str(directory), runtime["scan.lean"]], "streaming_index", budget_gb=1)
        io_phase("graph", "upstream_graph")
        step([sys.executable, str(repository / "tools/lean-inspector/Census/membership_cache.py"),
              str(repository), str(directory), runtime["membership.lean"]],
             "closure_membership", budget_gb=0.5)
        membership = read(directory / "membership.json")
        from validation import prepare as prepare_validation, run_batches
        plan = prepare_validation(repository, directory, membership, request)
        candidates, validation = run_batches(repository, directory, membership, request, plan, step, lean_binary)
        with (directory / "accounting-input.jsonl").open("wb") as out:
            with (directory / "membership.json.rows.jsonl").open("rb") as observations:
                shutil.copyfileobj(observations, out, 1024 * 1024)
            for row in candidates["entries"]:
                out.write(canonical(row))
        write(directory / "projection-input.json", {"head": head,
              "rows_file": str(directory / "accounting-input.jsonl")})
        lean("project.lean", [directory / "projection-input.json", directory / "projection.json"], "row_accounting")
        io_phase("sort", "row_sort")
        projection = read(directory / "projection.json")
        io_phase("hash", "receipt_hashing")
        sources = {canonical(source): source for source in candidates["source_inputs"]}
        write(directory / "emission.json", {"head_sha": head, "report_sha256": request["report_sha256"],
            "source_inputs": [sources[key] for key in sorted(sources)], "theorem_count": len(all_keys),
            "requested_keys": len(all_keys), "input_kind": "synthetic_fixture" if options.fixture_truth_export else "production",
            "query_verification": "lean_streaming_query"})
        io_phase("emit", "json_emission")
        summary = read(directory / "census.json.summary.json")
        validate_summary(summary, requested=len(all_keys), accounted=len(keys))
        state.update(status=summary["status"], requested_keys=len(all_keys), counts=projection["counts"],
                     candidate_keys=len(membership["candidate_keys"]), tracked_modules=len(domain),
                     artifact_bytes=(directory / "census.json").stat().st_size,
                     extraction_cache=read(directory / "extraction.json"),
                     membership_cache=read(directory / "membership-cache.json"),
                     emission_cache=read(directory / "emission-cache.json"),
                     validation_cache={k: validation[k] for k in ["hits", "misses", "revalidated_keys"]},
                     batches={"bound": validation["receipt"]["bound"],
                              "key_bound": validation["receipt"]["key_bound"],
                              "count": len(validation["receipt"]["batches"]),
                              "executed": len(validation["executions"])},
                     collisions={"total": len(membership["collisions"]),
                         "resolved_by_statement": sum(c["resolved_by_statement"] for c in membership["collisions"]),
                         "remaining": sum(not c["resolved_by_statement"] for c in membership["collisions"])})
        state["census_phases_wall_s"] = round(sum(v["wall_seconds"] for v in state["phases"].values()
                                                 if v["rss_budget_gib"] is not None), 3)
        if options.replay_of:
            expected = pathlib.Path(options.replay_of).resolve()
            # Re-enumeration, content hashing and membership always run. Cached
            # extraction/validation reuse is itself bound by the fresh receipt.
            state["replay"] = replay(lambda: {"receipt": read(directory / "receipt.json"),
                "projection": projection}, {"receipt": read(expected / "receipt.json"),
                "projection": read(expected / "projection.json")})
            with (directory / "census.json").open("rb") as actual, (expected / "census.json").open("rb") as prior:
                while True:
                    block = actual.read(4 * 1024 * 1024)
                    if block != prior.read(4 * 1024 * 1024):
                        raise ValueError("IE-C044 replay JSON bytes differ")
                    if not block:
                        break
            state["byte_identical"] = True
        if not options.no_structure:
            from Structure.sidecar import run_sidecar
            # Only completed census bytes are inputs. Structural failures have
            # their own closed diagnostics and never change accounting status.
            os.environ.update(env)
            state["structure"] = run_sidecar(repository, directory, raw_report)
        if not getattr(options, "no_publication", False):
            census = directory / "census.json"
            census_before_publication = file_stamp(census)
            step([sys.executable, str(repository / "tools/lean-inspector/Census/Certificate/manifest.py"),
                  "--directory", str(directory), "--report", str(report_path), "--prepare",
                  "--rows", str(directory / "rows.jsonl"), "--receipt", str(directory / "receipt.json"),
                  "--prefix", options.prefix], "certificate_manifest")
            step([lean_binary, "-DmaxRecDepth=100000", "-DmaxHeartbeats=0",
                  str(directory / "CensusPublish/Root.lean")], "certificate_publication",
                 phase_path=directory / "publication.json.phase")
            if file_stamp(census) != census_before_publication:
                raise ValueError("certificate publication changed census.json")
            state["publication"] = dict(publication_result(directory / "publication.json"),
                accounted=len(keys), census_json_unchanged_by_publication=True)
        print(json.dumps({"status": state["status"], "counts": state["counts"], "replay": state["replay"]}), flush=True)
        return 0 if state["status"] == "complete" else 2
    except BaseException as error:
        state.update(status="rejected", error=str(error))
        raise
    finally:
        save()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, help="new run-local directory")
    parser.add_argument("--lean-report", default=".lake/build/stratalint/raw-lean-report.json")
    parser.add_argument("--fixture-truth-export", help="synthetic fixture input; production revisions reject")
    parser.add_argument("--prefix", default="D5", help="explicit partial measurement scope")
    parser.add_argument("--replay-of", help="rerun every phase and compare canonical outputs to this prior run")
    parser.add_argument("--no-structure", action="store_true", help="omit the report-only structural sidecar")
    parser.add_argument("--no-publication", action="store_true", help="omit the certificate publication")
    return execute(parser.parse_args())


if __name__ == "__main__":
    sys.exit(main())
