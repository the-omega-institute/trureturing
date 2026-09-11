"""Report-only structural sidecar. This module never writes census.json."""

import argparse
import hashlib
import json
import pathlib
import sys
import time

from incremental import atomic_json
from phases import read, write
from streaming import canonical, digest, file_stamp
from Structure.sources import file_digest, fingerprint
from Structure.store import wire_key
from Structure.writing import jsonl_elements, object_prefix


def core_policy():
    path = pathlib.Path(__file__).with_name("core-logic.json")
    return read(path), file_digest(path)


def encoded_name(name):
    result = "n0"
    for part in name.split("."):
        result = "ns(" + result + "," + str(len(part.encode())) + ":" + part + ")"
    return result


def axiom_readings(repository, path, keys):
    """Reuse only full-key per-declaration report closures with source binding.

    Unlike value-only structural seeds, these closures cover type + value. A
    missing or unbound closure is a missing field, never an empty axiom set.
    """
    from report_stream import fields
    repository = pathlib.Path(repository).resolve()
    wanted = set(tuple(k) for k in keys)
    result, seen = {}, set()
    if not path.is_file():
        return result
    for field, module in fields(path, array_field="modules"):
        if field != "modules":
            continue
        source = (repository / module["source_path"]).resolve()
        if not source.is_relative_to(repository) or not source.is_file():
            continue
        if file_digest(source) != module["source_sha256"]:
            continue
        for declaration in module["declarations"]:
            key = (module["module"], declaration["name_key"], declaration["statement_id"])
            if key not in wanted or declaration["kind"] != "theorem":
                continue
            pair = key[1:]
            if pair in seen:
                result.pop(pair, None)
            else:
                seen.add(pair)
                if isinstance(declaration.get("axioms"), list):
                    result[pair] = sorted(set(declaration["axioms"]))
    return result


def header(directory, inputs):
    request = read(directory / "request.json")
    core, hashed = core_policy()
    return {"schema": "census-structure", "head_sha": request["head"],
            "report_sha256": request["report_sha256"], "census_sha256": file_digest(directory / "census.json"),
            "source_inputs": dict(inputs, core_set_fingerprint=hashed),
            "generated_policy": "in_denominator", "generated_candidate_policy": "substring .congr_simp only",
            "core_policy": {"constants": core, "sha256": hashed},
            "semantics": {"edges": "consumer_to_prerequisite",
                "direct": "proof_value_getUsedConstants",
                "folded": "first_frozen_hit_all_repository_declarations_stop_upstream_or_axiom",
                "axiom_closure": "existing_report_type_and_value_closure",
                "core_or_frozen_support": "U(value) subset of core union direct_frozen_prerequisites; no semantic classification",
                "information": "undetermined", "escape": "undetermined"}}


def publish(directory, fields, rows):
    path = directory / "census-structure.json"
    temporary = path.with_suffix(".json.tmp")
    with temporary.open("wb") as out, pathlib.Path(rows).open("rb") as source:
        object_prefix(out, fields)
        out.write(b',"rows":[\n')
        jsonl_elements(source, out, b",\n")
        out.write(b"\n]}\n")
    temporary.replace(path)


def report_only(directory, operation):
    """Absorb structural extraction failure after authoritative census emission."""
    directory = pathlib.Path(directory)
    try:
        return operation()
    except Exception as error:
        request = read(directory / "request.json")
        reason = str(error) if str(error) in {
            "missing_olean_part", "constant_missing", "kind_mismatch", "value_unavailable",
            "dependency_unresolved", "frozen_key_ambiguous", "graph_cycle"} else "dependency_unresolved"
        rows = directory / "structure-unavailable.jsonl"
        with rows.open("wb") as out:
            for key in sorted(request["keys"]):
                out.write(canonical(dict(wire_key(key), owning_module=key[0],
                                         status="unavailable", reason=reason, readings=None,
                                         information="undetermined", escape="undetermined")))
        inputs = {"olean_part_manifest_sha256": digest(read(directory / "olean-hashes.json")),
                  "reader_fingerprint": fingerprint(pathlib.Path(__file__).resolve().parents[4]),
                  "ownership_fingerprint": None}
        publish(directory, header(directory, inputs), rows)
        receipt = {"status": "unavailable", "error": str(error), "rows": len(request["keys"]),
                   "status_counts": {"complete": 0, "partial": 0, "unavailable": len(request["keys"])},
                   "unavailable_reasons": {reason: len(request["keys"])}}
        atomic_json(directory / "structure-summary.json", receipt)
        return receipt


def produce(repository, directory, raw_report):
    from resources import run
    from Structure.graph import analyse
    from Structure.sources import synchronize
    from Structure.store import Store
    cache = repository / ".lake/build/census/structure"
    cache.mkdir(parents=True, exist_ok=True)
    store = Store(cache / "summaries.sqlite")
    phases = {}

    def mark(label):
        (directory / "structure-phase.txt").write_text(label)

    def measure(command, label):
        mark(label)
        phases[label] = run(command, directory / "logs", label, cwd=repository, budget_gb=3,
                            wall_limit_s=1800)

    try:
        mark("structure_sources")
        inputs, stats, timings = synchronize(repository, directory, cache, store, measure, mark)
        atomic_json(directory / "structure-sources.json", {"source_inputs": inputs, "cache": stats, "timings_s": timings})
        started = time.monotonic()
        mark("structure_axioms")
        keys = read(directory / "request.json")["keys"]
        before = file_stamp(raw_report) if raw_report.is_file() else None
        axioms = axiom_readings(repository, raw_report, keys)
        inputs["axiom_report_sha256"] = file_digest(raw_report) if raw_report.is_file() else None
        if before is not None and file_stamp(raw_report) != before:
            raise ValueError("dependency_unresolved")
        timings["axiom_report_join"] = time.monotonic() - started
        core, _ = core_policy()
        mark("structure_projection")
        rows = directory / "structure-rows.jsonl"
        summary = analyse(store, keys, rows, [encoded_name(n) for n in core],
                          cache=cache / "projection", axioms=axioms, mark=mark)
        inputs["projection_fingerprint"] = summary["projection_key"]
        started = time.monotonic()
        mark("structure_publication")
        publish(directory, header(directory, inputs), rows)
        timings["binding_and_publication"] = time.monotonic() - started
        summary["timings_s"].update(timings)
        summary.update(status="reported", source_inputs=inputs, raw_cache=stats, phases=phases,
                       artifact_bytes=(directory / "census-structure.json").stat().st_size)
        atomic_json(directory / "structure-summary.json", summary)
        return summary
    finally:
        store.close()


def run_sidecar(repository, directory, raw_report):
    from resources import run

    def operation():
        run([sys.executable, "-m", "Structure.sidecar", str(repository.resolve()),
             str(directory.resolve()), str(raw_report.resolve())],
            directory / "logs", "structure", cwd=pathlib.Path(__file__).resolve().parents[1],
            budget_gb=3, wall_limit_s=1800,
            phase_path=directory / "structure-phase.txt")
        return read(directory / "structure-summary.json")
    try:
        return report_only(directory, operation)
    except Exception as error:
        # Even an unwritable sidecar destination cannot reject an already
        # emitted census. The run receipt retains the publication failure.
        return {"status": "unavailable", "publication_error": str(error)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ["repository", "directory", "raw_report"]:
        parser.add_argument(name, type=pathlib.Path)
    options = parser.parse_args()
    report_only(options.directory.resolve(), lambda: produce(
        options.repository.resolve(), options.directory.resolve(), options.raw_report.resolve()))
