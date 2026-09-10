"""Preregister the four review mutations, then record their complete six-tuples."""

import argparse
import hashlib
import json
import pathlib
import sys


if __package__ in (None, ""):
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from resources import run


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=pathlib.Path)
    options = parser.parse_args()
    root = pathlib.Path(__file__).resolve().parent
    cases = [
        ("handoff-ignores-row-digest", "handoff.py", "test_whole_stream_publication_entrypoint",
         "wholeStreamRowsBinding",
         '    if (rows_sha != receipt["rows_sha256"] or\n'
         '            inputs.get("rows") != {"artifact": "rows.jsonl", "sha256": rows_sha} or\n'
         '            inputs["expanded_rows_cache_key"] !=\n'
         '            digest([rows_sha, inputs["module_names"], inputs["scopes"], emitter])):\n'
         '        raise ValueError("IE-C044 whole_stream_rows_binding")\n', ''),
        ("emitter-codec-before-duplicates", "emission.py",
         "test_inventory_duplicate_before_malformed_report_entrypoint", "inventoryDuplicateBeforeEmitterCodec",
         '    seen = set()\n    for _, _, wire in report_keys:',
         '    for _, _, wire in report_keys:\n        statement_nat(wire)\n'
         '    seen = set()\n    for _, _, wire in report_keys:'),
        ("whole-path-uses-compiler-phase", "certificate_benchmark.py",
         "test_whole_path_budget_uses_outer_measurement", "wholePathIncludesValidationDriver",
         'result["wall_seconds"]', 'build["wall_s"]'),
        ("range-ignores-leaf-bound", "emission.py", "test_adaptive_leaf_bound", "adaptiveLeafBound",
         'depth < b or max(len(inv), len(rep)) > max_leaf_ids', 'depth < b'),
        ("handoff-opens-expanded", "handoff.py", "test_publication_reads_compact_rows",
         "publicationReadsCompactRows",
         '    keys = []', '    pathlib.Path(rows_path).with_name("census.json").read_bytes()\n    keys = []'),
        ("handoff-decodes-line-twice", "handoff.py", "test_compact_rows_linear_decoding",
         "compactRowsLinearDecoding",
         '                row = json.loads(line)',
         '                json.loads(line)\n                row = json.loads(line)'),
    ]
    outcomes = []
    for label, filename, method, expected, old, new in cases:
        source = root / filename
        original = source.read_bytes()
        assert old in original.decode(), label
        mutated = original.decode().replace(old, new).encode()
        if filename == "certificate_benchmark.py":
            mutated = mutated.replace(b'result["peak_rss_bytes"]', b'build["max_process_peak_rss_bytes"]')
        logs = options.output / label
        logs.mkdir(parents=True, exist_ok=False)
        record = {"mutation": label, "location": str(source), "expected_named_red": [expected],
                  "expected_red_count": 1, "expected_written_before_running": True,
                  "pristine_sha256": hashlib.sha256(original).hexdigest(),
                  "mutant_sha256": hashlib.sha256(mutated).hexdigest()}
        (logs / "preregistration.json").write_text(json.dumps(record, indent=2) + "\n")
        command = [sys.executable, "-m", "unittest", "-v", "tests.test_review_fixes.ReviewFixTests." + method]
        run(command, logs, "baseline", cwd=root.parent)
        record["baseline_exit_code"] = 0
        try:
            source.write_bytes(mutated)
            run([sys.executable, "-m", "py_compile", str(source)], logs, "compile", cwd=root.parent)
            record["compile_errors"] = 0
            try:
                run(command, logs, "test", cwd=root.parent)
            except RuntimeError:
                log = (logs / "test.log").read_text()
                assert expected in log and "FAILED (failures=1)" in log, log
                record.update(named_red=[expected], actual_red_count=1,
                    test_exit_code=json.loads((logs / "test.resources.json").read_text())["exit_code"])
            else:
                raise AssertionError(label + " survived")
        finally:
            source.write_bytes(original)
            record["restored_byte_identical"] = source.read_bytes() == original
            # Avoid same-second bytecode reuse after restoring equal-size source edits.
            for cached in (root / "__pycache__").glob(source.stem + ".*.pyc"):
                cached.unlink()
            (logs / "result.json").write_text(json.dumps(record, indent=2) + "\n")
        run(command, logs, "restored", cwd=root.parent)
        record["restored_exit_code"] = 0
        (logs / "result.json").write_text(json.dumps(record, indent=2) + "\n")
        outcomes.append(record)
    (options.output / "mutations.json").write_text(json.dumps(outcomes, indent=2) + "\n")


if __name__ == "__main__":
    main()
