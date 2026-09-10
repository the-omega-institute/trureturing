"""Six preregistered J6 faults, each killed by its named contract test."""

import argparse
import hashlib
import json
import pathlib
import py_compile
import subprocess
import sys

from incremental import atomic_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=pathlib.Path)
    options = parser.parse_args()
    folder = options.output.resolve()
    folder.mkdir(parents=True, exist_ok=True)
    root = pathlib.Path(__file__).resolve().parents[1]
    cases = [
        ("folding_skipped", "Structure/store.py", "test_structure.StructureTests",
         "test_panel_direct_folded_depth_and_distinct_descendants",
         [('consume(todo[0], (helper[1] or []) + helper[2], uncertain=bool(todo[2]))', 'pass')]),
        ("failed_extraction_as_empty", "Structure/store.py", "test_structure.StructureTests",
         "test_failed_extraction_is_unavailable_never_empty",
         [('errors.add("value_unavailable")\n                    entry["unbounded"] = True', 'pass')]),
        ("name_only_join", "Structure/store.py", "test_structure.StructureTests",
         "test_collision_uses_full_key_and_import_scope",
         [('candidates = self.signature(context, name)', 'candidates = self.signature(context, name)[:1]')]),
        ("core_namespace_prefix", "Structure/store.py", "test_structure.StructureTests",
         "test_nat_and_core_namespace_are_not_support_whitelists",
         [('if seed and name not in core:', 'if seed and name not in core and parse_name_key(name)[1] not in [parse_name_key(n)[1] for n in core]:')]),
        ("ignore_frozen_membership", "Structure/store.py", "test_structure.StructureTests",
         "test_newly_frozen_helper_invalidates_unchanged_raw_cache",
         [('if prior != current:', 'if [(c[0], c[1], c[4]) for c in prior] != [(c[0], c[1], c[4]) for c in current]:'),
          ('hasher.update(canonical([context, name, current]))', 'hasher.update(canonical([context, name, prior]))')]),
        ("sidecar_suppresses_census", "Structure/sidecar.py", "test_structure_sidecar.StructureSidecarTests",
         "test_sidecar_failure_keeps_census_bytes_and_success",
         [('except Exception as error:\n        request', 'except Exception as error:\n        (directory / "census.json").write_bytes(b"null\\n")\n        request')]),
    ]
    results = []
    for label, filename, suite, test, replacements in cases:
        path = root / filename
        original = path.read_bytes()
        mutated = original.decode()
        for old, new in replacements:
            assert mutated.count(old) == 1, label
            mutated = mutated.replace(old, new)
        record = {"mutation": label, "location": filename,
                  "expected_red_names": [test], "expected_red_count": 1,
                  "expected_written_before_running": True,
                  "pristine_sha256": hashlib.sha256(original).hexdigest(),
                  "mutant_sha256": hashlib.sha256(mutated.encode()).hexdigest()}
        atomic_json(folder / (label + ".preregistered.json"), record)
        command = [sys.executable, "-m", "unittest", "tests." + suite + "." + test]
        try:
            path.write_text(mutated)
            py_compile.compile(str(path), doraise=True)
            record["compile_errors"] = 0
            executed = subprocess.run(command, cwd=root, capture_output=True, text=True)
            log = executed.stdout + executed.stderr
            (folder / (label + ".log")).write_text(log)
            assert executed.returncode != 0 and "FAIL: " + test in log and "failures=1" in log, log
            record.update(actual_red_names=[test], actual_red_count=1, test_exit_code=executed.returncode,
                          command=command)
        finally:
            path.write_bytes(original)
            py_compile.compile(str(path), doraise=True)
            record["restored_byte_identical"] = path.read_bytes() == original
            atomic_json(folder / (label + ".result.json"), record)
        results.append(record)
    subprocess.run([sys.executable, "-m", "unittest", "tests.test_structure", "tests.test_structure_sidecar"],
                   cwd=root, check=True)
    atomic_json(folder / "mutations.json", results)
    print(json.dumps(results))


if __name__ == "__main__":
    main()
