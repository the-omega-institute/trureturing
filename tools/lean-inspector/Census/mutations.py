"""Execute preregistered production mutations and retain six-tuple receipts."""

import argparse
import hashlib
import json
import pathlib

from resources import run


def certificate_mutations(options):
    directory = options.output.resolve()
    repository = pathlib.Path(__file__).resolve().parents[3]
    source_root = repository / "tools/lean-inspector"
    manifest = source_root / "LeanInformationAudit/Census/Manifest.lean"
    publisher = source_root / "LeanInformationAudit/Census/Publish.lean"
    report = source_root / "LeanInformationAudit/Census/Report.lean"
    contract = source_root / "LeanInformationAudit/Tests/Census/Manifest/Contract.lean"
    environment = contract.with_name("Environment.lean")
    def omit_conjunct(text, family):
        start = text.index("def certificateSource (")
        end = text.index("\n/--", start)
        original = text[start:end]
        heads = {
            "ascending": ('ids.toString ++ ".length = " ++ toString requested ++ " ∧ " ++ ids.toString ++ " = " ++ reportIds.toString',
                          '"(by\\n  exact (LeanInformationAudit.certificate_of_range " ++ ids.getPrefix.toString ++ ".facts).2)\\n"'),
            "length": ('"LeanInformationAudit.strictlyAscending " ++ ids.toString ++ " = true ∧ " ++ ids.toString ++ " = " ++ reportIds.toString',
                       '"(by\\n  have h := LeanInformationAudit.certificate_of_range " ++ ids.getPrefix.toString ++ ".facts\\n  exact ⟨h.1, h.2.2⟩)\\n"'),
            "equality": ('"LeanInformationAudit.strictlyAscending " ++ ids.toString ++ " = true ∧ " ++ ids.toString ++ ".length = " ++ toString requested',
                         '"(by\\n  have h := LeanInformationAudit.certificate_of_range " ++ ids.getPrefix.toString ++ ".facts\\n  exact ⟨h.1, h.2.1⟩)\\n"'),
        }
        proposition, proof = heads[family]
        signature = original[:original.index(" :=\n")]
        replacement = signature + ' :=\n  input ++ "\\npublic theorem " ++ certificate.toString ++ " : " ++\n    ' + proposition + ' ++ " := " ++\n    ' + proof + '\n'
        return text[:start] + replacement + text[end:]

    def omit_chunk_recomputation(text):
        start = text.index("    unless (.lit (.natVal value) : Expr) == .lit (.natVal packed) do")
        end = text.index("  return keys", start)
        return text[:start] + text[end:]

    cases = [
        ("drop-ascending", publisher, contract, "certificateAscendingConjunct",
         lambda text: omit_conjunct(text, "ascending")),
        ("drop-length", publisher, contract.with_name("Length.lean"), "certificateLengthConjunct",
         lambda text: omit_conjunct(text, "length")),
        ("drop-bucket-equality", publisher, contract.with_name("Buckets.lean"), "bucketEqualityConjunct",
         lambda text: omit_conjunct(text, "equality")),
        ("skip-bucket-range", manifest, contract.with_name("Buckets.lean"), "bucketRangeBinding",
         lambda text: text.replace(
             '    if let some (k, b) := bucket then\n      unless (decodeIds chunk.length value).all (fun id => idPrefix b id == k) do\n        bindingError "bucket_prefix"\n', "")),
        ("skip-chunk-recomputation", manifest, contract.with_name("Chunks.lean"), "chunkLiteralBinding",
         omit_chunk_recomputation),
        ("payload-import", publisher, environment, "finalEnvironmentImports",
         lambda text: text.replace('  let input := input',
             '  let input := "import LeanInformationAudit.DispositionCensus\\n" ++ input')),
        ("report-codec-before-inventory-duplicates", report, contract.with_name("Precedence.lean"),
         "inventoryDuplicateBeforeMalformedReport", lambda text: text.replace(
             "  checkInventoryDuplicates rows\n  checkStatementIds frozen",
             "  checkStatementIds frozen\n  checkInventoryDuplicates rows")),
        ("missing-before-nat-binding", manifest, contract.with_name("Precedence.lean"),
         "manifestNatBeforeMissingRow", lambda text: text.replace(
             "  checkMissingKeys report.headSha report.theorems rows\n", "").replace(
             "  ofExcept <| checkMissingKeys report.headSha report.theorems rows\n", "").replace(
             '  bindKeys "manifest_keys" rows m.keys',
             '  checkMissingKeys report.headSha report.theorems rows\n  bindKeys "manifest_keys" rows m.keys').replace(
             '  let listName := manifestName.appendAfter "Keys"',
             '  ofExcept <| checkMissingKeys report.headSha report.theorems rows\n' +
             '  let listName := manifestName.appendAfter "Keys"')),
    ]
    outcomes = []
    for label, source, fixture, expected, transform in cases:
        original = source.read_bytes()
        mutated = transform(original.decode()).encode()
        assert original != mutated, "mutation did not change production"
        target = repository / ".lake/build/lib/lean" / source.relative_to(source_root).with_suffix(".olean")
        compiled_original = {path: path.read_bytes() for path in target.parent.glob(target.stem + ".*")}
        logs = directory / label
        logs.mkdir(parents=True, exist_ok=False)
        record = {"mutation": label, "location": str(source.relative_to(repository)),
                  "expected_named_red": [expected], "expected_red_count": 1,
                  "pristine_sha256": hashlib.sha256(original).hexdigest(),
                  "mutant_sha256": hashlib.sha256(mutated).hexdigest()}
        record["expected_written_before_running"] = True
        (logs / "preregistration.json").write_text(json.dumps(record, indent=2) + "\n")
        run(["lake", "env", "lean", str(fixture)], logs, "baseline", cwd=repository)
        record["baseline_exit_code"] = 0
        compile_command = ["lake", "env", "lean", "-R", str(source_root), "-o", str(target), str(source)]
        try:
            source.write_bytes(mutated)
            run(compile_command, logs, "compile", cwd=repository)
            record["compile_errors"] = 0
            try:
                run(["lake", "env", "lean", str(fixture)], logs, "test", cwd=repository)
            except RuntimeError:
                log = (logs / "test.log").read_text()
                errors = [line for line in log.splitlines() if ": error:" in line]
                assert len(errors) == 1 and expected in errors[0], log
                record["named_red"] = expected
                record["actual_red_count"] = len(errors)
                record["test_exit_code"] = json.loads((logs / "test.resources.json").read_text())["exit_code"]
            else:
                raise AssertionError(label + " survived")
        finally:
            source.write_bytes(original)
            for path, content in compiled_original.items():
                path.write_bytes(content)
            record["restored_byte_identical"] = source.read_bytes() == original and all(
                path.read_bytes() == content for path, content in compiled_original.items())
            (logs / "result.json").write_text(json.dumps(record, indent=2) + "\n")
        run(["lake", "env", "lean", str(fixture)], logs, "restored", cwd=repository)
        record["restored_exit_code"] = 0
        (logs / "result.json").write_text(json.dumps(record, indent=2) + "\n")
        outcomes.append(record)
    run(["lake", "env", "lean", str(contract)], directory, "restored-contract", cwd=repository)
    run(["lake", "env", "lean", str(environment)], directory, "restored-environment", cwd=repository)
    (directory / "mutations.json").write_text(json.dumps(outcomes, indent=2) + "\n")
    print(json.dumps(outcomes))




# Merged whole-stream query fixtures.
"""Preregistered streaming mutations with compile, named red, and restoration."""

import argparse
import hashlib
import json
import pathlib
import shutil
import sys

from resources import run


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=pathlib.Path)
    parser.add_argument("--fixtures", type=pathlib.Path)
    parser.add_argument("--certificate-only", action="store_true")
    parser.add_argument("--review-only", action="store_true")
    options = parser.parse_args()
    if options.certificate_only:
        return certificate_mutations(options)
    if options.fixtures is None:
        parser.error("--fixtures is required for query mutations")
    directory = options.output.resolve()
    repository = pathlib.Path(__file__).resolve().parents[3]
    source_root = repository / "tools/lean-inspector"
    python_root = source_root / "Census"
    streaming = python_root / "streaming.py"
    ownership = source_root / "LeanInformationAudit/Census/Ownership.lean"
    membership = source_root / "LeanInformationAudit/Census/Membership.lean"
    incremental = python_root / "incremental.py"
    membership_cache = python_root / "membership_cache.py"
    emission_cache = python_root / "emission_cache.py"
    fixture = source_root / "LeanInformationAudit/Tests/Census/Query/Ownership.lean"
    cases = [
        ("skip-freshness", streaming, "streamFreshnessGate",
         '    return step(["make", "lean"], "lake_freshness")', '    return None',
         [sys.executable, str(python_root / "negative_fixtures.py"), "--directory", str(options.fixtures), "--case", "stale_olean"]),
        ("first-import-ownership", ownership, "ownerMembershipPositive",
         '  return moduleContainsTheorem env.header.moduleData[index.toNat]! info',
         '  return env.getModuleIdxFor? declaration == some index',
         ["lake", "env", "lean", str(fixture)]),
        ("drop-scope-filter", membership, "streamOutOfScopeEvidence",
         '      unless scope.contains entry.moduleName do continue',
         '      pure ()',
         [sys.executable, str(python_root / "negative_fixtures.py"), "--directory", str(options.fixtures), "--case", "out_of_scope"]),
        ("ignore-import-graph", streaming, "test_receipt_digest_includes_import_graph",
         'def receipt_digest(inputs):\n    return digest(inputs)',
         'def receipt_digest(inputs):\n    return digest({k: v for k, v in inputs.items() if k != "import_graph"})',
         [sys.executable, "-m", "unittest", "tests.test_streaming.StreamingTests.test_receipt_digest_includes_import_graph"]),
        ("cache-ignores-olean-digest", incremental, "test_stale_extraction_cache_reextracts_changed_olean_only",
         '    addresses = module_digests(hashes)',
         '    addresses = {module: digest(module) for module, _ in manifest}',
         [sys.executable, "-m", "unittest", "tests.test_incremental.IncrementalTests.test_stale_extraction_cache_reextracts_changed_olean_only"]),
        ("ignore-batch-bound", incremental, "test_two_batches_respect_union_closure_bound",
         '            if current_keys and (name_collision or len(modules | scope) > bound or len(current_keys) + len(chunk) > BATCH_KEY_BOUND):',
         '            if current_keys and (name_collision or len(current_keys) + len(chunk) > BATCH_KEY_BOUND):',
         [sys.executable, "-m", "unittest", "tests.test_incremental.IncrementalTests.test_two_batches_respect_union_closure_bound"]),
        ("skip-statement-collision-resolution", membership, "streamStatementCollisionPositive",
         '      let matching := resolveCollision occurrences id',
         '      let matching : Array String := #[]',
         [sys.executable, str(python_root / "negative_fixtures.py"), "--directory", str(options.fixtures), "--case", "statement_collision"]),
        ("membership-cache-ignores-index", membership_cache, "test_membership_cache_requires_exact_index_request_and_native_reader",
         '    address = digest([file_digest(index), file_digest(request), reader])',
         '    address = digest([file_digest(request), reader])',
         [sys.executable, "-m", "unittest", "tests.test_incremental.IncrementalTests.test_membership_cache_requires_exact_index_request_and_native_reader"]),
        ("expanded-cache-ignores-rows", emission_cache, "test_expanded_rows_cache_binds_rows_scopes_and_emitter",
         '    return digest([rows, modules, scopes, emitter])',
         '    return digest([modules, scopes, emitter])',
         [sys.executable, "-m", "unittest", "tests.test_incremental.IncrementalTests.test_expanded_rows_cache_binds_rows_scopes_and_emitter"]),
    ]
    review_cases = [
        ("drop-name-isolation", incremental, "candidateNameIsolation",
         '            name_collision = any(name in current_names and current_names[name] != owner for name in owner_names)',
         '            name_collision = False', "colliding_owners"),
        ("drop-nested-scope", source_root / "LeanInformationAudit/DispositionEvidence.lean", "nestedEvidenceRootScope",
         '  unless ← CensusOwnership.nameInScope (← getEnv) modules name do\n    failClass key className s!"{field}.root_membership"\n',
         '', "nested_scope"),
        ("skip-replay-comparison", streaming, "streamReceiptReplayMismatch",
         '    if canonical(actual) != canonical(expected):\n        raise ValueError("IE-C044 receipt replay mismatch")\n',
         '', "receipt_controls"),
        ("retain-all-named-evidence", python_root / "validation.py", "batchScopedNamedEvidence",
         '        named = [entry for entry in membership["named"] if entry["module"] in batch_scope]',
         '        named = membership["named"]', "named_ballast"),
    ]
    review_labels = {case[0] for case in review_cases}
    review_cases = [(label, source, expected, old, new, [sys.executable,
        str(python_root / "tests/review_fixtures.py"), "--directory",
        str(directory / label / "fixture-inputs"), "--case", case])
        for label, source, expected, old, new, case in review_cases]
    cases = review_cases if options.review_only else cases + review_cases
    outcomes = []
    for label, source, expected, old, new, command in cases:
        original = source.read_bytes()
        assert original.decode().count(old) == 1, "mutation location is not unique"
        mutated = original.decode().replace(old, new).encode()
        target = (repository / ".lake/build/lib/lean" / source.relative_to(source_root).with_suffix(".olean")) if source.suffix == ".lean" else None
        compiled = target.read_bytes() if target else None
        native = repository / ".lake/build/ir" / source.relative_to(source_root).with_suffix(".c") if target else None
        native_bytes = native.read_bytes() if native else None
        logs = directory / label
        logs.mkdir(parents=True, exist_ok=False)
        if label in review_labels:
            inputs = logs / "fixture-inputs"
            inputs.mkdir()
            for name in ["index.jsonl", "manifest.json", "request.json", "external.json", "domain.json",
                         "olean-hashes.json", "inputs.json", "stamps.json"]:
                shutil.copyfile(options.fixtures / name, inputs / name)
        record = {"mutation": label, "location": str(source.relative_to(repository)),
                  "expected_named_red": [expected], "expected_red_count": 1,
                  "pristine_sha256": hashlib.sha256(original).hexdigest(),
                  "mutant_sha256": hashlib.sha256(mutated).hexdigest(),
                  "expected_written_before_running": True}
        (logs / "preregistration.json").write_text(json.dumps(record, indent=2) + "\n")
        try:
            source.write_bytes(mutated)
            compile_command = (["lake", "env", "lean", "-R", str(source_root), "-o", str(target), "-c", str(native), str(source)]
                if target else [sys.executable, "-m", "py_compile", str(source)])
            run(compile_command, logs, "compile", cwd=repository)
            record["compile_errors"] = 0
            try:
                run(command, logs, "test", cwd=python_root if command[1:3] == ["-m", "unittest"] else repository)
            except RuntimeError:
                log = (logs / "test.log").read_text()
                assert expected in log, log
                record["named_red"] = [expected]
                record["test_exit_code"] = json.loads((logs / "test.resources.json").read_text())["exit_code"]
            else:
                raise AssertionError(label + " survived")
        finally:
            source.write_bytes(original)
            if target:
                target.write_bytes(compiled)
                native.write_bytes(native_bytes)
            record["restored_byte_identical"] = source.read_bytes() == original and (not target or
                target.read_bytes() == compiled and native.read_bytes() == native_bytes)
            (logs / "result.json").write_text(json.dumps(record, indent=2) + "\n")
        outcomes.append(record)
    run([sys.executable, "-m", "unittest", "tests.test_streaming", "tests.test_incremental"], directory, "restored-python", cwd=python_root)
    run(["lake", "env", "lean", str(fixture)], directory, "restored-membership", cwd=repository)
    (directory / "mutations.json").write_text(json.dumps(outcomes, indent=2) + "\n")
    print(json.dumps(outcomes), flush=True)


if __name__ == "__main__":
    main()
