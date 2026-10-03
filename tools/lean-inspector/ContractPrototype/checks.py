"""Contract prototype negative probes. Requires macOS, Python 3, make and the pinned toolchain.

The caller supplies the repository and output directory and prepares PATH/DOTNET_ROOT.
All Lean invocations use make. Mutated source bytes are restored before returning.
"""
import argparse
import json
import hashlib
import shutil
import sys
import pathlib
import re
import subprocess
import os
import select
import time
from contextlib import closing


def wait_for_lean_builds(root=None):
    """Serialize Lake writers in this worktree before starting a Lean build."""
    deadline = time.monotonic() + 7200
    while True:
        processes = subprocess.check_output(["ps", "-axo", "pid=,comm="], text=True)
        pids = [int(pid) for line in processes.splitlines()
                for pid, command in [line.strip().split(None, 1)]
                if pathlib.Path(command).name == "lake"]
        if root is not None:
            local = []
            for pid in pids:
                reading = subprocess.run(["lsof", "-a", "-p", str(pid), "-d", "cwd", "-Fn"],
                    text=True, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
                directories = [pathlib.Path(line[1:]).resolve() for line in reading.stdout.splitlines()
                    if line.startswith("n")]
                if any(path == root or root in path.parents for path in directories):
                    local.append(pid)
            pids = local
        if not pids:
            return
        print("waiting for existing Lean builds: " + ",".join(map(str, pids)), flush=True)
        with closing(select.kqueue()) as queue:
            pending = set()
            for pid in pids:
                try:
                    queue.control([select.kevent(pid, filter=select.KQ_FILTER_PROC,
                        flags=select.KQ_EV_ADD | select.KQ_EV_ONESHOT,
                        fflags=select.KQ_NOTE_EXIT)], 0, 0)
                    pending.add(pid)
                except ProcessLookupError:
                    pass
            while pending:
                if time.monotonic() >= deadline:
                    raise RuntimeError("existing Lean builds did not exit within the infrastructure wait budget")
                for event in queue.control(None, len(pending), 30):
                    pending.discard(event.ident)


def free_bytes():
    reading = subprocess.check_output(["vm_stat"], text=True)
    page = int(re.search(r"page size of (\d+) bytes", reading)[1])
    pages = int(re.search(r"Pages free:\s+(\d+)", reading)[1])
    return page * pages


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True, type=pathlib.Path)
    parser.add_argument("--out", required=True, type=pathlib.Path)
    parser.add_argument("--unit", choices=["rollback", "negatives", "mapping", "isolated", "repair", "current", "unresolved", "opaque", "arena", "imports", "validated-opaque", "implementation"], required=True)
    parser.add_argument("--baseline", action="store_true", help="expect opaque or compiler implementation regressions to fail without the corresponding reader")
    parser.add_argument("--reference", type=pathlib.Path)
    args = parser.parse_args()
    if sys.platform != "darwin":
        parser.error("these probes require macOS vm_stat")
    if args.baseline and args.unit not in ("opaque", "validated-opaque", "implementation"):
        parser.error("--baseline requires opaque, validated-opaque or implementation")
    for tool in ("make", "vm_stat"):
        if shutil.which(tool) is None:
            parser.error("missing required tool: " + tool)
    root, out = args.root.resolve(), args.out.resolve()
    if not (root / "Makefile").is_file():
        parser.error("root must be a repository with Makefile")
    out.mkdir(parents=True, exist_ok=True)
    results = []

    def build(label, module, expected_exit, diagnostic=None, env=None):
        wait_for_lean_builds(root)
        memory = free_bytes()
        while memory < 8 * 1024**3:
            print(f"waiting for 8 GiB free memory: {memory}", flush=True)
            time.sleep(30)
            wait_for_lean_builds(root)
            memory = free_bytes()
        command = ["make", "lean", "LEAN_TARGETS=" + module]
        run_command = ["/usr/bin/time", "-l", *command] if args.unit == "isolated" else command
        path = out / (label + ".log")
        with path.open("w") as log:
            result = subprocess.run(run_command, cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT)
        text = path.read_text()
        matched = result.returncode == expected_exit and (
            diagnostic is None or re.search(diagnostic, text) is not None
        )
        compile_errors = sum(
            bool(re.search(r"error: .*\.lean:\d+:\d+:", line)) and "[FAIL]" not in line
            for line in text.splitlines()
        )
        failures = re.findall(r"\[FAIL\] ([^\n]+)", text)
        results.append({
            "name": label, "command": command, "exit_code": result.returncode,
            "expected_exit": expected_exit, "diagnostic_pattern": diagnostic,
            "diagnostic_matched": matched, "free_bytes_before": memory, "log": str(path),
            "compile_errors": compile_errors, "named_failures": failures,
        })
        if args.unit == "isolated":
            peak = re.search(r"(\d+)\s+maximum resident set size", text)
            if peak is None:
                raise RuntimeError("independent probe RSS reading missing")
            results[-1]["measurement_command"] = run_command
            results[-1]["peak_rss_bytes"] = int(peak[1])
        expected_named = {
            "rollback-ordinary-catch": ["runtime_replay_restores_all_state:root"],
            "field-default": [
                "contract_field_default:LeanInformationAudit.Contract.Registration.options"
            ],
        }.get(label)
        if expected_named is not None and (compile_errors != 0 or failures != expected_named):
            raise RuntimeError(f"invalid named mutation failure: {label}; see {path}")
        if not matched:
            raise RuntimeError(f"unmatched negative or control: {label}; see {path}")

    try:
        if args.unit == "validated-opaque":
            probe = "LeanInformationAuditRegTests.ContractValidatedOpaqueProbe"
            build("validated-opaque-control", probe, 0)
            for side, fixture in (
                ("old", root / "tools/lean-inspector/ContractPrototypeFixtures/ValidatedOpaqueOld.lean"),
                ("new", root / "tools/lean-inspector/ContractPrototypeFixtures/ValidatedOpaqueNew.lean"),
            ):
                original = fixture.read_bytes()
                marker = ("namespace Reg.ContractPrototype.Inputs.ValidatedOpaque" + side.title()).encode()
                head, tail = original.split(marker, 1)
                changed = head + marker + tail.replace(b"hiddenBit : Bool := false", b"hiddenBit : Bool := true", 1)
                if changed == original:
                    raise RuntimeError("validated opaque input did not change")
                expected = ["comparator_rejects_validated_opaque_" + side]
                prediction = {"mutation_location": str(fixture.relative_to(root)),
                    "expected_red_tests": expected, "expected_compile_errors": 0}
                (out / ("validated-opaque-" + side + "-prediction.json")).write_text(
                    json.dumps(prediction, indent=2) + "\n")
                try:
                    fixture.write_bytes(changed)
                    environment = os.environ | {"STRATALINT_CONTRACT_VALIDATED_OPAQUE_MUTATION": side}
                    build("validated-opaque-" + side, probe, 2 if args.baseline else 0,
                        r"\[FAIL\] " + expected[0] if args.baseline else
                        r"\[PASS\] " + expected[0], environment)
                    if results[-1]["compile_errors"] or results[-1]["named_failures"] != (
                        expected if args.baseline else []):
                        raise RuntimeError("unexpected validated opaque result")
                finally:
                    fixture.write_bytes(original)
                if fixture.read_bytes() != original:
                    raise RuntimeError("validated opaque restoration failed")
                results[-1]["restored_source_sha256"] = hashlib.sha256(original).hexdigest()
                build("validated-opaque-" + side + "-restored", probe, 0)
        elif args.unit == "implementation":
            probe = "LeanInformationAuditRegTests.ContractImplementationProbe"
            labels = ["Implemented", "Partial", "Extern", "OpaqueImplemented", "EqPartial", "SymbolExtern"]
            validated = ["ValidatedImplemented", "ValidatedPartial", "ValidatedExtern"]
            build("implementation-control", probe, 0)
            for side in ("old", "new"):
                changes = {}
                for label in labels:
                    path = root / ("Reg/ContractPrototype/Controls" if side == "old" else "Reg/ContractPrototype") / (label + ".lean")
                    original = path.read_bytes()
                    before, after = {
                        "Implemented": (b"hiddenImpl (_ : Nat) : Bool := false", b"hiddenImpl (_ : Nat) : Bool := true"),
                        "OpaqueImplemented": (b"runtimeBit (_ : Unit) : Bool := false", b"runtimeBit (_ : Unit) : Bool := true"),
                        "Partial": (b"then false else hiddenBit", b"then true else hiddenBit"),
                        "EqPartial": (b"then false else hiddenBit", b"then true else hiddenBit"),
                        "Extern": (b"((uint8_t)0)", b"((uint8_t)1)"),
                        "SymbolExtern": (b"lean_nat_dec_eq", b"lean_nat_dec_lt"),
                    }[label]
                    changed = original.replace(before, after)
                    if changed == original:
                        raise RuntimeError("implementation input not changed: " + label)
                    changes[path] = (original, changed)
                for label in validated:
                    path = root / "tools/lean-inspector/ContractPrototypeFixtures" / (label + side.title() + ".lean")
                    original = path.read_bytes()
                    before, after = {
                        "ValidatedImplemented": (b"hiddenImpl (_ : Nat) : Bool := false", b"hiddenImpl (_ : Nat) : Bool := true"),
                        "ValidatedPartial": (b"then false else hiddenBit", b"then true else hiddenBit"),
                        "ValidatedExtern": (b"((uint8_t)0)", b"((uint8_t)1)"),
                    }[label]
                    changed = original.replace(before, after)
                    if changed == original:
                        raise RuntimeError("validated implementation input not changed: " + label)
                    changes[path] = (original, changed)
                expected = ["comparator_rejects_implementation_" + label + "_" + state + "_" + side
                    for label in labels + validated
                    for state in (["validated"] if label in validated else ["unresolved", "undeclared"])]
                (out / ("implementation-" + side + "-prediction.json")).write_text(json.dumps({
                    "mutation_locations": [str(path.relative_to(root)) for path in changes],
                    "expected_red_tests": expected, "expected_compile_errors": 0}, indent=2) + "\n")
                try:
                    for path, (_, changed) in changes.items():
                        path.write_bytes(changed)
                    build("implementation-" + side, probe, 2 if args.baseline else 0,
                        r"\[FAIL\] " + expected[0] if args.baseline else r"\[PASS\] " + expected[0],
                        os.environ | {"STRATALINT_CONTRACT_IMPLEMENTATION_MUTATION": side})
                    row = results[-1]
                    if row["compile_errors"] or sorted(row["named_failures"]) != sorted(expected if args.baseline else []):
                        raise RuntimeError("implementation named outcomes differ from prediction")
                    if not args.baseline:
                        implementation = root / "tools/lean-inspector/LeanInformationAudit/ContractPrototype/Implementation.lean"
                        body = implementation.read_bytes()
                        text = body.decode()
                        start = text.index("    MetaM ImplementationIdentity := do")
                        end = text.index("\ndef renameImplementation", start)
                        disabled = text[:start] + "    MetaM ImplementationIdentity := do\n  return {}\n" + text[end:]
                        (out / ("implementation-reader-" + side + "-prediction.json")).write_text(json.dumps({
                            "mutation_location": str(implementation.relative_to(root)),
                            "expected_red_tests": expected, "expected_compile_errors": 0}, indent=2) + "\n")
                        try:
                            implementation.write_text(disabled)
                            build("implementation-reader-" + side, probe, 2,
                                r"\[FAIL\] " + expected[0],
                                os.environ | {"STRATALINT_CONTRACT_IMPLEMENTATION_MUTATION": side})
                            row = results[-1]
                            if row["compile_errors"] or sorted(row["named_failures"]) != sorted(expected):
                                raise RuntimeError("implementation reader mutant outcomes differ from prediction")
                        finally:
                            implementation.write_bytes(body)
                        if implementation.read_bytes() != body:
                            raise RuntimeError("implementation reader restoration failed")
                        results[-1]["restored_reader_sha256"] = hashlib.sha256(body).hexdigest()
                        build("implementation-reader-" + side + "-restored", probe, 0,
                            env=os.environ | {"STRATALINT_CONTRACT_IMPLEMENTATION_MUTATION": side})
                finally:
                    for path, (original, _) in changes.items():
                        path.write_bytes(original)
                if any(path.read_bytes() != original for path, (original, _) in changes.items()):
                    raise RuntimeError("implementation source restoration failed")
                results[-1]["restored_source_sha256"] = {
                    str(path.relative_to(root)): hashlib.sha256(original).hexdigest()
                    for path, (original, _) in changes.items()}
                build("implementation-" + side + "-restored", probe, 0)
            if not args.baseline:
                metadata_probe = "LeanInformationAuditRegTests.ContractImplementationMetadataProbe"
                build("implementation-metadata-control", metadata_probe, 0)
                implementation = root / "tools/lean-inspector/LeanInformationAudit/ContractPrototype/Implementation.lean"
                original = implementation.read_bytes()
                text = original.decode()
                start = text.index("    MetaM ImplementationIdentity := do")
                end = text.index("\ndef renameImplementation", start)
                expected = ["comparator_rejects_implementation_metadata_" + label for label in (
                    "implemented_by_target", "implemented_by_presence_old", "implemented_by_presence_new",
                    "extern_symbol", "extern_presence_old", "extern_presence_new", "extern_inline", "tagged_return",
                    "csimp_presence_old", "csimp_presence_new", "init_presence_old", "init_presence_new",
                    "builtin_init_presence_old", "builtin_init_presence_new")]
                expected += ["comparator_rejects_implementation_shape_" + label for label in (
                    "extern_adhoc", "extern_opaque", "extern_empty", "extern_backend", "missing_target", "init_anonymous", "unsafe_rec", "cpass")]
                (out / "implementation-metadata-prediction.json").write_text(json.dumps({
                    "mutation_location": str(implementation.relative_to(root)),
                    "expected_red_tests": expected, "expected_compile_errors": 0}, indent=2) + "\n")
                try:
                    disabled = text[:start] + "    MetaM ImplementationIdentity := do\n  return {}\n" + text[end:]
                    guard_start = disabled.index("def verifyCompilerPasses")
                    guard_end = disabled.index("/-- Lean", guard_start)
                    disabled = disabled[:guard_start] + "def verifyCompilerPasses (_env : Environment) : MetaM (Array Name) := pure #[]\n\n" + disabled[guard_end:]
                    implementation.write_text(disabled)
                    build("implementation-metadata-disabled", metadata_probe, 2, r"\[FAIL\] " + expected[0])
                    if results[-1]["compile_errors"] or sorted(results[-1]["named_failures"]) != sorted(expected):
                        raise RuntimeError("metadata mutant outcomes differ from prediction")
                finally:
                    implementation.write_bytes(original)
                if implementation.read_bytes() != original:
                    raise RuntimeError("metadata reader restoration failed")
                results[-1]["restored_source_sha256"] = hashlib.sha256(original).hexdigest()
                build("implementation-metadata-restored", metadata_probe, 0)
        elif args.unit in ("repair", "current", "unresolved", "opaque", "arena", "imports"):
            package = root / "tools/lean-inspector/LeanInformationAudit/ContractPrototype"
            mapping = package / "NameMapping.lean"
            equivalence = package / "Equivalence.lean"
            unresolved = package / "UnresolvedEquivalence.lean"
            inline = root / "Reg/ContractPrototype/Inline.lean"
            witness = root / "Reg/ContractPrototype/ValidWitness.lean"
            mapping_probe = "LeanInformationAuditRegTests.ContractMappingProbe"
            semantic_probe = "LeanInformationAuditRegTests.ContractSemanticProbe"

            def mutation(label, path, transform, module, expected, mode=None):
                original = path.read_bytes()
                changed = transform(original.decode())
                if changed == original.decode():
                    raise RuntimeError("mutation did not change source: " + label)
                prediction = {
                    "mutation_location": str(path.relative_to(root)),
                    "expected_red_tests": expected, "expected_compile_errors": 0,
                }
                (out / (label + "-prediction.json")).write_text(json.dumps(prediction, indent=2) + "\n")
                environment = os.environ | (
                    {"STRATALINT_CONTRACT_OPAQUE_MUTATION": mode.removeprefix("opaque:")}
                    if mode and mode.startswith("opaque:") else
                    {"STRATALINT_CONTRACT_IMPORT_MUTATION": "forbidden"}
                    if mode == "imports" else
                    {"STRATALINT_CONTRACT_SEMANTIC_MUTATION": mode} if mode else {})
                try:
                    path.write_text(changed)
                    build(label, module, 2, r"\[FAIL\] " + re.escape(expected[0]), environment)
                    row = results[-1]
                    if row["compile_errors"] != 0 or sorted(row["named_failures"]) != sorted(expected):
                        raise RuntimeError("unexpected repair mutation outcome: " + label)
                    row["mutation_location"] = prediction["mutation_location"]
                    row["expected_red_tests"] = expected
                finally:
                    path.write_bytes(original)
                if path.read_bytes() != original:
                    raise RuntimeError("source restoration failed: " + label)
                row["restored_source_sha256"] = hashlib.sha256(original).hexdigest()
                build(label + "-restored", module, 0, env=environment)
                row["restored_exit_code"] = results[-1]["exit_code"]

            def input_negative(label, path, transform, mode, failure, guard, weaken):
                original = path.read_bytes()
                changed = transform(original.decode())
                if changed == original.decode():
                    raise RuntimeError("input mutation did not change source: " + label)
                environment = os.environ | {"STRATALINT_CONTRACT_SEMANTIC_MUTATION": mode}
                try:
                    path.write_text(changed)
                    build(label, semantic_probe, 0, r"\[PASS\] " + re.escape(failure), environment)
                    mutation(label + "-guard", guard, weaken, semantic_probe, [failure], mode)
                finally:
                    path.write_bytes(original)
                if path.read_bytes() != original:
                    raise RuntimeError("input restoration failed: " + label)
                build(label + "-source-restored", semantic_probe, 0)

            def without_current_record(s):
                start = s.index("def verifyCurrentRecord")
                end = s.index("/-- Recompute both sides", start)
                return s[:start] + (
                    "def verifyCurrentRecord (_side : String) (_env : Environment) "
                    "(_record : BindingRecord) : MetaM Unit := pure ()\n\n"
                ) + s[end:]

            if args.unit == "arena":
                arena_probe = "LeanInformationAuditRegTests.ContractArenaProbe"
                build("validated-arena-control", arena_probe, 0)
                mutation("validated-arena", equivalence,
                         lambda s: s.replace(
                             '  unless (renameExpr mapping oldRecord.occurrence.arena).equal newRecord.occurrence.arena do\n'
                             '    throwError "contract.equivalence:arena_mapping"\n', ''),
                         arena_probe, ["comparator_rejects_validated_arena_old",
                                       "comparator_rejects_validated_arena_new"])
            elif args.unit == "imports":
                dependency_probe = "LeanInformationAuditRegTests.ContractUnresolvedDependencyProbe"
                probe = root / "tools/lean-inspector/LeanInformationAuditRegTests/ContractUnresolvedDependencyProbe.lean"
                fixture = root / "Reg/ContractPrototype/UnresolvedChanged.lean"
                build("candidate-import-control", dependency_probe, 0)
                original = fixture.read_bytes()
                environment = os.environ | {"STRATALINT_CONTRACT_IMPORT_MUTATION": "forbidden"}
                try:
                    fixture.write_bytes(b"import LeanInformationAuditInterface.Syntax\n" + original)
                    build("candidate-forbidden-import", dependency_probe, 0,
                          r"\[PASS\] comparator_rejects_unresolved_changed_candidate_import_closure", environment)
                    mutation("candidate-import-guard", probe,
                             lambda s: s.replace(
                                 '  unless forbidden.isEmpty do throwError "candidate_forbidden_import:{forbidden}"',
                                 '  unless true do throwError "candidate_forbidden_import:{forbidden}"'),
                             dependency_probe, ["comparator_rejects_unresolved_changed_candidate_import_closure"], "imports")
                finally:
                    fixture.write_bytes(original)
                if fixture.read_bytes() != original:
                    raise RuntimeError("import input restoration failed")
                build("candidate-import-source-restored", dependency_probe, 0)
            elif args.unit == "opaque":
                opaque_probe = "LeanInformationAuditRegTests.ContractOpaqueProbe"
                build("opaque-equal-control", opaque_probe, 0)
                for side, fixture in (
                    ("old", root / "Reg/ContractPrototype/Controls/Opaque.lean"),
                    ("new", root / "Reg/ContractPrototype/Opaque.lean"),
                ):
                    original = fixture.read_bytes()
                    expected = ["comparator_rejects_opaque_" + state + "_" + side
                                for state in ("unresolved", "undeclared")]
                    prediction = {"mutation_location": str(fixture.relative_to(root)),
                                  "expected_red_tests": expected, "expected_compile_errors": 0}
                    (out / ("opaque-" + side + "-prediction.json")).write_text(
                        json.dumps(prediction, indent=2) + "\n")
                    environment = os.environ | {"STRATALINT_CONTRACT_OPAQUE_MUTATION": side}
                    try:
                        changed = original.decode().replace(
                            "private opaque hiddenBit : Bool := false",
                            "private opaque hiddenBit : Bool := true")
                        if changed == original.decode():
                            raise RuntimeError("opaque input mutation did not change source")
                        fixture.write_text(changed)
                        build("opaque-" + side, opaque_probe, 2 if args.baseline else 0,
                              r"\[FAIL\] " + re.escape(expected[0]) if args.baseline
                              else r"\[PASS\] " + re.escape(expected[0]), environment)
                        if args.baseline:
                            if results[-1]["compile_errors"] != 0 or sorted(results[-1]["named_failures"]) != sorted(expected):
                                raise RuntimeError("invalid opaque baseline red")
                        else:
                            mutation("opaque-body-" + side, root / "tools/lean-inspector/LeanInformationAudit/Registry/Repository.lean",
                                     lambda s: s.replace("info.value? (allowOpaque := true)", "info.value?"),
                                     opaque_probe, expected, "opaque:" + side)
                    finally:
                        fixture.write_bytes(original)
                    if fixture.read_bytes() != original:
                        raise RuntimeError("opaque input restoration failed")
                    build("opaque-" + side + "-source-restored", opaque_probe, 0)
                if not args.baseline:
                    environment = os.environ | {"STRATALINT_CONTRACT_OPAQUE_MUTATION": "walk"}
                    # The mode is an elaboration-time input, so invalidate only
                    # the probe's source trace before the equal-body walk check.
                    probe = root / "tools/lean-inspector/LeanInformationAuditRegTests/ContractOpaqueProbe.lean"
                    original = probe.read_bytes()
                    try:
                        probe.write_bytes(original + b"\n")
                        build("opaque-traversal-control", opaque_probe, 0,
                              r"\[PASS\] opaque_repository_body_traversal_old", environment)
                        mutation("opaque-traversal", root / "tools/lean-inspector/LeanInformationAudit/Registry/Repository.lean",
                                 lambda s: s.replace("info.value? (allowOpaque := true)", "info.value?"),
                                 opaque_probe, ["opaque_repository_body_traversal_old",
                                                "opaque_repository_body_traversal_new"], "opaque:walk")
                    finally:
                        probe.write_bytes(original)
                    build("opaque-traversal-source-restored", opaque_probe, 0)
            elif args.unit == "current":
                current_probe = "LeanInformationAuditRegTests.ContractCurrentRecordProbe"
                expected = ["comparator_rejects_" + label for label in (
                    "unresolved_current_descriptor", "unresolved_source_identity",
                    "unresolved_current_claim_removed", "unresolved_current_escape",
                    "undeclared_current_claim",
                )]
                build("current-record-control", current_probe, 0)
                mutation("current-record-binding", equivalence, without_current_record,
                         current_probe, expected)
            elif args.unit == "unresolved":
                dependency_probe = "LeanInformationAuditRegTests.ContractUnresolvedDependencyProbe"
                build("unresolved-dependency-control", dependency_probe, 0)
                mutation("unresolved-actual-dependencies", unresolved,
                         lambda s: s.replace(
                             '  verifyActualDependencies "unresolved" oldEnv newEnv mapping\n'
                             '    oldRecord.occurrence newRecord.occurrence false #[descriptor] #[newDescriptor]\n',
                             ''),
                         dependency_probe, ["comparator_rejects_unresolved_actual_dependencies"])
            else:
                build("repair-control", mapping_probe, 0)
                mutation("stale-descriptor", equivalence,
                         lambda s: s.replace('  check s!"descriptor.{side}" (← identity source record.occurrence.levelParams descriptor)\n    certificate.descriptorIdentity\n', '').replace('  unless descriptorsEqual do throwError "contract.equivalence:{side}.current_descriptor"', '  unless true do throwError "contract.equivalence:{side}.current_descriptor"').replace(
                             '  verifyActualDependencies "validated" oldEnv newEnv mapping\n'
                             '    oldRecord.occurrence newRecord.occurrence source #[descriptor] #[newDescriptor]\n'
                             '    (oldPlan.dependencies ++ oldCert.argumentInputs ++ oldCert.extractionInputs |>.map (·.name))\n'
                             '    (newPlan.dependencies ++ newCert.argumentInputs ++ newCert.extractionInputs |>.map (·.name))\n', ''),
                         mapping_probe, ["comparator_rejects_stale_target_descriptor"])
                mutation("environment-claim", equivalence,
                         lambda s: without_current_record(s),
                         mapping_probe, ["comparator_rejects_stale_environment_claim"])
                mutation("unauthorized-append", mapping,
                         lambda s: s.replace('  validateInjection mapping\n  let key := oldRecord.occurrence.key',
                                             '  mapping := mapping.push (`Nat, `Nat)\n  validateInjection mapping\n  let key := oldRecord.occurrence.key'),
                         mapping_probe, ["comparator_rejects_unauthorized_mapping"])
                mutation("duplicate-key", mapping,
                         lambda s: s.replace('      if seen.contains record.occurrence.key then throwError "contract.pairing:duplicate_key"', '      if false then throwError "contract.pairing:duplicate_key"')
                                    .replace('  unless consumed.size == newRecords.size do throwError "contract.pairing:unconsumed_record"', '  unless true do throwError "contract.pairing:unconsumed_record"'),
                         mapping_probe, ["comparator_rejects_duplicate_occurrence_key", "comparator_rejects_unconsumed_occurrence"])
                mutation("missing-key", mapping,
                         lambda s: s.replace('      | throwError "contract.pairing:missing_key:{key.theoremName}/{key.catalog}"', '      | continue'),
                         mapping_probe, ["comparator_rejects_missing_occurrence_key"])
                mutation("unconsumed", mapping,
                         lambda s: s.replace('  unless consumed.size == newRecords.size do throwError "contract.pairing:unconsumed_record"', '  unless true do throwError "contract.pairing:unconsumed_record"'),
                         mapping_probe, ["comparator_rejects_unconsumed_occurrence"])
                mutation("theorem-only-pair", mapping,
                         lambda s: s.replace('newRecords.find? (·.occurrence.key == key)', 'newRecords.find? (·.occurrence.key.theoremName == key.theoremName)'),
                         mapping_probe, ["comparator_pairs_same_theorem_multiple_catalogs"])
                mutation("theorem-only-input", mapping,
                         lambda s: s.replace('owner == key.registrationModule && inputKey input.entry == key',
                                             'owner == key.registrationModule && input.entry.theoremName == key.theoremName'),
                         mapping_probe, ["comparator_rejects_missing_input_key",
                                         "comparator_pairs_same_theorem_multiple_catalogs"])
                mutation("duplicate-input", mapping,
                         lambda s: s.replace('  unless candidates.size == 1 do', '  unless !candidates.isEmpty do'),
                         mapping_probe, ["comparator_rejects_duplicate_input_key"])
                mutation("support-collision", mapping,
                         lambda s: s.replace('unless earlier == name do throwError "contract.mapping:constant_collision:{earlier}/{name}"', 'unless true do throwError "contract.mapping:constant_collision:{earlier}/{name}"'),
                         mapping_probe, ["comparator_rejects_prefix_unmigrated_collision"])
                # Both negative inputs are ordinary, kernel-checked contract source changes.
                input_negative("generated-bridge-input", inline,
                         lambda s: s.replace('theorem bridge :', 'theorem renamedBridge :')
                                    .replace('Inline.bridge, bridge', 'Inline.renamedBridge, renamedBridge'),
                         "bridge", "comparator_rejects_generated_bridge_rename", mapping,
                         lambda s: s.replace('    let predicted := (authorization.generatedBridges.find? (·.1 == oldRealization)).map Prod.snd\n      |>.getD (predictedCompanionName oldEnv mapping entry primitiveRealizationSuffix)',
                                             '    let predicted := newInput.entry.realizationName'))
                input_negative("undeclared-input", witness,
                         lambda s: s.replace('def thirdDeclaration',
                             'def changedReads := counterexampleRealization (fun i : Fin 2 => decide (i = 1))\n'
                             'theorem changedBridge : WitnessPrimitiveRealization arena (¬ claim) changedReads := ⟨fun _ => third⟩\n'
                             'theorem changedLaw : arena.Law changedReads := ⟨(0 : Fin 2), rfl⟩\n'
                             'theorem changedVariation : arena.Law changedReads ∧ ¬ arena.Law arena.constantTrue := arena.variation changedLaw\n'
                             'theorem changedSensitivity : LeanInformationAudit.FiniteSlotSensitivity arena.toPrimitiveLawArena := arena.sensitivity changedLaw\n\ndef thirdDeclaration')
                           .replace('def thirdDeclaration : Registration third\n    WitnessArena WitnessArena (PrimitiveRealization arena.signature)\n    (arena.Law reads',
                             'def thirdDeclaration : Registration third\n    WitnessArena WitnessArena (PrimitiveRealization arena.signature)\n    (arena.Law changedReads')
                           .replace('realization := .witness arena reads reads.toPrimitiveBundle\n    ⟨`Reg.ContractPrototype.Fixtures.Witness.thirdBridge, thirdBridge⟩ law',
                             'realization := .witness arena changedReads changedReads.toPrimitiveBundle\n'
                             '    ⟨`Reg.ContractPrototype.ValidWitness.changedBridge, changedBridge⟩ changedLaw')
                           .replace('  readout := none\n  variation := some ⟨`Reg.ContractPrototype.Fixtures.Witness.variation, variation⟩\n  sensitivity := some ⟨`Reg.ContractPrototype.Fixtures.Witness.sensitivity, sensitivity⟩',
                             '  readout := none\n  variation := some ⟨`Reg.ContractPrototype.ValidWitness.changedVariation, changedVariation⟩\n'
                             '  sensitivity := some ⟨`Reg.ContractPrototype.ValidWitness.changedSensitivity, changedSensitivity⟩'),
                         "undeclared", "comparator_rejects_undeclared_primitive_change", equivalence,
                         lambda s: s[:s.index('  let source := oldRecord.escape.bridgeKind == "source-equivalence"')] +
                             s[s.index('  let occurrence := oldRecord.occurrence', s.index('def verifyMissingRecord')):])
                mutation("unresolved-form", unresolved,
                         lambda s: s[:s.index('def requireSupportedDiagnostic')] +
                             'def requireSupportedDiagnostic (_diagnostic : String) : MetaM Unit := pure ()\n\n' +
                             s[s.index('/-- Verify the named-site'):],
                         semantic_probe, ["comparator_rejects_unsupported_unresolved_form"])
        elif args.unit == "rollback":
            replay = root / "tools/lean-inspector/LeanInformationAudit/ContractPrototype/Replay.lean"
            original = replay.read_bytes()
            text = original.decode()
            mutated = text.replace("tryCatchRuntimeEx (do", "try").replace(
                "  ) fun error => do", "  catch error =>"
            )
            if mutated == text or "tryCatchRuntimeEx (do" in mutated:
                raise RuntimeError("rollback mutation did not replace the boundary")
            (out / "rollback-prediction.json").write_text(json.dumps({
                "mutation": "replace tryCatchRuntimeEx with ordinary try/catch",
                "expected_failures": ["runtime_replay_restores_all_state:root"],
                "expected_compile_errors": 0,
            }, indent=2) + "\n")
            try:
                replay.write_text(mutated)
                build("rollback-ordinary-catch", "LeanInformationAuditRegTests.ContractPrototypeRollback",
                      2, r"\[FAIL\] runtime_replay_restores_all_state:root")
            finally:
                replay.write_bytes(original)
            if replay.read_bytes() != original:
                raise RuntimeError("replay source was not restored")
            results[-1]["restored_source_sha256"] = hashlib.sha256(original).hexdigest()
            build("rollback-restored", "LeanInformationAuditRegTests.ContractPrototypeRollback", 0,
                  r"\[PASS\] runtime_replay_restores_all_state:seal followup_matches_clean=true")
        elif args.unit == "mapping":
            comparator = root / "tools/lean-inspector/LeanInformationAudit/ContractPrototype/Equivalence.lean"
            original = comparator.read_bytes()
            text = original.decode()
            start = text.index("def verifyRecord")
            body = text.index(": MetaM Json := do", start)
            end = text.index("/-- Missing readout evidence", body)
            mutated = text[:body] + ": MetaM Json := do\n  return Json.null\n\n" + text[end:]
            expected = [
                "comparator_rejects_stale_target_descriptor", "comparator_rejects_stale_environment_claim",
                "comparator_rejects_unauthorized_mapping",
                "comparator_rejects_same_type_readout", "comparator_rejects_same_type_primitive",
                "comparator_rejects_same_type_template_selection", "comparator_rejects_unauthorized_owner",
            ]
            (out / "mapping-prediction.json").write_text(json.dumps({
                "mutation": "replace verifyRecord body with a successful null result",
                "expected_failures": expected, "expected_compile_errors": 0,
            }, indent=2) + "\n")
            try:
                comparator.write_text(mutated)
                build("mapping-accept-all", "LeanInformationAuditRegTests.ContractMappingProbe", 2,
                      r"\[FAIL\] comparator_rejects_same_type_readout")
                if results[-1]["compile_errors"] != 0 or sorted(results[-1]["named_failures"]) != sorted(expected):
                    raise RuntimeError("mapping mutation did not produce precisely the predicted failures")
            finally:
                comparator.write_bytes(original)
            if comparator.read_bytes() != original:
                raise RuntimeError("comparator source was not restored")
            results[-1]["restored_source_sha256"] = hashlib.sha256(original).hexdigest()
            build("mapping-restored", "LeanInformationAuditRegTests.ContractMappingProbe", 0)
        elif args.unit == "isolated":
            if args.reference is None or not args.reference.is_file():
                raise RuntimeError("isolated probes require a completed batch reference")
            reference = args.reference.resolve()
            targets = [row["target"] for row in json.loads(reference.read_text())["rows"]]
            if not targets or len(set(targets)) != len(targets):
                raise RuntimeError("reference targets must be nonempty and unique")
            probe = root / "tools/lean-inspector/LeanInformationAuditRegTests/ContractIsolatedProbe.lean"
            if probe.exists():
                raise RuntimeError("independent probe fixture already exists")
            try:
                for index, target in enumerate(targets):
                    if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", target) is None:
                        raise RuntimeError("invalid reference module name")
                    label = f"independent-{index:02d}"
                    output = out / (label + ".json")
                    output.unlink(missing_ok=True)
                    probe.write_text(
                        "import LeanInformationAuditRegTests.ContractIndependent\nimport " + target +
                        "\n\nrun_cmd LeanInformationAuditRegTests.ContractIndependent.verify `" + target + "\n"
                    )
                    environment = os.environ | {
                        "STRATALINT_CONTRACT_PROTOTYPE_REFERENCE": str(reference),
                        "STRATALINT_CONTRACT_PROTOTYPE_OUTPUT": str(output),
                    }
                    build(label, "LeanInformationAuditRegTests.ContractIsolatedProbe", 0,
                          r"\[PASS\] contract_independent_environment:" + re.escape(target), environment)
                    reading = json.loads(output.read_text())
                    if reading["target"] != target or not all(reading[field] for field in (
                        "only_target_import_closure", "only_target_and_fixed_judge_report_closure",
                        "binding_generated_seal_equal",
                    )):
                        raise RuntimeError("independent reading mismatch")
                    results[-1]["reading"] = reading
            finally:
                probe.unlink(missing_ok=True)
        else:
            contract = root / "tools/lean-inspector-interface/LeanInformationAuditInterface/Contract/Registration.lean"
            negative = root / "Reg/ContractPrototype/Negative.lean"
            if negative.exists():
                raise RuntimeError("negative fixture already exists")
            original = contract.read_bytes()
            (out / "defaults-prediction.json").write_text(json.dumps({
                "mutation": "add a default to Contract.Registration.options",
                "expected_failures": [
                    "contract_field_default:LeanInformationAudit.Contract.Registration.options"
                ],
                "expected_compile_errors": 0,
            }, indent=2) + "\n")
            inline = (root / "Reg/ContractPrototype/Inline.lean").read_text()
            bad = inline.replace("Reg.ContractPrototype.Inline", "Reg.ContractPrototype.Negative")
            bad = bad.replace("⟨`Reg.ContractPrototype.Negative.bridge, bridge⟩", "⟨`True.intro, True.intro⟩")
            if "⟨`True.intro, True.intro⟩" not in bad:
                raise RuntimeError("bridge mutation did not change input")
            line = next(i for i, s in enumerate(bad.splitlines(), 1) if "⟨`True.intro, True.intro⟩" in s)
            try:
                negative.write_text(bad)
                build("wrong-bridge", "Reg.ContractPrototype.Negative", 2,
                      rf"Negative\.lean:{line}:\d+: Application type mismatch:")
                log = (out / "wrong-bridge.log").read_text()
                if "True.intro" not in log or "LegacyPrimitiveRealization" not in log:
                    raise RuntimeError("bridge diagnostic lacks concrete expected/actual types")
                negative.unlink()
                mandatory = original.decode().replace("  options : Options", "  options : Options\n  abiTag : Nat")
                contract.write_text(mandatory)
                build("mandatory-field", "Reg.ContractPrototype.Inline", 2,
                      r"Inline\.lean:\d+:\d+: Fields missing: `abiTag`")
                defaulted = original.decode().replace("  options : Options", "  options : Options := {}")
                contract.write_text(defaulted)
                build("field-default", "LeanInformationAuditRegTests.ContractDefaults", 2,
                      r"contract_field_default:LeanInformationAudit\.Contract\.Registration\.options")
            finally:
                contract.write_bytes(original)
                negative.unlink(missing_ok=True)
            if contract.read_bytes() != original:
                raise RuntimeError("contract source was not restored")
            results[-1]["restored_source_sha256"] = hashlib.sha256(original).hexdigest()
            build("defaults-restored", "LeanInformationAuditRegTests.ContractDefaults", 0,
                  r"\[PASS\] contract_no_field_defaults structures=\d+ fields=\d+")
            build("inline-restored", "Reg.ContractPrototype.Inline", 0)
    finally:
        (out / (args.unit + ".json")).write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
