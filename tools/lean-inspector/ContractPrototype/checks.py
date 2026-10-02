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


def free_bytes():
    reading = subprocess.check_output(["vm_stat"], text=True)
    page = int(re.search(r"page size of (\d+) bytes", reading)[1])
    pages = int(re.search(r"Pages free:\s+(\d+)", reading)[1])
    return page * pages


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True, type=pathlib.Path)
    parser.add_argument("--out", required=True, type=pathlib.Path)
    parser.add_argument("--unit", choices=["rollback", "negatives", "mapping", "isolated", "repair", "current", "unresolved"], required=True)
    parser.add_argument("--reference", type=pathlib.Path)
    args = parser.parse_args()
    if sys.platform != "darwin":
        parser.error("these probes require macOS vm_stat")
    for tool in ("make", "vm_stat"):
        if shutil.which(tool) is None:
            parser.error("missing required tool: " + tool)
    root, out = args.root.resolve(), args.out.resolve()
    if not (root / "Makefile").is_file():
        parser.error("root must be a repository with Makefile")
    out.mkdir(parents=True, exist_ok=True)
    results = []

    def build(label, module, expected_exit, diagnostic=None, env=None):
        memory = free_bytes()
        if memory < 8 * 1024**3:
            raise RuntimeError(f"free memory below 8 GiB: {memory}")
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
        if args.unit in ("repair", "current", "unresolved"):
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
                environment = os.environ | ({"STRATALINT_CONTRACT_SEMANTIC_MUTATION": mode} if mode else {})
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

            if args.unit == "current":
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
                         lambda s: s.replace('  check s!"descriptor.{side}" (← identity source record.occurrence.levelParams descriptor)\n    certificate.descriptorIdentity\n', '').replace('  unless descriptorsEqual do throwError "contract.equivalence:{side}.current_descriptor"', '  unless true do throwError "contract.equivalence:{side}.current_descriptor"'),
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
