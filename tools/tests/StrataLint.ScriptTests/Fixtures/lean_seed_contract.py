"""Behavior contracts. All transport is a private local fake; no GitHub writes."""
import importlib.util
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest
import zipfile
import shutil
from lean_seed_runtime import FAKE_LAKE, PAIR_PRODUCER

from lean_seed_support import DELTA, INPUT, OTHER, PUBLISH, REV, ROOT, PartitionFixture, digest, write
from lean_seed_transport import FAKE_GH, ReleaseTransportCases


class DeltaTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = pathlib.Path(self.temporary.name)
        self.cache = self.root / "cache"
        self.address = "a" * 64
        self.producer = "b" * 64
        self.config = "c" * 64
        self.entry = self.cache / self.address
        self.report = self.entry / "raw-lean-report.json"
        self.modules = []
        self.materials = {}
        for name, imports in [("A", []), ("B", ["A"]), ("C", ["B"]), ("D", [])]:
            write(self.root / (name + ".lean"), "def value := 1\n")
            self.modules.append({"module": name, "source_path": name + ".lean",
                "source_sha256": "sha256:" + digest((self.root / (name + ".lean")).read_bytes()),
                "imports": imports, "declarations": []})
        self.store()

    def store(self):
        write(self.report, json.dumps({"modules": self.modules, "schema": "stratalint-raw-lean-report-v2"}, sort_keys=True) + "\n")
        report_sha = digest(self.report.read_bytes())
        write(pathlib.Path(str(self.report) + ".sha256"), report_sha + "  raw-lean-report.json\n")
        write(pathlib.Path(str(self.report) + ".input.attestation"), "schema=stratalint-lean-report-input-attestation-v1\nrepository_input_sha256=" + "d"*64 + "\nproducer_sha256=" + self.producer + "\nreport_sha256=" + report_sha + "\n")
        write(pathlib.Path(str(self.report) + ".provenance.json"), json.dumps({
            "schema": "stratalint-lean-report-provenance-v1", "side": "candidate", "mode": "produced",
            "source_side": "candidate", "input_address": "sha256:" + self.address,
            "producer_sha256": self.producer, "repository_inspector_sha256": self.producer,
            "lean_sources_sha256": "e"*64, "lean_config_sha256": self.config, "report_sha256": report_sha}))
        with zipfile.ZipFile(str(self.report) + ".materials.zip", "w") as archive:
            for name, material in sorted(self.materials.items()):
                archive.writestr(name, material)

    def add_declaration_material(self):
        spec = importlib.util.spec_from_file_location("materials", DELTA.with_name("materials.py"))
        materials = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(materials)
        material = b"statement-v1(uparams=[],type=ec(ns(n0,3:Nat),[]),value=ei(ln(1)))"
        declaration = {"axioms": [], "include_in_statement": True, "kind": "def",
            "name": "value", "name_key": "ns(n0,5:value)",
            "type_sha256": materials.statement_address(material),
            "statement_id": materials.statement_address(materials.canonical_json({
                "declaration_name_key": "ns(n0,5:value)", "kind": "def", "module_path": "A.lean",
                "schema": "declaration-statement-v1", "statement_material": material.decode("utf-8")}))}
        self.modules[0]["declarations"] = [declaration]
        self.materials["sha256/" + declaration["type_sha256"][7:]] = material
        self.store()
        return declaration

    def plan(self, producer=None, config=None, extra=()):
        names = sorted(path.stem for path in self.root.glob("*.lean"))
        table = self.root / "modules.tsv"
        write(table, "".join(name + "\t" + name + ".lean\n" for name in names))
        plan = self.root / "plan.json"
        result = subprocess.run([sys.executable, str(DELTA), "plan", str(self.root), str(self.cache),
            self.address, producer or self.producer, producer or self.producer, config or self.config,
            str(table), str(plan), *extra], text=True, capture_output=True)
        self.assertEqual(0, result.returncode, result.stderr)
        return json.loads(plan.read_text())

    def test_exact_seed_enters_incremental_reuse(self):
        result = self.plan()
        self.assertEqual("reuse", result["status"])
        self.assertEqual([], result["recheck"])

    def test_source_changes_close_transitive_reverse_dependencies(self):
        write(self.root / "A.lean", "def value := 2\n")
        self.assertEqual(["A", "B", "C"], self.plan()["recheck"])

    def test_add_remove_preserves_unaffected_modules(self):
        (self.root / "A.lean").unlink()
        write(self.root / "E.lean", "def e := 3\n")
        result = self.plan()
        self.assertEqual(["A"], result["removed"])
        self.assertEqual(["E"], result["added"])
        self.assertEqual(["B", "C", "E"], result["recheck"])

    def test_semantics_change_reinspects_inside_producer(self):
        for result in [self.plan(producer="f"*64), self.plan(config="f"*64)]:
            self.assertEqual("delta", result["status"])
            self.assertEqual(["A", "B", "C", "D"], result["recheck"])
            self.assertTrue(result["semantic_changed"])

    def test_corrupt_materials_are_not_a_reuse_seed(self):
        write(pathlib.Path(str(self.report) + ".materials.zip"), "broken")
        self.assertEqual("fallback", self.plan()["status"])

    def test_nonempty_declaration_material_is_reused(self):
        self.add_declaration_material()
        result = self.plan()
        self.assertEqual("reuse", result["status"])
        self.assertEqual([], result["recheck"])

    def test_damaged_declaration_material_is_not_a_reuse_seed(self):
        declaration = self.add_declaration_material()
        self.materials["sha256/" + declaration["type_sha256"][7:]] += b"damaged"
        self.store()
        self.assertEqual("fallback", self.plan()["status"])

    def test_wrong_declaration_identity_is_not_a_reuse_seed(self):
        declaration = self.add_declaration_material()
        declaration["statement_id"] = "sha256:" + "f" * 64
        self.store()
        self.assertEqual("fallback", self.plan()["status"])

    def test_runtime_invalidation_is_internal_and_partition_mismatch_is_a_miss(self):
        seed = {"schema": "lean-report-seed-v1", "partition": REV + "/linux-x64",
            "runtime_sha256": "1"*64, "report_sha256": digest(self.report.read_bytes()),
            "materials_sha256": digest(pathlib.Path(str(self.report)+".materials.zip").read_bytes())}
        write(pathlib.Path(str(self.report)+".seed.json"), json.dumps(seed))
        options = ["--partition", seed["partition"], "--runtime-sha", "1"*64]
        self.assertEqual("reuse", self.plan(extra=options)["status"])
        options[-1] = "2"*64
        result = self.plan(extra=options)
        self.assertEqual(["A", "B", "C", "D"], result["recheck"])
        self.assertTrue(result["semantic_changed"])
        options[1] = OTHER + "/linux-x64"
        self.assertEqual("fallback", self.plan(extra=options)["status"])

    def test_legacy_logs_are_never_imported_as_production_evidence(self):
        logs = pathlib.Path(str(self.report)+".logs")
        logs.symlink_to(self.root / "absent")
        self.assertEqual("fallback", self.plan()["status"])


class TransportTests(ReleaseTransportCases, unittest.TestCase):
    """Release transport cases exposed under their existing test identity."""

    def test_transition_fetch_flag_cannot_widen_partition_compatibility(self):
        self.assertEqual(0, self.transport("publish").returncode)
        shutil.rmtree(self.root / ".lake/build")
        self.manifest["packages"][0]["rev"] = OTHER
        self.save_manifest()
        missed = self.transport("fetch", arguments=("--allow-seed",))
        self.assertEqual(1, missed.returncode, missed.stdout + missed.stderr)
        self.assertIn('"status":"miss"', missed.stdout)
        self.assertFalse((self.root / ".lake/build").exists())
        self.manifest["packages"][0]["rev"] = REV
        self.save_manifest()
        restored = self.transport("fetch", arguments=("--allow-seed",))
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        self.assertEqual("locally-produced-olean", (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())


    def test_malformed_cleanup_metadata_cannot_fail_or_repeat_the_build(self):
        calls = self.root / "build-calls"
        write(self.bin / "make", '#!/bin/sh\necho build >> "$FAKE_BUILD_CALLS"\nexit 0\n')
        malformed = [("FAKE_API_JSON", "[]"), ("FAKE_LIST_JSON", '["invalid"]'),
                     ("FAKE_LIST_JSON", '[{"tagName":12,"createdAt":"today","isDraft":false}]')]
        for index, (field, value) in enumerate(malformed):
            result = self.transport("publish", str(601 + index), FAKE_BUILD_CALLS=str(calls), **{field: value})
            self.assertEqual(0, result.returncode, result.stdout + result.stderr)
            self.assertIn('"prune_error":', result.stdout)
        self.assertEqual(["build"] * len(malformed), calls.read_text().splitlines())


class PairFixture(PartitionFixture):
    def setUp(self):
        super().setUp()
        self.supervisor = tempfile.TemporaryDirectory(prefix="lean-seed-supervisor-")
        self.addCleanup(self.supervisor.cleanup)
        shutil.copytree(ROOT / "tools/scripts", self.root / "tools/scripts",
                        ignore=shutil.ignore_patterns("bin", "obj", "__pycache__"))
        shutil.copytree(ROOT / "tools/lean-inspector", self.root / "tools/lean-inspector")
        self.producer = self.root / "tools/lean-inspector/inspect.sh"
        write(self.producer, PAIR_PRODUCER)
        self.producer.chmod(0o755)
        # This synthetic producer runs only scripts; real project roots are
        # are not selected merely because the helper project is present.
        registration = json.loads((ROOT / "Meta/ReportProducers/lean-report.json").read_text())
        registration["projects"] = []
        registration["materials"] = []
        write(self.root / "Meta/ReportProducers/lean-report.json", json.dumps(registration))
        write(self.root / "Meta/engineering-projects.json", json.dumps({
            "version": 1, "rule_build_inputs": [], "projects": [{
                "path": "tools/scripts/report/JudgeSeedTask.csproj", "assembly": "JudgeSeedTask",
                "role": "test-support", "ci": False,
                "include": ["tools/scripts/report/JudgeSeedTask.cs"], "exclude": [], "references": [],
                "owner": None, "owned_test_assembly": None, "test_partition": None,
                "root_namespace": "Fixture", "namespace_exclude": [], "global_namespace_exceptions": [],
            }], "historical_projects": []}))
        subprocess.run(["git", "init", "--quiet", str(self.root)], check=True, capture_output=True)
        subprocess.run(["git", "-C", str(self.root), "add", "tools"], check=True, capture_output=True)
        self.cache = self.root / ".lake/report-cache"
        self.output = self.root / "out/raw-lean-report.json"
        self.helper = self.root / "tools/scripts/report/lean-report-input.sh"

    def pair(self, **extra):
        return subprocess.run([str(self.root / "tools/scripts/lean-report-pair.sh"),
            "--producer", str(self.producer), "--lake-bin", "/bin/echo",
            "--candidate-root", str(self.root), "--candidate-output", str(self.output)],
            text=True, capture_output=True, env={**os.environ,
                "STRATALINT_SUPERVISOR_ROOT": self.supervisor.name,
                "STRATALINT_REPORT_CACHE_ROOT": str(self.cache), **extra})

    def report_input(self, command="address"):
        return subprocess.run([str(self.helper), command, "--repository", str(self.root),
            *(["--report", str(self.output)] if command == "verify" else [])], text=True, capture_output=True)

    def runs(self):
        return len((self.root / "producer-runs").read_text().splitlines())

    def seeds(self):
        return list(self.cache.glob("*/*/*/raw-lean-report.json"))

    def stage_report(self, target):
        return subprocess.run(["bash", "-euo", "pipefail", "-c", '''
python3 "$1" stage --report "$2" --output "$3"
"$4" verify --repository "$5" --report "$3"
''', "stage-report", str(self.root / "tools/lean-inspector/report_cache.py"),
            str(self.output), str(target), str(self.helper), str(self.root)],
            text=True, capture_output=True)

    def import_report(self, report, cache):
        return subprocess.run([str(self.root / "tools/scripts/report/lean-report-ci-baseline.sh"),
            "--bundle", str(report), "--cache-root", str(cache)], text=True, capture_output=True)

    def bundle_bytes(self, report):
        values = {suffix: pathlib.Path(str(report) + suffix).read_bytes() for suffix in
                  ("", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip", ".seed.json")}
        logs = pathlib.Path(str(report) + ".logs")
        values.update({".logs/" + path.relative_to(logs).as_posix(): path.read_bytes()
                       for path in logs.rglob("*") if path.is_file()})
        return values

    def write_bundle_bytes(self, report, values):
        for suffix, content in values.items():
            path = pathlib.Path(str(report) + suffix)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)

    def publication_fault(self, boundary="bundle", damage=""):
        hooks = self.root / "publication-hooks"
        write(hooks / "sitecustomize.py", '''
import errno, os, pathlib, shutil
destination = pathlib.Path(os.environ["PUBLICATION_DESTINATION"]).resolve()
boundary = os.environ["PUBLICATION_BOUNDARY"]
def move(original, source, target, *args, **kwargs):
    src, dst = pathlib.Path(source).resolve(), pathlib.Path(target).resolve()
    if dst.is_relative_to(destination):
        if (boundary in ("bundle", "logs") and not src.is_relative_to(destination)
                and (src.name.endswith(".logs") == (boundary == "logs"))):
            raise OSError(errno.EXDEV, "injected cross-device move", str(src))
    return original(source, target, *args, **kwargs)
replace, rename, copyfile = os.replace, os.rename, shutil.copyfile
os.replace = lambda *args, **kwargs: move(replace, *args, **kwargs)
os.rename = lambda *args, **kwargs: move(rename, *args, **kwargs)
# Python 3.9 pathlib captures os.rename before sitecustomize runs.
path_rename = pathlib.Path.rename
pathlib.Path.rename = lambda *args, **kwargs: move(path_rename, *args, **kwargs)
def copy(source, target, *args, **kwargs):
    result = copyfile(source, target, *args, **kwargs)
    path = pathlib.Path(target).resolve()
    if path.is_relative_to(destination):
        with (destination / "copied-members").open("a") as log:
            log.write(path.name + "\\n")
        if os.environ["PUBLICATION_DAMAGE"] and path.name.endswith(os.environ["PUBLICATION_DAMAGE"]):
            path.write_bytes(b"corrupt staging copy")
    return result
shutil.copyfile = copy
''')
        return {"PYTHONPATH": str(hooks), "PUBLICATION_DESTINATION": str(self.output.parent),
                "PUBLICATION_BOUNDARY": boundary, "PUBLICATION_DAMAGE": damage}

class PairTests(PairFixture, unittest.TestCase):
    def test_phase_diagnostics_survive_failed_staging_without_becoming_report_evidence(self):
        diagnostics = self.root / "build/ci/logs/current/lean-inspector"
        write(self.producer, '''#!/bin/bash
set -euo pipefail
output="" logs=""
while [[ $# -gt 0 ]]; do
  case "$1" in --output) output="$2" ;; --log-dir) logs="$2" ;; esac
  shift 2
done
logs="${logs:-$output.logs}"
mkdir -p "$logs"
printf 'lake build\\n' > "$logs/build.command.log"
printf 'raw build output\\n' > "$logs/build.stdout.log"
printf 'raw inspector error\\n' > "$logs/inspect.stderr.log"
printf '19\\n' > "$logs/inspect.exit.log"
exit 19
''')
        result = self.pair(STRATALINT_LEAN_REPORT_LOG_DIR=str(diagnostics),
                           STRATALINT_SUPERVISOR_ROOT=str(self.root / "supervisor-state"))
        self.assertEqual(19, result.returncode, result.stdout + result.stderr)
        self.assertEqual([], list(self.root.glob(".lean-report-bundle.*")))
        self.assertFalse(self.output.exists())
        self.assertFalse(pathlib.Path(str(self.output) + ".provenance.json").exists())
        self.assertEqual([], self.seeds())
        self.assertEqual("lake build\n", (diagnostics / "build.command.log").read_text())
        self.assertEqual("raw build output\n", (diagnostics / "build.stdout.log").read_text())
        self.assertEqual("raw inspector error\n", (diagnostics / "inspect.stderr.log").read_text())
        self.assertEqual("19\n", (diagnostics / "inspect.exit.log").read_text())

    def test_external_diagnostics_allow_successful_validated_publication(self):
        diagnostics = self.root / "build/ci/logs/current/lean-inspector"
        result = self.pair(STRATALINT_LEAN_REPORT_LOG_DIR=str(diagnostics),
                           STRATALINT_SUPERVISOR_ROOT=str(self.root / "supervisor-state"))
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertEqual(0, self.report_input("verify").returncode)
        self.assertEqual("produced\n", (diagnostics / "producer.log").read_text())
        self.assertEqual(b"diagnostic\x00bytes\n", (diagnostics / "subprocess/stderr.log").read_bytes())
        self.assertEqual("produced\n", pathlib.Path(str(self.output) + ".logs/producer.log").read_text())

    def test_exact_hit_always_enters_producer_and_rebinds_candidate(self):
        first = self.pair()
        self.assertEqual(0, first.returncode, first.stdout + first.stderr)
        before = self.output.read_bytes()
        second = self.pair()
        self.assertEqual(0, second.returncode, second.stdout + second.stderr)
        self.assertEqual(2, self.runs())
        self.assertEqual(before, self.output.read_bytes())
        self.assertEqual("produced", json.loads(pathlib.Path(str(self.output) + ".provenance.json").read_text())["mode"])
        self.assertEqual(0, self.report_input("verify").returncode)
        self.assertEqual(1, len(self.seeds()))
        self.assertFalse(pathlib.Path(str(self.seeds()[0]) + ".logs").exists())
        expected = self.bundle_bytes(self.output)
        self.assertEqual(8, len(expected))  # Six members and two nested log files.
        for boundary in ("bundle", "logs"):
            with self.subTest(publication=boundary):
                self.output = self.root / ("runner-temp-" + boundary) / "raw-lean-report.json"
                result = self.pair(**self.publication_fault(boundary))
                self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertEqual(expected, self.bundle_bytes(self.output))
                self.assertEqual(0, self.report_input("verify").returncode)
                copied = (self.output.parent / "copied-members").read_text().splitlines()
                self.assertCountEqual([self.output.name + suffix for suffix in expected if not suffix.startswith(".logs/")]
                                      + ["producer.log", "stderr.log"], copied)
                self.assertEqual([], list(self.output.parent.glob(".lean-report-publish-*")))

    def test_real_producer_failure_cannot_be_masked_by_prior_report(self):
        self.assertEqual(0, self.pair().returncode)
        before = self.output.read_bytes()
        result = self.pair(PAIR_FAIL="19")
        self.assertEqual(19, result.returncode, result.stdout + result.stderr)
        self.assertEqual(2, self.runs())
        self.assertEqual(before, self.output.read_bytes())

    def test_corrupt_seed_and_failed_save_do_not_override_production(self):
        self.assertEqual(0, self.pair().returncode)
        write(self.seeds()[0], "corrupt seed")
        self.assertEqual(0, self.pair().returncode)
        shutil.rmtree(self.cache)
        write(self.cache, "cache storage unavailable")
        result = self.pair()
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertEqual(3, self.runs())
        self.assertEqual(0, self.report_input("verify").returncode)

    def test_invalid_producer_outputs_never_replace_prior_bundle(self):
        self.assertEqual(0, self.pair().returncode)
        before = self.output.read_bytes()
        for damage in ["logs", "materials", "checksum", "report"]:
            with self.subTest(damage=damage):
                result = self.pair(PAIR_DAMAGE=damage)
                self.assertNotEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertEqual(before, self.output.read_bytes())
        before = self.bundle_bytes(self.output)
        write(self.root / "D5/A.lean", "def a := 5\n")
        for damage in (".provenance.json", ".materials.zip"):
            with self.subTest(staging_damage=damage):
                self.write_bundle_bytes(self.output, before)
                result = self.pair(**self.publication_fault(boundary="none", damage=damage))
                self.assertNotEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertEqual(before, self.bundle_bytes(self.output))
                self.assertEqual([], list(self.output.parent.glob(".lean-report-publish-*")))
        prior = self.output
        self.output = self.root / "next/raw-lean-report.json"
        self.assertEqual(0, self.pair().returncode)
        complete = self.bundle_bytes(self.output)
        for index, suffix in enumerate(("", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip", ".seed.json", ".logs")):
            with self.subTest(missing=suffix):
                self.write_bundle_bytes(prior, before)
                incomplete = self.root / f"missing-{index}/raw-lean-report.json"
                self.write_bundle_bytes(incomplete, {key: value for key, value in complete.items()
                    if key != suffix and not (suffix == ".logs" and key.startswith(".logs/"))})
                result = subprocess.run([sys.executable, str(self.root / "tools/lean-inspector/report_cache.py"),
                    "publish", "--report", str(incomplete), "--output", str(prior)], text=True, capture_output=True)
                self.assertNotEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertEqual(before, self.bundle_bytes(prior))

    def test_transport_adapter_preserves_seed_identity_and_omits_logs(self):
        self.output = self.root / "out/candidate-lean-report.json"
        self.assertEqual(0, self.pair().returncode)
        before = {p.name.removeprefix(self.output.name): p.read_bytes()
                  for p in self.output.parent.iterdir() if p.is_file()}
        self.assertEqual(6, len(before))
        staged = self.root / "staged/raw-lean-report.json"
        for unused in range(2):
            result = self.stage_report(staged)
            self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        transported = self.root / "transported/raw-lean-report.json"
        shutil.copytree(staged.parent, transported.parent)
        for suffix, content in before.items():
            self.assertEqual(content, pathlib.Path(str(self.output) + suffix).read_bytes())
            expected = (digest(before[""]) + "  raw-lean-report.json\n").encode() if suffix == ".sha256" else content
            self.assertEqual(expected, pathlib.Path(str(staged) + suffix).read_bytes())
            self.assertEqual(expected, pathlib.Path(str(transported) + suffix).read_bytes())
        target = self.root / "imported"
        result = self.import_report(transported, target)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(str(target), result.stdout.strip())
        imported = list(target.glob("*/*/*/raw-lean-report.json"))
        self.assertEqual(1, len(imported))
        for suffix in before:
            self.assertEqual(pathlib.Path(str(transported)+suffix).read_bytes(),
                             pathlib.Path(str(imported[0])+suffix).read_bytes())
        self.assertFalse(pathlib.Path(str(imported[0])+".logs").exists())
        for suffix in before:
            for damage in ("missing", "corrupt"):
                with self.subTest(suffix=suffix, damage=damage):
                    member = pathlib.Path(str(transported) + suffix)
                    content = member.read_bytes()
                    if damage == "missing": member.unlink()
                    else: member.write_bytes(b"corrupt")
                    missed = self.import_report(transported, self.root / "unusable")
                    self.assertEqual(0, missed.returncode, missed.stderr)
                    self.assertEqual("", missed.stdout)
                    self.assertFalse((self.root / "unusable").exists())
                    member.write_bytes(content)
        write(self.root / "D5/A.lean", "def a := 5\n")
        self.assertEqual(2, self.stage_report(staged).returncode)


class ReportImportTests(unittest.TestCase):
    def test_import_edit_rechecks_dependents_and_updates_reverse_closure(self):
        delta = DeltaTests()
        delta.setUp()
        self.addCleanup(delta.doCleanups)
        source = delta.root / "B.lean"
        write(source, "import D\ndef b := 2\n")
        plan = delta.plan()
        self.assertEqual(["B"], plan["changed"])
        self.assertEqual(["B", "C"], plan["recheck"])
        self.assertFalse(plan["semantic_changed"])
        # Model the inspector's updated import list in the next seed.
        delta.modules[1]["source_sha256"] = "sha256:" + digest(source.read_bytes())
        delta.modules[1]["imports"] = ["D"]
        delta.store()
        write(delta.root / "A.lean", "def value := 2\n")
        self.assertEqual(["A"], delta.plan()["recheck"])
        write(delta.root / "A.lean", "def value := 1\n")
        write(delta.root / "D.lean", "def value := 2\n")
        self.assertEqual(["B", "C", "D"], delta.plan()["recheck"])
        print(json.dumps({"case": "import-edit", "selected": 2, "modules": 4,
            "old_dependency_selected": 1, "new_dependency_selected": 3}), flush=True)


class InspectorTests(PairFixture, unittest.TestCase):
    def setUp(self):
        super().setUp()
        shutil.copyfile(ROOT / "tools/lean-inspector/inspect.sh", self.producer)
        shutil.copyfile(ROOT / "Makefile", self.root / "Makefile")
        write(self.root / "global.json", "{}\n")
        write(self.root / "tools/StrataLint.Lean/StrataLint.Lean.csproj",
            '<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><OutputType>Exe</OutputType>'
            '<TargetFramework>net10.0</TargetFramework></PropertyGroup></Project>\n')
        write(self.root / "tools/StrataLint.Lean/Program.cs", 'System.Console.WriteLine("[]");\n')
        runner = self.root / "tools/scripts/worktree/lean-cache-run.sh"
        write(runner, '#!/bin/sh\nexec "$@"\n')
        runner.chmod(0o755)
        self.lake = self.root / "runtime/bin/lean"
        write(self.lake, FAKE_LAKE)
        self.lake.chmod(0o755)
        self.core = self.root / "runtime/lib/lean/Init.olean"
        write(self.core, "compiled core fixture")
        write(self.core.with_suffix(".ilean"), json.dumps({"directImports": []}))

    def pair(self, **extra):
        return subprocess.run([str(self.root / "tools/scripts/lean-report-pair.sh"),
            "--producer", str(self.producer), "--lake-bin", str(self.lake),
            "--candidate-root", str(self.root), "--candidate-output", str(self.output)],
            text=True, capture_output=True, env={**os.environ,
                "STRATALINT_SUPERVISOR_ROOT": self.supervisor.name,
                "STRATALINT_REPORT_CACHE_ROOT": str(self.cache), **extra})

    def current_report(self):
        self.output = self.root / ".lake/build/stratalint/raw-lean-report.json"
        environment = {**os.environ, "LAKE_BIN": str(self.lake),
                       "STRATALINT_SUPERVISOR_ROOT": self.supervisor.name}
        environment.pop("STRATALINT_REPORT_CACHE_ROOT", None)
        return subprocess.run(["make", "lean-report"], cwd=self.root,
            text=True, capture_output=True, env=environment)

    def test_inspector_runs_lake_on_exact_seed_with_zero_reinspection(self):
        self.output = self.root / "out/candidate-lean-report.json"
        first = self.pair()
        self.assertEqual(0, first.returncode, first.stdout + first.stderr)
        write(self.root / "lakefile.toml", 'name = "renamed"\nkeywords = ["metadata"]\n[leanOptions]\nmaxRecDepth = 1000\n')
        self.manifest["packages"][0]["inputRev"] = "metadata-tag"
        self.save_manifest()
        current = self.current_report()
        self.assertEqual(0, current.returncode, current.stdout + current.stderr)
        self.assertIn("LEAN_REPORT_DELTA mode=reuse changed=0 added=0 removed=0 recheck=0", current.stdout)
        staged = self.root / "staged/raw-lean-report.json"
        stage = self.stage_report(staged)
        self.assertEqual(0, stage.returncode, stage.stdout + stage.stderr)
        transported = self.root / "transported/raw-lean-report.json"
        shutil.copytree(staged.parent, transported.parent)
        imported = self.import_report(transported, self.root / "imported")
        self.assertEqual(0, imported.returncode, imported.stderr)
        self.assertEqual(str(self.root / "imported"), imported.stdout.strip())
        self.cache = pathlib.Path(imported.stdout.strip())
        self.output = self.root / "next/candidate-lean-report.json"
        second = self.pair()
        self.assertEqual(0, second.returncode, second.stdout + second.stderr)
        self.assertIn("LEAN_REPORT_DELTA mode=reuse changed=0 added=0 removed=0 recheck=0", second.stdout)
        write(self.root / "D5/A.lean", "def a := 3\n")
        third = self.pair()
        self.assertEqual(0, third.returncode, third.stdout + third.stderr)
        self.assertIn("LEAN_REPORT_DELTA_PLAN mode=delta changed=1 added=0 removed=0 recheck=1", third.stdout)
        self.assertIn("LEAN_REPORT_DELTA mode=delta changed=1 added=0 removed=0 recheck=1", third.stdout)
        commands = (self.root / "lake-runs").read_text().splitlines()
        self.assertEqual(4, commands.count("build"))
        self.assertEqual(2, sum("--run" in command for command in commands))

    def test_report_staging_does_not_preempt_cold_cache_provisioning(self):
        self.output = self.root / ".lake/build/stratalint/raw-lean-report.json"
        result = self.pair(LAKE_EXPECT_NO_LAKE="1")
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)

    def test_actual_runtime_dependency_change_reinspects_inside_same_partition(self):
        first = self.pair()
        self.assertEqual(0, first.returncode, first.stdout + first.stderr)
        write(self.core, "changed compiled core fixture")
        second = self.pair()
        self.assertEqual(0, second.returncode, second.stdout + second.stderr)
        self.assertIn("LEAN_REPORT_DELTA mode=delta changed=0 added=0 removed=0 recheck=2", second.stdout)

    def test_unknown_runtime_disables_reuse_but_allows_real_full_production(self):
        self.core.with_suffix(".ilean").unlink()
        for unused in range(2):
            result = self.pair()
            self.assertEqual(0, result.returncode, result.stdout + result.stderr)
            self.assertIn("LEAN_REPORT_DELTA mode=full-fallback", result.stdout)
        self.assertEqual([], self.seeds())

    def test_inspector_real_failure_blocks_even_when_report_seed_exists(self):
        self.assertEqual(0, self.pair().returncode)
        before = self.output.read_bytes()
        result = self.pair(LAKE_BUILD_FAIL="19")
        self.assertEqual(19, result.returncode, result.stdout + result.stderr)
        self.assertEqual(before, self.output.read_bytes())
        write(self.root / "D5/A.lean", "def a := 3\n")
        result = self.pair(LAKE_INSPECT_FAIL="23")
        self.assertEqual(23, result.returncode, result.stdout + result.stderr)
        self.assertEqual(before, self.output.read_bytes())


if __name__ == "__main__":
    unittest.main(verbosity=2)
