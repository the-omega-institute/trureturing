"""Actions report snapshot export, handoff, restore, and layer-isolation contracts."""
import hashlib
import json
import os
import pathlib
import platform
import shutil
import subprocess
import sys
import unittest
from unittest import mock

from ci_contract import CACHE, REPO, REV, CacheFixture


class SnapshotContracts(CacheFixture, unittest.TestCase):
    def prepare_report(self):
        from lean_seed_contract import InspectorTests, FAKE_LAKE
        fixture = InspectorTests("test_inspector_runs_lake_on_exact_seed_with_zero_reinspection")
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        self.root = fixture.root
        fixture.manifest["packages"][0]["rev"] = REV
        fixture.save_manifest()
        fixture.output = self.root / "out/declared-current-report.json"
        # Exercise real compaction/validation with nonempty declaration material.
        fixture.lake.write_text(FAKE_LAKE.replace("output.write_text(", '''
spool = pathlib.Path(args[args.index("--material-spool") + 1])
spool.mkdir(parents=True, exist_ok=True)
for index, row in enumerate(modules):
    name = str(index) + ".statement"
    (spool / name).write_text(row["module"] + ":" + (root / row["source_path"]).read_text())
    row["declarations"] = [{"name": "value", "name_key": "ns(n0,5:value)", "kind": "def",
        "include_in_statement": True, "axioms": [], "material_file": name}]
    row["imports"] = ["D5.A"] if row["module"] == "Trureturing" else []
output.write_text('''))
        self.env.update(HOME=str(self.root), GITHUB_OUTPUT=str(self.root / "outputs"),
                        GITHUB_ENV=str(self.root / "environment"))
        return fixture

    def produce_report(self, fixture):
        result = fixture.pair()
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        # Synthetic current/pack evidence for the export consumer. Fake Lake is
        # the statement producer; this fixture does not claim a real current run.
        (self.root / ".gitignore").write_text("*\n")
        for args in (("init", "-q"), ("add", "-f", ".gitignore", "D5", "Trureturing.lean",
                     "lakefile.toml", "lake-manifest.json", "lean-toolchain"),
                     ("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "candidate")):
            subprocess.run(["git", "-C", str(self.root), *args], check=True, capture_output=True)
        self.env.update(CANDIDATE_SHA=subprocess.check_output(
            ["git", "-C", str(self.root), "rev-parse", "HEAD"], text=True).strip(), GITHUB_REPOSITORY="fixture/trureturing")
        self.write_handoff(fixture)
        return next(seed for seed in fixture.seeds()
                    if fixture.bundle_bytes(seed)[".seed.json"] == fixture.bundle_bytes(fixture.output)[".seed.json"])

    def write_handoff(self, fixture):
        summary = self.root / "build/ci/current-result.json"
        summary.parent.mkdir(parents=True, exist_ok=True)
        candidate, round_id = "e" * 64, "fixture-current-round"
        summary.write_text(json.dumps({"stage": "current", "exit": 0, "candidate": candidate,
            "current_evidence": "build/ci/current.json",
            "report": fixture.output.relative_to(self.root).as_posix()}))
        paths = [str(fixture.output.relative_to(self.root)) + suffix for suffix in
                 ("", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip", ".seed.json")]
        def materials(paths):
            return [{"path": path, "sha256": hashlib.sha256((self.root / path).read_bytes()).hexdigest()}
                    for path in sorted(paths)]
        current = self.root / "build/ci/current.json"
        current.write_text(json.dumps({"version": 1, "candidate": candidate, "round": round_id,
            "steps": [{"name": name, "raw_exit": 0, "exit": 0, "status": "executed", "log": "build/ci/fixture.log"}
                      for name in ("lean-report", "scribe", "filemap", "check-current")], "materials": materials(paths)}))
        (self.root / "build/ci/current-transport.json").write_text(json.dumps({"version": 1, "stage": "current",
            "candidate": candidate, "round": round_id, "commit": self.env["CANDIDATE_SHA"],
            "run_id": int(self.env["GITHUB_RUN_ID"]), "run_attempt": int(self.env["GITHUB_RUN_ATTEMPT"]),
            "repository": self.env["GITHUB_REPOSITORY"], "materials": [dict(item,
                mode=(self.root / item["path"]).stat().st_mode & 0o777) for item in
                materials(paths + ["build/ci/current.json", "build/ci/current-result.json"])]}))

    def test_report_export_requires_matching_handoff(self):
        fixture = self.prepare_report()
        self.produce_report(fixture)
        self.assertEqual("true", self.snapshot_result()[0]["report_ready"])
        manifest = self.root / "build/lean-cache/report/manifest.json"
        saved = manifest.read_bytes()
        paths = [self.root / "build/ci" / name for name in ("current-result.json", "current.json", "current-transport.json")]
        original = [path.read_bytes() for path in paths]
        cases = ("missing-current", "missing-transport", "current-bytes", "summary-bytes", "candidate", "round",
                 "commit", "run_id", "run_attempt", "repository", "stage", "missing-binding", "material-binding",
                 "current-candidate", "current-round", "current-material")
        for case in cases:
            with self.subTest(case=case):
                if case == "missing-current": paths[1].unlink()
                elif case == "missing-transport": paths[2].unlink()
                elif case == "current-bytes": paths[1].write_bytes(original[1] + b" ")
                elif case == "summary-bytes": paths[0].write_bytes(original[0] + b" ")
                else:
                    transport = json.loads(original[2])
                    if case.startswith("current-"):
                        current = json.loads(original[1])
                        if case == "current-material": current["materials"][0]["sha256"] = "0" * 64
                        else: current[case.removeprefix("current-")] = "stale"
                        paths[1].write_text(json.dumps(current))
                        for item in transport["materials"]:
                            if item["path"] == "build/ci/current.json":
                                item["sha256"] = hashlib.sha256(paths[1].read_bytes()).hexdigest()
                    elif case == "missing-binding": transport["materials"] = transport["materials"][1:]
                    elif case == "material-binding": transport["materials"][-1]["sha256"] = "0" * 64
                    else: transport[case] = 99 if case in ("run_id", "run_attempt") else "stale"
                    paths[2].write_text(json.dumps(transport))
                readiness, receipts = self.snapshot_result()
                self.assertEqual("false", readiness["report_ready"], receipts)
                self.assertEqual("save-failed", receipts["report"]["status"])
                self.assertEqual(saved, manifest.read_bytes())
                self.assertFalse(list(manifest.parent.parent.glob(".snapshot-*")))
            for path, data in zip(paths, original): path.write_bytes(data)

    def test_report_export_does_not_revalidate(self):
        fixture = self.prepare_report()
        self.produce_report(fixture)
        hooks = self.root / "export-hooks"
        hooks.mkdir()
        (hooks / "sitecustomize.py").write_text('''
import atexit, collections, json, os, pathlib, subprocess, sys
counts = collections.Counter()
processes = []
def observe(frame, event, arg):
    if event == "call":
        file, name = pathlib.Path(frame.f_code.co_filename).name, frame.f_code.co_name
        if (file == "delta.py" and name in ("valid_bundle", "parse_json_modules", "validate_materials")
                or file == "zipfile.py" and name == "read"):
            counts[name] += 1
sys.setprofile(observe)
start = subprocess.Popen
def process(command, *args, **kwargs):
    processes.append(command)
    return start(command, *args, **kwargs)
subprocess.Popen = process
def finish():
    sys.setprofile(None)
    with open(os.environ["EXPORT_OBSERVATIONS"], "a") as stream:
        stream.write(json.dumps({"counts": dict(counts), "processes": processes}) + "\\n")
atexit.register(finish)
''')
        observations = self.root / "export-observations.jsonl"
        with mock.patch.dict(self.env, PYTHONPATH=str(hooks), EXPORT_OBSERVATIONS=str(observations)):
            readiness, receipts = self.snapshot_result()
        self.assertEqual("true", readiness["report_ready"], receipts)
        recorded = [json.loads(line) for line in observations.read_text().splitlines()]
        print("REPORT_EXPORT_CALLS " + json.dumps(recorded), flush=True)
        self.assertEqual({}, {key: value for row in recorded for key, value in row["counts"].items()})
        self.assertTrue(all(pathlib.Path(command[0]).name == "git" for row in recorded for command in row["processes"]), recorded)

    def test_report_snapshot_keeps_only_current_complete_seed(self):
        from argparse import Namespace
        from lean_seed_contract import DeltaTests
        sys.path.insert(0, str(REPO / "tools/lean-inspector"))
        from report_cache import store
        fixture = self.prepare_report()
        current = self.produce_report(fixture)
        partition = json.loads(fixture.bundle_bytes(current)[".seed.json"])["partition"]
        history = DeltaTests()
        history.setUp()
        self.addCleanup(history.doCleanups)
        history.add_declaration_material()
        for index, seed_partition in enumerate((partition, partition, partition.replace(REV, "f" * 40)), 1):
            history.address = str(index) * 64
            history.store()
            pathlib.Path(str(history.report) + ".seed.json").write_text(json.dumps({
                "schema": "lean-report-seed-v1", "partition": seed_partition, "runtime_sha256": "c" * 64,
                "report_sha256": hashlib.sha256(history.report.read_bytes()).hexdigest(),
                "materials_sha256": hashlib.sha256(pathlib.Path(str(history.report) + ".materials.zip").read_bytes()).hexdigest()}))
            self.assertTrue(store(Namespace(repository=None, report=history.report, cache_root=fixture.cache)))
        seeds = fixture.seeds()
        self.assertEqual(4, len(seeds))
        for seed in seeds:
            os.utime(seed.parent, ns=(1, 1) if seed == current else (2, 2))
        before = {seed: fixture.bundle_bytes(seed) for seed in seeds}
        readiness, receipts = self.snapshot_result()
        self.assertEqual("true", readiness["report_ready"], receipts)
        cached = self.root / "build/lean-cache/report"
        expected = {current.relative_to(fixture.cache).as_posix() + suffix: data
                    for suffix, data in before[current].items()}
        actual = {path.relative_to(cached / "data").as_posix(): path.read_bytes()
                  for path in (cached / "data").rglob("*") if path.is_file()}
        print("REPORT_SNAPSHOT_INVENTORY " + json.dumps({
            "local_seed_count": len(seeds), "snapshot_files": len(actual),
            "snapshot_bytes": sum(map(len, actual.values())), "current_files": len(expected),
            "current_bytes": sum(map(len, expected.values())), "paths": sorted(actual)}), flush=True)
        self.assertEqual(expected, actual)
        self.assertEqual(before, {seed: fixture.bundle_bytes(seed) for seed in seeds})
        self.assertFalse(any(path.is_symlink() for path in (cached / "data").rglob("*")))
        self.assertEqual(0o700, (cached / "data").stat().st_mode & 0o777)
        key = json.loads((cached / "manifest.json").read_text())["key"]
        # Simulate a fresh PR runner; no report output can secretly seed it.
        shutil.rmtree(fixture.cache)
        shutil.rmtree(fixture.output.parent)
        self.env.update(GITHUB_EVENT_NAME="pull_request_target", STRATALINT_CACHE_WRITES="false")
        restored = self.run_tool(CACHE, "restore", "--report-key", key)
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        self.assertIn('"status": "restored"', restored.stdout)
        self.assertEqual([current], fixture.seeds())
        self.assertEqual(before[current], fixture.bundle_bytes(current))
        config = self.root / "lakefile.toml"
        config.write_text(config.read_text().replace('name = "fixture"', 'name = "metadata-only"'))
        reused = fixture.pair()
        self.assertEqual(0, reused.returncode, reused.stdout + reused.stderr)
        self.assertIn("mode=reuse changed=0 added=0 removed=0 recheck=0", reused.stdout)
        (self.root / "D5/A.lean").write_text("def a := 4\n")
        incremental = fixture.pair()
        self.assertEqual(0, incremental.returncode, incremental.stdout + incremental.stderr)
        self.assertIn("mode=delta changed=1 added=0 removed=0 recheck=2", incremental.stdout)
        produced = fixture.bundle_bytes(fixture.output)
        fixture.cache = self.root / "clean-cache"
        fixture.output = self.root / "clean-output/raw-lean-report.json"
        clean = fixture.pair()
        self.assertEqual(0, clean.returncode, clean.stdout + clean.stderr)
        for suffix in ("", ".materials.zip", ".seed.json", ".provenance.json", ".input.attestation"):
            self.assertEqual(produced[suffix], fixture.bundle_bytes(fixture.output)[suffix])
        commands = (self.root / "lake-runs").read_text().splitlines()
        self.assertEqual(4, commands.count("build"))
        self.assertEqual(3, sum("--run" in command for command in commands))
        readiness, receipts = self.snapshot_result()
        self.assertEqual("false", readiness["report_ready"])
        self.assertEqual("save-disabled", receipts["report"]["status"])
        self.assertEqual(actual, {path.relative_to(cached / "data").as_posix(): path.read_bytes()
                               for path in (cached / "data").rglob("*") if path.is_file()})

    def test_report_snapshot_rejects_invalid_current_without_using_history(self):
        fixture = self.prepare_report()
        current = self.produce_report(fixture)
        self.assertEqual("true", self.snapshot_result()[0]["report_ready"])
        cached = self.root / "build/lean-cache/report/manifest.json"
        saved = cached.read_bytes()
        bundle = fixture.bundle_bytes(fixture.output)
        summary = self.root / "build/ci/current-result.json"
        original_summary = summary.read_bytes()
        cases = ["missing-summary", "failed-current", "missing-report", "missing-seed", "materials", "partition", "identity",
                 "sha", "bound-sha", "bound-sha-name", "missing-sha", "missing-attestation", "missing-provenance", "missing-materials"]
        for case in cases:
            with self.subTest(case=case):
                if case == "missing-summary": summary.unlink()
                elif case == "failed-current":
                    failed = fixture.pair(LAKE_BUILD_FAIL="19")
                    self.assertEqual(19, failed.returncode, failed.stdout + failed.stderr)
                    summary.write_text(json.dumps({"stage": "current", "exit": 2,
                        "report": fixture.output.relative_to(self.root).as_posix()}))
                elif case == "missing-report": fixture.output.unlink()
                elif case == "missing-seed": pathlib.Path(str(fixture.output) + ".seed.json").unlink()
                elif case in ("sha", "bound-sha", "bound-sha-name"):
                    value = "0" * 64 + "  " + fixture.output.name + "\n"
                    if case == "bound-sha-name": value = hashlib.sha256(bundle[""]).hexdigest() + "  wrong-name.json\n"
                    pathlib.Path(str(fixture.output) + ".sha256").write_text(value)
                    # Current's material seal alone does not replace the original
                    # SHA sidecar grammar/digest check before copy rewrites it.
                    if case.startswith("bound-"): self.write_handoff(fixture)
                elif case.startswith("missing-"):
                    suffix = {"missing-sha": ".sha256", "missing-attestation": ".input.attestation",
                              "missing-provenance": ".provenance.json", "missing-materials": ".materials.zip"}[case]
                    pathlib.Path(str(fixture.output) + suffix).unlink()
                elif case == "materials": pathlib.Path(str(fixture.output) + ".materials.zip").write_bytes(b"corrupt")
                elif case == "partition":
                    seed = json.loads(bundle[".seed.json"])
                    seed["partition"] = seed["partition"].replace(REV, "f" * 40)
                    pathlib.Path(str(fixture.output) + ".seed.json").write_text(json.dumps(seed))
                else: (self.root / "D5/A.lean").write_text("def a := 99\n")
                readiness, receipts = self.snapshot_result()
                self.assertEqual("false", readiness["report_ready"], receipts)
                self.assertEqual("save-failed", receipts["report"]["status"])
                self.assertEqual(saved, cached.read_bytes())
                self.assertFalse(list(cached.parent.parent.glob(".snapshot-*")))
                fixture.write_bundle_bytes(fixture.output, bundle)
                summary.write_bytes(original_summary)
                (self.root / "D5/A.lean").write_text("def a := 1\n")
                self.write_handoff(fixture)
        self.assertEqual(bundle[".materials.zip"], fixture.bundle_bytes(current)[".materials.zip"])

    def test_report_staging_and_restore_validate_independently(self):
        fixture = self.prepare_report()
        self.produce_report(fixture)
        self.assertEqual("true", self.snapshot_result()[0]["report_ready"])
        cached = self.root / "build/lean-cache/report"
        saved = (cached / "manifest.json").read_bytes()
        hooks = self.root / "snapshot-hooks"
        hooks.mkdir()
        (hooks / "sitecustomize.py").write_text('''
import pathlib, shutil
copy = shutil.copyfile
def damaged(source, target, *args, **kwargs):
    result = copy(source, target, *args, **kwargs)
    path = pathlib.Path(target)
    if any(part.startswith(".snapshot-") for part in path.parts) and path.name.endswith(".materials.zip"):
        path.write_bytes(b"damaged staging copy")
    return result
shutil.copyfile = damaged
''')
        with mock.patch.dict(self.env, PYTHONPATH=str(hooks)):
            readiness, receipts = self.snapshot_result()
        self.assertEqual("false", readiness["report_ready"], receipts)
        self.assertEqual("save-failed", receipts["report"]["status"])
        self.assertEqual(saved, (cached / "manifest.json").read_bytes())
        self.assertFalse(list(cached.parent.glob(".snapshot-*")))
        report = next((cached / "data").glob("*/*/*/raw-lean-report.json"))
        bundle = fixture.bundle_bytes(report)
        for case in ("missing", "materials", "partition"):
            with self.subTest(case=case):
                manifest = json.loads(saved)
                if case == "missing": report.unlink()
                elif case == "materials": pathlib.Path(str(report) + ".materials.zip").write_bytes(b"corrupt")
                else:
                    path = pathlib.Path(str(report) + ".seed.json")
                    seed = json.loads(path.read_text())
                    seed["partition"] = seed["partition"].replace(REV, "f" * 40)
                    path.write_text(json.dumps(seed))
                    for item in manifest["files"]:
                        item["sha256"] = hashlib.sha256((cached / "data" / item["path"]).read_bytes()).hexdigest()
                (cached / "manifest.json").write_text(json.dumps(manifest))
                shutil.rmtree(fixture.cache, ignore_errors=True)
                restored = self.run_tool(CACHE, "restore", "--report-key", manifest["key"])
                self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
                self.assertIn('"status": "miss"', restored.stdout)
                self.assertEqual([], fixture.seeds())
                fixture.write_bundle_bytes(report, bundle)
        (cached / "manifest.json").write_bytes(saved)

    def test_invalid_dependency_links_disable_only_that_save_with_an_offending_path(self):
        fixture = self.prepare_report()
        self.produce_report(fixture)
        source, _ = self.dependency_files()
        for target in (".lake/build",):
            directory = self.root / target
            directory.mkdir(parents=True)
            (directory / "fixture").write_bytes(b"other layer bytes")
        readiness, _ = self.snapshot_result()
        self.assertEqual({layer + "_ready": "true" for layer in ("dependency", "project", "report")}, readiness)
        cached = self.root / "build/lean-cache/dependency"
        outside = self.root / "outside"
        outside.write_bytes(b"outside must stay private")
        # The same relative escape also lands on an existing file from staging.
        staged_outside = cached.parent / "outside"
        staged_outside.write_bytes(b"outside staging must stay private")
        cases = {
            "escape": "../../../../outside",
            "absolute": str(outside),
            "broken": "missing",
            "self-cycle": "bad-link",
            "chain-cycle": "cycle-peer",
            "directory": "..",
        }
        link = source / "batteries/docs/bad-link"
        link.parent.mkdir()
        peer = link.with_name("cycle-peer")
        for name, target in cases.items():
            before = (cached / "manifest.json").read_bytes()
            with self.subTest(link=name):
                link.symlink_to(target)
                if name == "chain-cycle":
                    peer.symlink_to("bad-link")
                try:
                    readiness, receipts = self.snapshot_result()
                    self.assertEqual({"dependency_ready": "false", "project_ready": "true", "report_ready": "true"},
                                     readiness, receipts)
                    self.assertEqual("save-failed", receipts["dependency"]["status"])
                    self.assertIn("batteries/docs/bad-link", receipts["dependency"]["reason"])
                    self.assertEqual(before, (cached / "manifest.json").read_bytes())
                    self.assertEqual(target, os.readlink(link))
                    self.assertEqual(b"outside must stay private", outside.read_bytes())
                    self.assertEqual(b"outside staging must stay private", staged_outside.read_bytes())
                    self.assertFalse(list(cached.parent.glob(".snapshot-*")))
                finally:
                    link.unlink()
                    peer.unlink(missing_ok=True)

    def test_snapshot_readiness_and_material_follow_writer_permissions(self):
        fixture = self.prepare_report()
        current = self.produce_report(fixture)
        self.env.update(GITHUB_RUN_ID="34362630774", GITHUB_RUN_ATTEMPT="1")
        self.write_handoff(fixture)
        material = {
            "dependency": (".lake/packages", "mathlib/Mathlib.olean", b"private dependency seed\n"),
            "project": (".lake/build", "lib/Module.olean", b"private project seed\n"),
        }
        layers = (*material, "report")
        for target, relative, data in material.values():
            path = self.root / target / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
            path.chmod(0o640)
        system, machine = platform.system().lower(), platform.machine().lower()
        architecture = {"aarch64": "arm64", "x86_64": "x64", "amd64": "x64"}.get(machine, machine)
        partition = f"{REV}/{system}-{architecture}"
        cases = [
            ("dev_push", "push", "refs/heads/dev", "true", "true", True),
            ("dev_pr_target", "pull_request_target", "refs/heads/dev", "true", "true", False),
            ("pr_merge", "pull_request", "refs/pull/7/merge", "true", "true", False),
            ("dev_dispatch", "workflow_dispatch", "refs/heads/dev", "true", "true", False),
            ("dev_writes_false", "push", "refs/heads/dev", "false", "true", False),
            ("dev_check_failed", "push", "refs/heads/dev", "true", "false", False),
            ("dev_check_missing", "push", "refs/heads/dev", "true", None, False),
            ("other_branch", "push", "refs/heads/topic", "true", "true", False),
            ("other_integration", "push", "refs/heads/integration-ci-other-tests", "true", "true", False),
        ]
        # Integration-only rollout data: exclude this block from dev delivery.
        integration = "integration-ci-current-stability-0909-tests"
        cases += [
            ("integration_push", "push", f"refs/heads/{integration}", "true", "true", True),
            ("integration_pr_target", "pull_request_target", f"refs/heads/{integration}", "true", "true", False),
            ("integration_pr", "pull_request", f"refs/heads/{integration}", "true", "true", False),
            ("integration_dispatch", "workflow_dispatch", f"refs/heads/{integration}", "true", "true", False),
            ("integration_writes_false", "push", f"refs/heads/{integration}", "false", "true", False),
            ("integration_check_failed", "push", f"refs/heads/{integration}", "true", "false", False),
            ("integration_check_missing", "push", f"refs/heads/{integration}", "true", None, False),
            ("integration_suffix", "push", f"refs/heads/{integration}-other", "true", "true", False),
            ("integration_tag", "push", f"refs/tags/{integration}", "true", "true", False),
        ]
        # End integration-only rollout data.
        for name, event, ref, writes, success, allowed in cases:
            with self.subTest(case=name):
                cache = self.root / "build/lean-cache"
                if cache.exists():
                    shutil.rmtree(cache)
                output = self.root / "outputs"
                output.unlink(missing_ok=True)
                env = dict(self.env, GITHUB_RUN_ID="34362630774", GITHUB_RUN_ATTEMPT="1",
                           GITHUB_EVENT_NAME=event, GITHUB_REF=ref, STRATALINT_CACHE_WRITES=writes)
                env.pop("STRATALINT_CHECK_SUCCEEDED", None)
                if success is not None:
                    env["STRATALINT_CHECK_SUCCEEDED"] = success
                result = self.run_tool(CACHE, "snapshot", env=env)
                self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertEqual({layer + "_ready": str(allowed).lower() for layer in layers},
                                 dict(line.split("=", 1) for line in output.read_text().splitlines()), result.stdout)
                receipts = [json.loads(line.removeprefix("LEAN_ACTIONS_CACHE "))
                            for line in result.stdout.splitlines() if line.startswith("LEAN_ACTIONS_CACHE ")]
                self.assertEqual({layer: "snapshot" if allowed else "save-disabled" for layer in layers},
                                 {receipt["layer"]: receipt["status"] for receipt in receipts})
                if not allowed:
                    self.assertFalse(cache.exists())
                    continue
                self.assertEqual(fixture.bundle_bytes(current), fixture.bundle_bytes(
                    cache / "report/data" / current.relative_to(fixture.cache)))
                for layer, (target, relative, data) in material.items():
                    staged = cache / layer
                    self.assertEqual(data, (staged / "data" / relative).read_bytes())
                    self.assertEqual(data, (self.root / target / relative).read_bytes())
                    self.assertEqual({
                        "schema": "lean-actions-seed-v1", "partition": partition, "layer": layer,
                        "key": f"lean-{layer}-v3-{REV}-{system}-{architecture}-34362630774-1",
                        "files": [{"path": relative, "sha256": hashlib.sha256(data).hexdigest(), "mode": 0o640}],
                    }, json.loads((staged / "manifest.json").read_text()))


if __name__ == "__main__":
    unittest.main()
