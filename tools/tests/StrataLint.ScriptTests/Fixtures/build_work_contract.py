"""Invocation-local Lean build work at the inspector's two build boundaries."""
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

REPO = Path(__file__).resolve().parents[4]


class BuildWorkContracts(unittest.TestCase):
    def invoke(self, reused=True, targets=True, output="Build completed successfully (1 jobs).\n", failure=0, stale_logs=False, native_work=False, missing_phase_log=False, recorder_failure=False):
        temp = tempfile.TemporaryDirectory(prefix="build-work-contract-")
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        for name in ("tools/lean-inspector/inspect.sh", "tools/scripts/lib/resource-observation-lib.sh",
                     "tools/lean-inspector/build_work.py"):
            dest = root / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            if (REPO / name).exists(): shutil.copyfile(REPO / name, dest)
        def script(name, text):
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            path.chmod(0o755)
            return path
        script("tools/scripts/report/lean-report-selection.py", "import sys\nsys.exit(0)\n")
        script("tools/lean-inspector/reuse.py",
               "import sys\nsys.exit(" + str(0 if reused else 3) + " if sys.argv[1] == 'reuse' else 0)\n")
        script("tools/lean-inspector/native.py", "import sys\nfrom pathlib import Path\n" +
               ("(Path(sys.argv[3] + '.logs') / 'report.exit.log').unlink()\n" if missing_phase_log else "") +
               "sys.exit(0)\n")
        script("tools/scripts/worktree/lean-cache-ensure.sh", "#!/bin/bash\nexit 0\n")
        script("tools/scripts/worktree/lean-cache-run.sh",
               "#!/bin/bash\ncat <<'LOG'\n" + output + "LOG\nexit " + str(failure) + "\n")
        lake = script("fake-lake", "#!/bin/bash\nexit 0\n")
        producer = root / "producer.dll"
        producer.touch()
        artifact = root / ".lake/build/lib/lean/Probe.olean"
        artifact.parent.mkdir(parents=True)
        artifact.write_bytes(b"existing artifact")
        dependency = root / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Probe.olean"
        dependency.parent.mkdir(parents=True)
        dependency.write_bytes(b"dependency artifact")
        fact = root / "build/lean-cache/build-work.json"
        fact.parent.mkdir(parents=True)
        fact.write_text('{"report":999,"programs":999}')
        if stale_logs:
            logs = root / "report.json.logs"
            logs.mkdir()
            (logs / "report.exit.log").write_text("0")
            (logs / "report.stdout.log").write_text("✔ [1/1] Built Probe\nBuild completed successfully (1 jobs).\n")
            (logs / "report.stderr.log").write_text("")
        if native_work:
            path = root / "tools/scripts/worktree/lean-cache-run.sh"
            path.write_text(path.read_text().replace("cat <<'LOG'", "printf '%s\\n' '{\"kind\":\"extract\",\"count\":1}' >> \"$STRATALINT_INSPECTOR_ACTIVITY\"\ncat <<'LOG'"))
        if recorder_failure:
            script("tools/lean-inspector/build_work.py",
                   "import sys\nprint('LEAN_BUILD_WORK_UNKNOWN recorder unavailable', file=sys.stderr)\nsys.exit(2)\n")
        env = dict(os.environ, STRATALINT_INSPECTOR_SUPERVISED="1", LAKE_BIN=str(lake),
                   STRATALINT_LEAN_PRODUCER_DLL=str(producer), GITHUB_RUN_ID="17", GITHUB_RUN_ATTEMPT="2",
                   STRATALINT_LEAN_BUILD_WORK_FILE=str(fact),
                   STRATALINT_LEAN_BUILD_TARGETS='["Probe"]' if targets else '[]')
        result = subprocess.run(["bash", str(root / "tools/lean-inspector/inspect.sh"),
                                 "--repository", str(root), "--output", str(root / "report.json")],
                                env=env, capture_output=True, text=True)
        return result, fact, root

    def recorder_inputs(self, output="Build completed successfully (1 jobs).\n", activity=()):
        temp = tempfile.TemporaryDirectory(prefix="build-work-contract-")
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        script = root / "build_work.py"
        shutil.copyfile(REPO / "tools/lean-inspector/build_work.py", script)
        logs = root / "logs"
        logs.mkdir()
        for name, text in (("report.exit.log", "0"), ("report.stdout.log", output),
                           ("report.stderr.log", ""),
                           ("native-work.jsonl", "".join(json.dumps(row) + "\n" for row in activity))):
            (logs / name).write_text(text)
        project = root / ".lake/build/lib/lean/Probe.olean"
        project.parent.mkdir(parents=True)
        project.write_bytes(b"project artifact")
        fact = root / "work/build-work.json"
        fact.parent.mkdir()
        fact.write_text('{"report":999,"programs":999}')
        return root, logs, fact

    def run_recorder(self, root, logs, fact):
        return subprocess.run([sys.executable, "-B", str(root / "build_work.py"),
                               str(root), str(logs), str(fact), "report"],
                              capture_output=True, text=True)

    def test_aggregate_native_activity_is_added_to_report_work(self):
        root, logs, fact = self.recorder_inputs(
            output="✔ [1/1] Built Probe\nBuild completed successfully (1 jobs).\n",
            activity=({"kind": "aggregate", "count": 2}, {"kind": "extract", "count": 3},
                      {"kind": "aggregate", "count": 0}))
        result = self.run_recorder(root, logs, fact)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual((6, 0), (json.loads(fact.read_text())["report"],
                                json.loads(fact.read_text())["programs"]))

    def test_malformed_native_activity_reports_unknown_and_exits_two(self):
        for row in ({"kind": "other", "count": 1}, {"count": 1},
                    {"kind": "extract", "count": True}, {"kind": "aggregate", "count": -1},
                    {"kind": "aggregate", "count": "1"}, {"kind": "extract", "count": 1.5},
                    {"kind": "extract", "count": None}, {"kind": "extract"}, [], None, "activity"):
            with self.subTest(row=row):
                root, logs, fact = self.recorder_inputs(activity=(row,))
                previous = fact.read_bytes()
                result = self.run_recorder(root, logs, fact)
                self.assertEqual(2, result.returncode, result.stderr)
                self.assertIn("LEAN_BUILD_WORK_UNKNOWN invalid native build activity", result.stderr)
                self.assertNotIn("LEAN_BUILD_WORK ", result.stdout)
                self.assertEqual(previous, fact.read_bytes())

    def test_extensionless_executable_captions_resolve_project_and_package_outputs(self):
        for caption, expected in (("projectProbe", 1), ("fixture/projectProbe:exe", 1),
                                  ("packageProbe", 0), ("dependency/packageProbe:exe", 0)):
            with self.subTest(caption=caption):
                root, logs, fact = self.recorder_inputs(
                    output="✔ [1/1] Built " + caption + "\nBuild completed successfully (1 jobs).\n")
                for name in (".lake/build/bin/projectProbe",
                             ".lake/packages/dependency/.lake/build/bin/packageProbe"):
                    path = root / name
                    path.parent.mkdir(parents=True)
                    path.write_text("#!/bin/sh\nexit 0\n")
                    path.chmod(0o755)
                result = self.run_recorder(root, logs, fact)
                self.assertEqual(0, result.returncode, result.stderr)
                self.assertEqual(expected, json.loads(fact.read_text())["report"])

    def test_known_project_work_remains_a_lower_bound_with_unresolved_captions(self):
        root, logs, fact = self.recorder_inputs(
            output="✔ [1/2] Built Probe\n✔ [2/2] Built UnknownTarget\n"
                   "Build completed successfully (2 jobs).\n")
        result = self.run_recorder(root, logs, fact)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(1, json.loads(fact.read_text())["report"])

    def test_recorder_atomically_replaces_the_work_fact(self):
        root, logs, fact = self.recorder_inputs(activity=({"kind": "aggregate", "count": 2},))
        previous = fact.read_bytes()
        retained = fact.with_name("previous-work.json")
        os.link(fact, retained)
        result = self.run_recorder(root, logs, fact)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(2, json.loads(fact.read_text())["report"])
        self.assertEqual(previous, retained.read_bytes())
        self.assertEqual([], list(fact.parent.glob(".build-work-*")))

    def test_recorder_canonicalizes_the_repository_address(self):
        root, logs, fact = self.recorder_inputs()
        alias = root / "repository-link"
        alias.symlink_to(root, target_is_directory=True)
        result = self.run_recorder(alias, logs, fact)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(str(root.resolve()), json.loads(fact.read_text())["repository"])

    def test_recorder_keeps_the_destination_present_until_replace(self):
        root, logs, fact = self.recorder_inputs()
        previous = fact.read_bytes()
        replace = Path.replace

        def checked_replace(source, destination):
            self.assertTrue(destination.is_file(), "work fact disappeared before replacement")
            self.assertEqual(previous, destination.read_bytes())
            return replace(source, destination)

        record = runpy.run_path(str(root / "build_work.py"))["record"]
        with mock.patch.object(Path, "replace", autospec=True, side_effect=checked_replace) as replacing:
            record(root, logs, fact, "report")
        replacing.assert_called_once()
        self.assertEqual(0, json.loads(fact.read_text())["report"])

    def test_recorder_io_failure_reports_unknown_and_exits_two(self):
        for defect in ("parent-file", "destination-directory", "missing-log"):
            with self.subTest(defect=defect):
                root, logs, fact = self.recorder_inputs()
                previous = fact.read_bytes()
                if defect == "parent-file":
                    blocked = root / "blocked"
                    blocked.write_text("not a directory")
                    destination = blocked / "build-work.json"
                elif defect == "destination-directory":
                    destination = fact.parent / "blocked"
                    destination.mkdir()
                    (destination / "keep").write_bytes(previous)
                else:
                    destination = fact
                    (logs / "report.stdout.log").unlink()
                result = self.run_recorder(root, logs, destination)
                self.assertEqual(2, result.returncode, result.stderr)
                self.assertIn("LEAN_BUILD_WORK_UNKNOWN ", result.stderr)
                self.assertNotIn("LEAN_BUILD_WORK ", result.stdout)
                self.assertEqual(previous, fact.read_bytes())
                self.assertEqual([], list(fact.parent.glob(".build-work-*")))
                if defect == "destination-directory":
                    self.assertEqual(previous, (destination / "keep").read_bytes())

    def test_optional_recorder_failure_preserves_successful_inspector_exit(self):
        result, fact, _ = self.invoke(recorder_failure=True)
        self.assertIn("LEAN_BUILD_WORK_UNKNOWN recorder unavailable", result.stderr)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertFalse(fact.exists())

    def test_reused_report_still_records_program_work(self):
        result, fact, root = self.invoke(output="✔ [1/1] Built Probe (15ms)\nBuild completed successfully (1 jobs).\n")
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(dict(schema_version=1, run_id="17", run_attempt="2", repository=str(root.resolve()),
                              report=0, programs=1), json.loads(fact.read_text()))
        self.assertIn("LEAN_BUILD_WORK", result.stdout + result.stderr)

    def test_report_boundary_counts_work_without_program_phase(self):
        result, fact, _ = self.invoke(reused=False, targets=False,
            output="✔ [1/1] Built Probe:report (internal native artifact) (15ms)\nBuild completed successfully (1 jobs).\n")
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(1, json.loads(fact.read_text())["report"])
        self.assertEqual(0, json.loads(fact.read_text())["programs"])

    def test_replays_and_dependency_only_builds_are_zero_project_work(self):
        for output in ("ℹ [1/1] Replayed Probe\n", "✔ [1/1] Built Mathlib.Probe (2ms)\n", ""):
            with self.subTest(output=output):
                result, fact, _ = self.invoke(output=output + "Build completed successfully (1 jobs).\n")
                self.assertEqual(0, result.returncode, result.stderr)
                self.assertEqual(0, json.loads(fact.read_text())["programs"])

    def test_unrecognized_or_incomplete_lake_output_is_unknown(self):
        for output in ("✔ [1/1] Built UnknownTarget\nBuild completed successfully (1 jobs).\n", ""):
            with self.subTest(output=output):
                result, fact, _ = self.invoke(output=output)
                self.assertEqual(0, result.returncode, result.stderr)
                self.assertIsNone(json.loads(fact.read_text())["programs"])

    def test_stale_phase_logs_cannot_be_inherited_by_a_reused_report(self):
        result, fact, _ = self.invoke(targets=False, stale_logs=True)
        self.assertEqual(0, result.returncode, result.stderr)
        value = json.loads(fact.read_text())
        self.assertEqual((0, 0), (value["report"], value["programs"]))

    def test_native_report_build_actions_are_counted_without_compiler_work(self):
        result, fact, _ = self.invoke(reused=False, targets=False, native_work=True)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertGreater(json.loads(fact.read_text())["report"], 0)

    def test_missing_current_phase_log_is_unknown(self):
        result, fact, _ = self.invoke(reused=False, targets=False, missing_phase_log=True)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertIsNone(json.loads(fact.read_text())["report"])

    def test_failed_build_removes_stale_fact_and_preserves_exit(self):
        result, fact, _ = self.invoke(failure=23)
        self.assertEqual(23, result.returncode, result.stderr)
        self.assertFalse(fact.exists())

    def test_failed_report_producer_leaves_no_work_fact(self):
        result, fact, _ = self.invoke(reused=False, targets=False, failure=23)
        self.assertEqual(23, result.returncode, result.stderr)
        self.assertFalse(fact.exists())


if __name__ == "__main__":
    unittest.main()
