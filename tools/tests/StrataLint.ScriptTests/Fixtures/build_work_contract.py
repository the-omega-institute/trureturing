"""Invocation-local Lean build work at the inspector's two build boundaries."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

REPO = Path(__file__).resolve().parents[4]


class BuildWorkContracts(unittest.TestCase):
    def invoke(self, reused=True, targets=True, output="Build completed successfully (1 jobs).\n", failure=0, stale_logs=False, native_work=False, missing_phase_log=False):
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
        env = dict(os.environ, STRATALINT_INSPECTOR_SUPERVISED="1", LAKE_BIN=str(lake),
                   STRATALINT_LEAN_PRODUCER_DLL=str(producer), GITHUB_RUN_ID="17", GITHUB_RUN_ATTEMPT="2",
                   STRATALINT_LEAN_BUILD_WORK_FILE=str(fact),
                   STRATALINT_LEAN_BUILD_TARGETS='["Probe"]' if targets else '[]')
        result = subprocess.run(["bash", str(root / "tools/lean-inspector/inspect.sh"),
                                 "--repository", str(root), "--output", str(root / "report.json")],
                                env=env, capture_output=True, text=True)
        return result, fact, root

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


if __name__ == "__main__":
    unittest.main()
