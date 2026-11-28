"""Exercise the Omega result reader, writer and Lean success boundary."""

import base64
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import audit_cache


REPORT = b'{"backend":"mathlib","consumerModules":["D5.Root"],"declarations":[]}\n'
CLI = Path("src/OmegaChecks/audit_cache.py")


class AuditCacheTests(unittest.TestCase):
    def setUp(self):
        self.root = Path(self.enterContext(tempfile.TemporaryDirectory()))

    def runner(self, name):
        project = self.root / name
        for relative in audit_cache.RULES:
            dest = project / relative
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(audit_cache.ROOT / relative, dest)
        inputs = []
        for label in ("strict/D5.Root/olean", "strict/D5.Import/olean", "reference/D5.Import/olean", "driver/omegaAudit"):
            path = project / "stage" / label
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(label)
            inputs.append([label, str(path)])
        self.write_manifest(project, {"kind": "official-interface", "arguments": ["D5.Root", "D5.Other", "--basis"],
                                     "report": str(project / "report.json"), "files": inputs})
        return project

    def write_manifest(self, project, data):
        (project / "manifest.json").write_text(json.dumps(data))

    def invoke(self, project, operation, code):
        result = subprocess.run([sys.executable, "-B", CLI, operation, "manifest.json"], cwd=project,
                                env={**os.environ, "OMEGA_AUDIT_CACHE": str(project / "cache")},
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, code, result.stdout + result.stderr)
        return result.stdout

    def seed(self):
        first = self.runner("producer")
        self.assertIn("miss", self.invoke(first, "lookup", 1))
        (first / "report.json").write_bytes(REPORT)
        self.invoke(first, "store", 0)
        records = list((first / "cache/produced").glob("*.json"))
        self.assertEqual(len(records), 1)
        return records[0]

    def restore(self, project, record):
        dest = project / "cache/restored" / record.name
        dest.parent.mkdir(parents=True)
        shutil.copyfile(record, dest)
        return dest

    def test_same_inputs_in_another_checkout_restore_original_report_bytes(self):
        record = self.seed()
        consumer = self.runner("consumer")
        manifest = json.loads((consumer / "manifest.json").read_text())
        manifest["files"].reverse()
        self.write_manifest(consumer, manifest)
        self.restore(consumer, record)
        self.assertIn("hit", self.invoke(consumer, "lookup", 0))
        self.assertEqual((consumer / "report.json").read_bytes(), REPORT)
        self.assertFalse((consumer / "cache/produced").exists())

    def test_transitive_inputs_driver_and_audit_rules_each_invalidate(self):
        record = self.seed()
        for i, file in enumerate(("stage/strict/D5.Import/olean", "stage/reference/D5.Import/olean",
                                  "stage/driver/omegaAudit", "src/OmegaChecks/check.py", "lean-toolchain")):
            with self.subTest(file=file):
                consumer = self.runner(f"consumer-{i}")
                self.restore(consumer, record)
                (consumer / file).write_bytes(b"changed input")
                self.assertIn("miss", self.invoke(consumer, "lookup", 1))
                self.assertFalse((consumer / "report.json").exists())

    def test_backend_kind_ordered_roots_and_report_presence_each_invalidate(self):
        record = self.seed()
        for i, change in enumerate(({"kind": "common-interface"}, {"arguments": ["D5.Other", "D5.Root", "--basis"]},
                                    {"arguments": ["D5.Root", "--basis"]}, {"report": None})):
            with self.subTest(change=change):
                consumer = self.runner(f"consumer-{i}")
                self.restore(consumer, record)
                self.write_manifest(consumer, json.loads((consumer / "manifest.json").read_text()) | change)
                self.assertIn("miss", self.invoke(consumer, "lookup", 1))
                self.assertFalse((consumer / "report.json").exists())

    def test_corrupt_record_never_replaces_the_report(self):
        record = self.seed()
        for i, change in enumerate(({"report": base64.b64encode(b"changed report").decode()}, {"report": "?"},
                                    {"kind": "strict-kernel"}, {"key": "f" * 64}, {"schema": "obsolete"})):
            with self.subTest(change=change):
                consumer = self.runner(f"consumer-{i}")
                restored = self.restore(consumer, record)
                restored.write_text(json.dumps(json.loads(restored.read_text()) | change))
                previous = consumer / "report.json"
                previous.write_bytes(b"previous report")
                self.invoke(consumer, "lookup", 1)
                self.assertEqual(previous.read_bytes(), b"previous report")
                self.assertFalse((consumer / "cache/produced").exists())

    def test_changed_input_or_missing_report_prevents_store(self):
        project = self.runner("producer")
        self.assertIn("miss", self.invoke(project, "lookup", 1))
        self.invoke(project, "store", 1)
        (project / "report.json").write_bytes(REPORT)
        (project / "stage/strict/D5.Import/olean").write_bytes(b"changed since lookup")
        self.invoke(project, "store", 1)
        self.assertFalse((project / "cache/produced").exists())

    def test_lean_caller_only_records_completed_actions(self):
        project = self.runner("caller")
        source = Path(__file__).with_name("AuditCache.lean")
        shutil.copyfile(source, project / source.name)
        # Execute the repository's real withResult around each action without Mathlib.
        probe = project / "Probe.lean"
        probe.write_text("""import AuditCache
def main (args : List String) : IO Unit := do
  OmegaChecks.AuditCache.withResult "strict-kernel" #["Root"] #[] do
    IO.FS.writeFile "action-ran" "yes"
    match args with
    | ["fail"] => throw (IO.userError "probe failed")
    | ["interrupt"] => IO.Process.exit 19
    | _ => pure ()
""")
        env = {**os.environ, "OMEGA_AUDIT_CACHE": str(project / "cache"), "LEAN_PATH": str(project)}
        subprocess.run(["lean", "-o", "AuditCache.olean", source.name], cwd=project, env=env, check=True)
        marker = project / "action-ran"
        for mode, expected in (("fail", 1), ("interrupt", 19), ("complete", 0)):
            with self.subTest(mode=mode):
                proc = subprocess.run(["lean", "--run", probe.name, mode], cwd=project, env=env,
                                      capture_output=True, text=True)
                self.assertEqual(proc.returncode, expected, proc.stdout + proc.stderr)
                self.assertTrue(marker.is_file(), proc.stdout + proc.stderr)
                marker.unlink()
                rows = list((project / "cache/produced").glob("*.json"))
                self.assertEqual(len(rows), int(expected == 0), proc.stdout + proc.stderr)
        self.restore(project, rows[0])
        proc = subprocess.run(["lean", "--run", probe.name, "fail"], cwd=project, env=env,
                              capture_output=True, text=True)
        self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
        self.assertIn("hit", proc.stdout)
        self.assertFalse(marker.exists())


if __name__ == "__main__":
    unittest.main()
