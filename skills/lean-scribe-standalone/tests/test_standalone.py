"""Source-export and admission boundaries; no Lean cache or SDK is needed."""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ENTRY = Path(__file__).resolve().parents[1] / "scripts/standalone.py"
SPEC = importlib.util.spec_from_file_location("standalone", ENTRY)
standalone = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(standalone)


class SourceExportTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="standalone tests ")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / "upstream"
        self.source.mkdir()
        self.git("init", "--quiet")
        self.write("lean-report-inputs.json", json.dumps({"producer_scopes": {"lean-report": {"include": []}}}))
        self.write("tools/lean-inspector-interface/Contract.lean", "import D5.S0.Observation.Support\n")
        self.write("D5/S0/Observation/Support.lean", "def support := 1\n")
        self.write("Golden/Frozen/state/D5/S0/Observation/Support.lean.json", '{"statement_id":"support"}\n')
        self.write("D5/S0/Observation/Result.lean", "import D5.S0.Observation.Support\ndef answer := support\n")
        self.write("Blueprint/D5/S0/Observation/Result.scribe.cs", '// reference "Cited"\n')
        self.write("Golden/Frozen/state/D5/S0/Observation/Result.lean.json", '{"statement_id":"result"}\n')
        self.write("Library/Area/Cited.md", "Cited result.\n")
        self.write("Library/Area/Other.md", "Unrelated result.\n")
        self.write("tools/Example/bin/ignored.dll", "compiled")
        self.write("Golden/Projection/unrelated.json", "{}")
        self.git("add", ".")
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid", "commit", "--quiet", "-m", "fixture")
        self.revision = self.git("rev-parse", "HEAD").strip()
        self.dest = self.root / "new project"

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.source, text=True)

    def write(self, name, text):
        path = self.source / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def initialize(self):
        standalone.initialize(argparse.Namespace(source=self.source, dest=self.dest,
            revision=self.revision, include=["D5.S0.Observation.Result"]))

    def test_export_is_pinned_relocatable_and_source_only(self):
        self.write("D5/S0/Observation/Result.lean", "dirty working copy\n")
        self.initialize()
        self.assertIn("import D5", (self.dest / "D5/S0/Observation/Result.lean").read_text())
        self.assertTrue((self.dest / "D5/S0/Observation/Support.lean").is_file())
        self.assertTrue((self.dest / "Library/Area/Cited.md").is_file())
        self.assertFalse((self.dest / "Library/Area/Other.md").exists())
        self.assertFalse((self.dest / "tools/Example/bin/ignored.dll").exists())
        self.assertFalse((self.dest / ".lake").exists())
        self.assertFalse((self.dest / "Golden/Projection").exists())
        self.assertFalse((self.dest / "Golden/Frozen/state/D5/S0/Observation/Result.lean.json").exists())
        moved = self.root / "moved project"
        self.dest.rename(moved)
        standalone.protect(moved)
        (moved / "D5/S0/Observation/Support.lean").unlink()
        with self.assertRaisesRegex(ValueError, "protected source changed or missing"):
            standalone.protect(moved)

    def test_nonempty_destination_preserves_user_files(self):
        self.dest.mkdir()
        (self.dest / "user.txt").write_text("keep")
        with self.assertRaisesRegex(ValueError, "absent or empty"):
            self.initialize()
        self.assertEqual((self.dest / "user.txt").read_text(), "keep")

    def test_missing_local_import_fails(self):
        with self.assertRaisesRegex(ValueError, "unresolved upstream import"):
            standalone.source_closure(lambda _: b"import D5.Missing\n", {"Input.lean"}, ["Input.lean"])

    def test_deleting_freeze_manifest_fails_even_before_first_freeze(self):
        self.initialize()
        (self.dest / "standalone-frozen.json").unlink()
        with self.assertRaisesRegex(ValueError, "missing standalone protection manifest"):
            standalone.protect(self.dest)

    def test_emptying_freeze_manifest_cannot_hide_a_live_pin(self):
        self.initialize()
        pin = self.dest / "Golden/Frozen/state/D5/S0/Observation/Result.lean.json"
        pin.write_text('{"statement_id":"result"}\n')
        with self.assertRaisesRegex(ValueError, "frozen pin missing source protection"):
            standalone.protect(self.dest)

    def test_committed_freeze_protection_cannot_shrink(self):
        self.initialize()
        path = self.dest / "standalone-frozen.json"
        name = "D5/S0/Observation/Result.lean"
        standalone.write_json(path, {"schema": 1, "sources": {name: standalone.sha(self.dest / name)}})
        subprocess.run(["git", "add", "."], cwd=self.dest, check=True)
        subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                        "commit", "--quiet", "-m", "frozen fixture"], cwd=self.dest, check=True)
        standalone.write_json(path, {"schema": 1, "sources": {}})
        with self.assertRaisesRegex(ValueError, "committed source protection removed"):
            standalone.protect(self.dest)


if __name__ == "__main__":
    unittest.main()
