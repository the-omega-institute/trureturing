"""Exercise contribution scope against real Git baseline/worktree changes."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

ENTRY = Path(__file__).resolve().parents[1] / "scripts/check.py"
SPEC = importlib.util.spec_from_file_location("fork_check", ENTRY)
fork_check = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(fork_check)


class ScopeTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="fork scope ")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.git("init", "--quiet")
        self.write("D5/Old.lean", "theorem historical : True := .intro\n")
        self.write("Blueprint/D5/Old.scribe.cs", "fixture")
        self.git("add", ".")
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                 "commit", "--quiet", "-m", "baseline")
        self.base = self.git("rev-parse", "HEAD").strip()

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, text=True)

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def test_committed_and_untracked_contributions_share_protected_base(self):
        self.write("D5/Old.lean", "theorem historical : True := .intro\ndef added := 1\n")
        self.git("add", "D5/Old.lean")
        self.git("-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                 "commit", "--quiet", "-m", "contribution")
        self.write("D5/New.lean", "def fresh := 2\n")
        self.write("Blueprint/D5/New.scribe.cs", "fixture")
        self.write("Reg/D5/New.lean", "import D5.New\n")
        self.write("scratch.txt", "unrelated")
        roots, paths = fork_check.select(self.root, self.base, [])
        self.assertEqual(roots, ["D5/New.lean", "D5/Old.lean", "Reg/D5/New.lean"])
        self.assertIn("Blueprint/D5/Old.scribe.cs", paths)
        self.assertNotIn("scratch.txt", paths)

    def test_explicit_unchanged_module_includes_its_registration(self):
        self.write("Reg/D5/Old.lean", "import D5.Old\n")
        roots, _ = fork_check.select(self.root, self.base, ["D5.Old"])
        self.assertEqual(roots, ["D5/Old.lean", "Reg/D5/Old.lean"])

    def test_registration_only_change_includes_mathematical_owner_and_scribe(self):
        self.write("Reg/D5/Old.lean", "import D5.Old\n")
        for modules in ([], ["Reg.D5.Old"]):
            roots, paths = fork_check.select(self.root, self.base, modules)
            self.assertEqual(roots, ["D5/Old.lean", "Reg/D5/Old.lean"])
            self.assertIn("Blueprint/D5/Old.scribe.cs", paths)

    def test_missing_scribe_and_deleted_lean_fail_before_build(self):
        self.write("D5/New.lean", "def fresh := 2\n")
        with self.assertRaisesRegex(ValueError, "missing Blueprint"):
            fork_check.select(self.root, self.base, [])
        (self.root / "D5/New.lean").unlink()
        (self.root / "D5/Old.lean").unlink()
        with self.assertRaisesRegex(ValueError, "missing/deleted"):
            fork_check.select(self.root, self.base, [])

    def test_empty_and_wildcard_targets_cannot_become_full_build(self):
        with self.assertRaisesRegex(ValueError, "no Lean targets"):
            fork_check.select(self.root, self.base, [])
        for invalid in ("", "D5", "Reg", "D5.*", "D5.Foo;other", "../D5.Foo"):
            with self.assertRaises(ValueError):
                fork_check.lean_path(invalid)


if __name__ == "__main__":
    unittest.main()
