"""Shared synthetic repository setup for Lean seed behavior contracts."""
import hashlib
import json
import os
import pathlib
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[4]
INPUT = ROOT / "tools/scripts/worktree/lean-cache-input.sh"
DELTA = ROOT / "tools/lean-inspector/delta.py"
REV = "0123456789abcdef0123456789abcdef01234567"
OTHER = "f" * 40
PUBLISH = ROOT / "tools/scripts/worktree/lean-cache-publish.sh"


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(value, encoding="utf-8")


def digest(value):
    return hashlib.sha256(value).hexdigest()


class PartitionFixture:
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = pathlib.Path(self.temporary.name)
        self.manifest = {"packages": [{"name": "mathlib", "rev": REV, "inputRev": "v1"}]}
        self.save_manifest()
        write(self.root / "lean-toolchain", "leanprover/lean4:v4.33.0\n")
        write(self.root / "lakefile.toml", 'name = "fixture"\n[leanOptions]\nmaxRecDepth = 1000\n')
        write(self.root / "Trureturing.lean", "import D5.A\n")
        write(self.root / "D5/A.lean", "def a := 1\n")

    def save_manifest(self):
        write(self.root / "lake-manifest.json", json.dumps(self.manifest))

    def run_input(self, command, *extra, env=None):
        return subprocess.run(["bash", str(INPUT), command, "--repository", str(self.root), *extra],
                              text=True, capture_output=True, env={**os.environ, **(env or {})})

    def partition(self):
        result = self.run_input("partition")
        self.assertEqual(0, result.returncode, result.stderr)
        return result.stdout.strip()
