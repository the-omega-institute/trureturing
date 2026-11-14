"""Shared synthetic repository setup for Lean seed behavior contracts."""
import hashlib
import json
import os
import pathlib
import subprocess
import tempfile
import sys
import shutil
import zipfile

ROOT = pathlib.Path(__file__).resolve().parents[4]
INPUT = ROOT / "tools/scripts/worktree/lean-cache-input.sh"
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
        write(self.root / "Meta/FILEMAP.toml", 'files = [{pattern = "Meta/ci-cache-paths.json"}]\n')
        write(self.root / "Meta/ci-cache-paths.json", (ROOT / "Meta/ci-cache-paths.json").read_text())

    def save_manifest(self):
        write(self.root / "lake-manifest.json", json.dumps(self.manifest))

    def run_input(self, command, *extra, env=None):
        return subprocess.run(["bash", str(INPUT), command, "--repository", str(self.root), *extra],
                              text=True, capture_output=True, env={**os.environ, **(env or {})})

    def partition(self):
        result = self.run_input("partition")
        self.assertEqual(0, result.returncode, result.stderr)
        return result.stdout.strip()


def prepare_release_report(root):
    """Canonical synthetic bundle for Release transport's existing strict reader."""
    for directory, names in (("tools/lean-inspector", ("reuse.py", "publication.py", "materials.py")),
                             ("tools/scripts/report", ("lean-report-selection.py", "lean-report-input.sh"))):
        target = root / directory
        target.mkdir(parents=True, exist_ok=True)
        for name in names:
            shutil.copy2(ROOT / directory / name, target / name)
    paths = lambda *names: dict(include=[dict(pattern=name, optional=False) for name in names], exclude=[])
    sources = ["Trureturing.lean", *sorted(p.relative_to(root).as_posix() for p in (root / "D5").rglob("*.lean"))]
    configs = [name for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json") if (root / name).is_file()]
    write(root / "lean-report-inputs.json", json.dumps(dict(schema_version=1,
        report_execution=dict(toolchain="lean-toolchain", tools=["lake", "lean"], platform=["system", "machine"],
            environment=["LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "ELAN_TOOLCHAIN", "LEAN_OPTS"]),
        report_modules=paths(*sources), inspector_sources=paths(), config_inputs=paths(*configs),
        producer_scopes={"lean-report": paths("lean-report-inputs.json", "tools/scripts/report/lean-report-selection.py"),
                         "scribe-content": paths()})))


def write_release_report(root):
    sys.path.insert(0, str(root / "tools/lean-inspector"))
    import reuse
    publication, materials = reuse.publication, reuse.materials
    captured = reuse.capture(root)
    report = root / ".lake/build/stratalint/raw-lean-report.json"
    try:
        reuse.read_receipt(report, captured)
        return
    except reuse.INVALID_SEED:
        pass
    report.parent.mkdir(parents=True, exist_ok=True)
    rows = [dict(module=name, source_path=path, source_sha256="sha256:" + publication.digest(root / path),
                 imports=[], declarations=[]) for name, path in sorted(publication.selection.Selection(root).modules().items())]
    report.write_bytes(materials.canonical_json(dict(schema=publication.selection.REPORT_FORMAT, modules=rows)))
    with zipfile.ZipFile(publication.member(report, ".materials.zip"), "w"):
        pass
    origins = {row["module"]: dict(module=row["module"],
        report_sha256=digest(materials.canonical_json(dict(schema=materials.REPORT_SCHEMA, modules=[row]))),
        input_projection=dict(schema="stratalint-judge-input-projection-v1", module=row["module"], inputs=[]),
        producer_sources_sha256="a" * 64, inspector_executable_sha256="b" * 64) for row in rows}
    producer, sources, config = "c" * 64, "d" * 64, "e" * 64
    coordinates = subprocess.check_output([str(root / "tools/scripts/report/lean-report-input.sh"), "coordinates",
        producer, producer, sources, config], text=True).strip().split()
    publication.write_sidecars(report, dict(input=coordinates[0], repository=coordinates[1],
        producer=producer, sources=sources, config=config), origins)
    publication.validate_bundle(report, repository=root)
    reuse.write_receipt(report, captured)


if __name__ == "__main__":
    root = pathlib.Path(sys.argv[2])
    if sys.argv[1] == "prepare-release-report":
        prepare_release_report(root)
    else:
        # The canonical report entry owns a writer lock; the tiny fake producer
        # needs the same serialization while it writes a multi-file bundle.
        import fcntl
        with (root / ".fixture-report.lock").open("a+b") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            write_release_report(root)
