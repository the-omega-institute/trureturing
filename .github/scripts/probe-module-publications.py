"""Exercise the installed module publishers and read their output on a clean runner."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

TOOL_ROOT = Path.cwd()
sys.path.insert(0, str(TOOL_ROOT / "tools/scripts/worktree"))
from lean_artifact_inventory import Module
from lean_module_remote import json_body
from lean_module_shards import restore_shard
from test_lean_module_cache import MemoryRemote, ModuleReleases


def run(*args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def produce(directory):
    source = directory / "source"
    source.mkdir(parents=True)
    test = ModuleReleases("test_reports_publish_and_retry_from_compiler_only_artifacts")
    setup = test.setUp

    def setup_source():
        setup()
        for name in ("D5", "Other"):
            shutil.copytree(test.root / name, source / name)
        for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
            shutil.copyfile(test.root / name, source / name)
        empty = {"include": [], "exclude": []}
        def required(*names):
            return {"include": [{"pattern": n, "optional": False} for n in names], "exclude": []}
        config = dict(schema_version=1, report_modules=required("D5/A.lean"),
                      inspector_sources=empty, config_inputs=empty, producer_scopes={
                          "lean-report": required("lean-report-inputs.json", "tools/scripts/report/lean-report-selection.py"),
                          "scribe-content": empty})
        (source / "lean-report-inputs.json").write_bytes(json_body(config))
        run("git", "init", "--quiet", str(source))
        run("git", "add", ".", cwd=source)
        run("git", "-c", "user.name=Publication fixture", "-c", "user.email=fixture@example.invalid",
            "commit", "-qm", "Build the three-module Lake fixture", cwd=source)
        test.source = run("git", "rev-parse", "HEAD", cwd=source)
        run("git", "bundle", "create", str(directory / "source.bundle"), "HEAD", cwd=source)

    publish = MemoryRemote.publish
    def export(remote, index):
        publish(remote, index)
        folder = directory / index["version"]
        folder.mkdir()
        (folder / "index.json").write_bytes(json_body(index))
        for row in index["shards"].values():
            data = remote.assets[row["version"], row["asset"]]
            assert hashlib.sha256(data).hexdigest() == row["sha256"]
            (folder / row["asset"]).write_bytes(data)
        print(f'Published {index["kind"]} {index["version"]}, targets={len(index["targets"])} shards={len(index["shards"])}',
              flush=True)

    test.setUp = setup_source
    with patch.object(MemoryRemote, "publish", export):
        suite = unittest.TestSuite([test])
        if not unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful():
            raise RuntimeError("module publication fixture failed")
    shutil.rmtree(source)


def consume(directory, reader, issuer):
    with tempfile.TemporaryDirectory() as temporary:
        fixture = Path(temporary) / "checkout"
        run("git", "clone", "--quiet", "--no-checkout", str(directory / "source.bundle"), str(fixture))
        source = run("git", "bundle", "list-heads", str(directory / "source.bundle"), "HEAD").split()[0]
        run("git", "checkout", "--quiet", "--detach", source, cwd=fixture)
        assert source == run("git", "rev-parse", "HEAD", cwd=fixture)
        version = f"lean-modules-{source}"
        compiler = json.loads((directory / version / "index.json").read_bytes())
        assert compiler["kind"] == "compiler" and compiler["source"] == source
        name = "D5.A"
        inputs = {name: Module("trureturing", Path("D5/A.lean"), Path("."))}
        row = compiler["shards"][compiler["targets"][name]["shard"]]
        output = fixture / ".lake/build"
        restored = restore_shard(directory / row["version"] / row["asset"], row, [name], inputs, output,
                                 root=fixture, kind="compiler")
        assert restored == {name} and (output / "lib/lean/D5/A.olean").is_file()
        assert not (output / "lean-inspector").exists()
        report_dir = output / "lean-inspector/modules"
        subprocess.run([sys.executable, "-B", reader, directory.as_uri(), version + "-report", report_dir],
                       cwd=fixture, check=True)
        assert [p.name for p in report_dir.iterdir()] == [name + ".zip"]
        # The fixed Truth publisher imports the source-pinned Inspector modules.
        for part in ("lean-inspector", "scripts/report"):
            shutil.copytree(TOOL_ROOT / "tools" / part, fixture / "tools" / part,
                            ignore=shutil.ignore_patterns(".lake", "__pycache__", "bin", "obj"))
        report = fixture / "report.json"
        subprocess.run([sys.executable, "-B", issuer, report], cwd=fixture, check=True)
        aggregate = json.loads(report.read_bytes())
        item, = aggregate["modules"]
        assert item["module"] == name and len(item["declarations"]) > 0
        digest = "sha256:" + hashlib.sha256((fixture / "D5/A.lean").read_bytes()).hexdigest()
        assert item["source_sha256"] == digest
        print(f"Clean compiler restore=1, report archive=1, canonical aggregate=1, source={source}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["produce", "consume"])
    parser.add_argument("directory", type=Path)
    parser.add_argument("--reader", type=Path)
    parser.add_argument("--issuer", type=Path)
    args = parser.parse_args()
    if args.phase == "produce":
        produce(args.directory.resolve())
    else:
        consume(args.directory.resolve(), args.reader.resolve(), args.issuer.resolve())
