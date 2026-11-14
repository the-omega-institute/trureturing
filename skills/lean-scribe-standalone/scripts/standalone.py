#!/usr/bin/env python3
"""Export a source-only Lean/Scribe workspace and run its scoped upstream tools."""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile

UPSTREAM_COMMIT = "0826c2f31d52656aa8b51ccc676896bc7693fad7"
UPSTREAM_URL = "https://github.com/the-omega-institute/trureturing.git"
MODULE = re.compile(r"D5(?:\.[A-Za-z_][A-Za-z0-9_']*)+|Reg(?:\.[A-Za-z_][A-Za-z0-9_']*)+")
ROOT_FILES = {".editorconfig", ".gitignore", "Directory.Build.props", "Directory.Packages.props",
              "Directory.Build.targets", "global.json", "lean-toolchain", "lakefile.toml",
              "lake-manifest.json", "lean-report-inputs.json", "LICENSE", "NOTICE"}
EXCLUDED = ("tools/tests/", "tools/TestSupport/", "tools/scripts/agent/",
            "tools/lean-inspector/LeanInformationAuditRegTests/",
            "tools/lean-inspector/LeanInformationAuditFibTests/",
            "tools/lean-inspector/LeanInformationAuditRegAnalysis/")
ENVIRONMENT = {"MATHLIB_NO_CACHE_ON_UPDATE": "1", "DOTNET_EnableDiagnostics": "0"}


def run(argv, cwd=None, *, capture=False, env=None):
    return subprocess.run([str(a) for a in argv], cwd=cwd,
                          env=env or {**os.environ, **ENVIRONMENT}, check=True,
                          stdout=subprocess.PIPE if capture else None,
                          text=capture).stdout


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    data = json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent, delete=False) as stream:
        temporary = Path(stream.name)
        stream.write(data)
    temporary.replace(path)


def source_closure(read, files, seeds):
    pending, found = list(seeds), set()
    while pending:
        path = pending.pop()
        if path in found:
            continue
        if path not in files:
            raise ValueError("missing upstream source: " + path)
        found.add(path)
        # Upstream's pinned source uses ordinary, single-line import commands.
        for line in read(path).decode("utf-8").splitlines():
            if not line.startswith("import "):
                continue
            for name in line[7:].split():
                if name.startswith("--"):
                    break
                relative = name.replace(".", "/") + ".lean"
                matches = [prefix + relative for prefix in
                           ("", "tools/lean-inspector/", "tools/lean-inspector-interface/")
                           if prefix + relative in files]
                if matches:
                    pending.extend(matches)
                elif name.startswith(("D5.", "Reg.", "LeanInformationAudit", "Trureturing")):
                    raise ValueError("unresolved upstream import: " + name)
    return found


def initialize(args):
    if not re.fullmatch(r"[0-9a-f]{40}", args.revision):
        raise ValueError("--revision must be an immutable full 40-hex commit")
    if args.dest.exists() and any(args.dest.iterdir()):
        raise ValueError("destination must be absent or empty")
    if args.source is None:
        with tempfile.TemporaryDirectory(prefix="standalone-upstream-") as directory:
            source = Path(directory)
            run(["git", "init", "--quiet", source])
            run(["git", "-C", source, "remote", "add", "origin", UPSTREAM_URL])
            run(["git", "-C", source, "config", "remote.origin.promisor", "true"])
            run(["git", "-C", source, "config", "remote.origin.partialclonefilter", "blob:none"])
            run(["git", "-C", source, "fetch", "--quiet", "--depth=1", "--filter=blob:none", "origin", args.revision])
            args.source = source
            args.remote_source = True
            initialize(args)
        return
    source, dest = args.source.resolve(), args.dest.resolve()
    revision = run(["git", "rev-parse", "--verify", args.revision + "^{commit}"], source, capture=True).strip()
    if dest.exists() and any(dest.iterdir()):
        raise ValueError("destination must be absent or empty")
    files = set(run(["git", "ls-tree", "-r", "--name-only", revision], source, capture=True).splitlines())

    def read(path):
        return subprocess.check_output(["git", "show", revision + ":" + path], cwd=source)

    seeds = [p for p in files if p.startswith("tools/lean-inspector-interface/") and p.endswith(".lean")]
    for module in args.include:
        if not MODULE.fullmatch(module):
            raise ValueError("invalid included module: " + module)
        seeds.append(module.replace(".", "/") + ".lean")
    closure = source_closure(read, files, seeds)
    selected = {p for p in files if p in ROOT_FILES or
                p.startswith("tools/") and not p.startswith(EXCLUDED) or
                p.startswith("Meta/") and p.count("/") == 1 or
                p in {"Reg/lakefile.toml", "Reg/lake-manifest.json"}}
    selected |= closure
    primary = {name.removeprefix("Reg.").replace(".", "/") + ".lean" for name in args.include
               if name.startswith(("D5.", "Reg.D5."))}
    for path in closure:
        if not path.startswith("D5/"):
            continue
        related_paths = [] if path in primary else ["Golden/Frozen/state/" + path + ".json"]
        if path in primary:
            related_paths.append("Blueprint/" + path[:-5] + ".scribe.cs")
        for related in related_paths:
            if related in files:
                selected.add(related)
    # Export referenced notes, rather than the upstream literature collection.
    scribe_text = "\n".join(read(p).decode("utf-8") for p in selected if p.endswith(".scribe.cs"))
    selected |= {p for p in files if p.startswith("Library/") and p.endswith(".md")
                 and json.dumps(Path(p).stem) in scribe_text}
    selected = {p for p in selected if not {".lake", "bin", "obj", "__pycache__"}.intersection(Path(p).parts)}
    dest.mkdir(parents=True, exist_ok=True)
    if getattr(args, "remote_source", False):
        # Checkout batches missing blob retrieval; archive alone can fetch one
        # promised blob at a time. The temporary checkout contains this slice only.
        subprocess.run(["git", "sparse-checkout", "set", "--no-cone", "--stdin"], cwd=source,
                       input="".join("/" + p + "\n" for p in sorted(selected)), text=True, check=True)
        run(["git", "checkout", "--quiet", "--detach", revision], source)
    archive = subprocess.check_output(["git", "archive", "--format=tar", revision, "--", *sorted(selected)], cwd=source)
    with tarfile.open(fileobj=io.BytesIO(archive)) as bundle:
        if any(not (member.isfile() or member.isdir()) for member in bundle.getmembers()):
            raise ValueError("upstream source export contains a link or special file")
        bundle.extractall(dest, filter="data")
    (dest / "Blueprint").mkdir(exist_ok=True)
    (dest / "Trureturing.lean").write_text("-- Independent mathematical library.\n", encoding="utf-8")
    shutil.copyfile(Path(__file__).resolve(), dest / "formalize.py")
    assets = Path(__file__).resolve().parents[1] / "assets"
    if not assets.is_dir():
        assets = Path(__file__).resolve().parent / "standalone"
    (dest / "standalone").mkdir(exist_ok=True)
    for name in ("ScribeHost.cs", "ScribeHost.targets"):
        shutil.copyfile(assets / name, dest / "standalone" / name)
    # The standalone policy and runner are semantic build inputs.
    manifest_path = dest / "lean-report-inputs.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["producer_scopes"]["lean-report"]["include"].append({"pattern": "formalize.py", "optional": False})
    write_json(manifest_path, manifest)
    protected = {p: sha(dest / p) for p in selected if not p.startswith(("Blueprint/", "Library/"))}
    protected["Trureturing.lean"] = sha(dest / "Trureturing.lean")
    protected["formalize.py"] = sha(dest / "formalize.py")
    protected.update({"standalone/" + name: sha(dest / "standalone" / name)
                      for name in ("ScribeHost.cs", "ScribeHost.targets")})
    write_json(dest / "standalone-source.json", {"schema": 1, "upstream_commit": revision,
        "upstream_url": "https://github.com/the-omega-institute/trureturing", "protected": protected})
    write_json(dest / "standalone-frozen.json", {"schema": 1, "sources": {}})
    run(["git", "init", "--quiet"], dest)
    count = sum(1 for p in dest.rglob("*") if p.is_file() and ".git" not in p.parts)
    print(f"STANDALONE_INITIALIZED project={dest} files={count} upstream={revision}")


def project_root(value):
    root = value.resolve() if value else Path(__file__).resolve().parent
    if not (root / "standalone-source.json").is_file():
        raise ValueError("not an initialized standalone project: " + str(root))
    return root


@contextmanager
def writer_lock(root):
    name = run(["git", "rev-parse", "--git-path", "lean-scribe-standalone.lock"], root, capture=True).strip()
    path = Path(name)
    if not path.is_absolute():
        path = root / path
    with path.open("a") as stream:
        fcntl.flock(stream, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(stream, fcntl.LOCK_UN)


def protect(root):
    manifests = {}
    for filename, field in (("standalone-source.json", "protected"), ("standalone-frozen.json", "sources")):
        path = root / filename
        if not path.is_file() or path.is_symlink():
            raise ValueError("missing standalone protection manifest: " + filename)
        manifest = json.loads(path.read_text())
        if manifest.get("schema") != 1 or not isinstance(manifest.get(field), dict):
            raise ValueError("invalid standalone protection manifest: " + filename)
        manifests[filename] = manifest[field]
        # Committed protection may only grow. HEAD is data, never executed code.
        previous = subprocess.run(["git", "show", "HEAD:" + filename], cwd=root,
                                  capture_output=True, text=True)
        if previous.returncode == 0:
            old = json.loads(previous.stdout)[field]
            if any(manifest[field].get(name) != digest for name, digest in old.items()):
                raise ValueError("committed source protection removed or changed: " + filename)
        for name, expected in manifest[field].items():
            if Path(name).is_absolute() or ".." in Path(name).parts:
                raise ValueError("invalid protected source path: " + name)
            file = root / name
            if not file.is_file() or file.is_symlink() or sha(file) != expected:
                raise ValueError("protected source changed or missing: " + name)
    known = manifests["standalone-source.json"] | manifests["standalone-frozen.json"]
    for pin in (root / "Golden/Frozen/state").rglob("*.json"):
        name = pin.relative_to(root).as_posix()
        if name not in known:
            raise ValueError("frozen pin missing source protection: " + name)
        source = name.removeprefix("Golden/Frozen/state/").removesuffix(".json")
        if source not in known:
            raise ValueError("frozen module missing source protection: " + source)


def doctor(root):
    protect(root)
    for tool in ("git", "python3", "lake", "lean", "dotnet"):
        if not shutil.which(tool):
            raise ValueError("missing tool: " + tool)
    run(["python3", "-c", "import sys; assert sys.version_info >= (3, 12), sys.version"], root)
    version = run(["lean", "--version"], root, capture=True)
    expected = re.search(r":v([0-9]+\.[0-9]+\.[0-9]+)$", (root / "lean-toolchain").read_text().strip())
    if not expected or not version.startswith("Lean (version " + expected[1] + ","):
        raise ValueError("Lean executable does not match the pinned release: " + version.strip())
    print(version.strip(), flush=True)
    run(["dotnet", "--version"], root)
    if not run(["git", "rev-parse", "--is-inside-work-tree"], root, capture=True).strip() == "true":
        raise ValueError("project must be a Git worktree")
    print("STANDALONE_DOCTOR_OK")


def report(root, modules, name="standalone-scoped"):
    # Entry's scope discovery, report production and validation are upstream code.
    # Only the host's cache transportation wrapper is replaced for this new project.
    sys.path.insert(0, str(root / "tools/lean-inspector"))
    import scoped

    class ColdEntry(scoped.Entry):
        def guarded(self, *arguments):
            return [self.lake, "-d", str(self.root / "tools/lean-inspector-reg"), *arguments]

    output = root / (".lake/build/stratalint/" + name + ".json")
    output.parent.mkdir(parents=True, exist_ok=True)
    scoped.check_destination(root, output)
    scoped.public.member(output, ".input.attestation").unlink(missing_ok=True)
    with tempfile.TemporaryDirectory(prefix="standalone-report-") as directory:
        temporary = Path(directory)
        logs = output.parent / "standalone-logs"
        logs.mkdir(exist_ok=True)
        entry = ColdEntry(root, temporary, logs)
        entry.environment.update(ENVIRONMENT)
        entry.provision()
        scope, utilities = entry.discover(modules)
        scoped.produce(entry, output, scope, utilities)
    return output


def validate_current_report(root, output, modules):
    import scoped
    provenance = scoped.public.read_json(scoped.public.member(output, ".provenance.json").read_bytes())
    inputs = provenance["inputs"]
    scoped.check_scope(root, inputs["scope"], sorted(set(modules)))
    scoped.validate_bundle(output, root, inputs["scope"], utilities=inputs["utilities"])
    return inputs


def assert_files(root, expected):
    for name, digest in expected.items():
        path = root / name
        if not path.is_file() or path.is_symlink() or sha(path) != digest:
            raise ValueError("checked source changed or missing: " + name)


def check(root, modules):
    doctor(root)
    if not modules or any(not MODULE.fullmatch(name) for name in modules):
        raise ValueError("explicit D5/Reg module roots are required")
    # No lake update, cache get, donor, release or shared-cache admission occurs here.
    output = report(root, sorted(set(modules)))
    scribe = root / "tools/StrataLint.Scribe/StrataLint.Scribe.csproj"
    paths = ["Blueprint/" + name.replace(".", "/") + ".scribe.cs" for name in modules if name.startswith("D5.")]
    for path in paths:
        if not (root / path).is_file():
            raise ValueError("missing Scribe source: " + path)
    scribe_inputs = {path: sha(root / path) for path in paths}
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", prefix="standalone-paths-", delete=False) as stream:
        path_file = Path(stream.name)
        stream.write("\n".join(paths) + "\n")
    roots_file = Path(str(path_file) + ".roots")
    roots_file.write_text("\n".join(name.replace(".", "/") + ".lean" for name in sorted(set(modules))) + "\n")
    try:
        env = {**os.environ, **ENVIRONMENT, "STRATALINT_LEAN_REPORT": str(output),
               "SCRIBE_DOTNET": str(Path(shutil.which("dotnet")).resolve())}
        common = ["dotnet", "run", "--project", scribe, "--configuration", "Release",
                  "--property", "DirectoryBuildTargetsPath=" + str(root / "standalone/ScribeHost.targets"), "--"]
        run([*common, "emit", output, path_file, roots_file], root, env=env)
        run([*common, "check", output, path_file, roots_file], root, env=env)
        run([*common, "audit", output, path_file, roots_file], root, env=env)
    finally:
        path_file.unlink(missing_ok=True)
        roots_file.unlink(missing_ok=True)
    protect(root)
    assert_files(root, scribe_inputs)
    scribe_inputs.update({path.removesuffix(".scribe.cs") + ".md":
                         sha(root / (path.removesuffix(".scribe.cs") + ".md")) for path in paths})
    validate_current_report(root, output, modules)
    print("STANDALONE_CHECK_OK report=" + str(output))
    return output, scribe_inputs


def freeze(root, modules):
    output, scribe_inputs = check(root, modules)
    # Schema and full certificates have already been verified by scoped.produce.
    data = json.loads(output.read_text())
    selected = {name.replace(".", "/") + ".lean" for name in modules if name.startswith("D5.")}
    if not selected:
        raise ValueError("freeze requires a mathematical D5 module")
    mathematical = sorted(name for name in modules if name.startswith("D5."))
    # The upstream writer consumes the exact mathematical scope, which excludes
    # the additional imports needed only by Reg's audit proofs.
    freeze_report = report(root, mathematical, "standalone-freeze")
    audit_inputs = validate_current_report(root, output, modules)
    assert_files(root, scribe_inputs)
    cli = root / "tools/StrataLint.Cli/StrataLint.Cli.csproj"
    for path in sorted(selected):
        pin = root / "Golden/Frozen/state" / (path + ".json")
        if pin.exists():
            raise ValueError("already frozen; this path only adds modules: " + path)
    run(["dotnet", "build", cli, "--configuration", "Release", "--nologo", "--verbosity", "quiet"], root)
    arguments = ["dotnet", "run", "--no-build", "--project", cli, "--configuration", "Release", "--", "ledger-align"]
    for path in sorted(selected):
        arguments.extend(["--add", path])
    new_pins = [root / "Golden/Frozen/state" / (path + ".json") for path in selected]
    try:
        run([*arguments, "--candidate-lean-report", freeze_report], root)
        validate_current_report(root, output, modules)
        assert_files(root, scribe_inputs)
        frozen = root / "standalone-frozen.json"
        state = json.loads(frozen.read_text())
        members = {row["source_path"] for row in data["modules"]}
        state["sources"].update({name: audit_inputs["files"][name] for name in sorted(members)})
        state["sources"].update(scribe_inputs)
        state["sources"].update({str(path.relative_to(root)): sha(path) for path in new_pins})
        write_json(frozen, state)
    except BaseException:
        for pin in new_pins:
            pin.unlink(missing_ok=True)
        raise
    print("STANDALONE_FROZEN modules=" + str(len(selected)))


def main():
    if sys.version_info < (3, 12):
        raise ValueError("Python >=3.12 is required")
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    init = commands.add_parser("init")
    init.add_argument("--source", type=Path, help="optional local upstream Git source; otherwise fetch the public pin")
    init.add_argument("--revision", default=UPSTREAM_COMMIT)
    init.add_argument("--dest", type=Path, required=True)
    init.add_argument("--include", action="append", default=[])
    for name in ("doctor", "check", "freeze"):
        sub = commands.add_parser(name)
        sub.add_argument("--project", type=Path)
        if name != "doctor":
            sub.add_argument("--module", action="append", required=True)
    args = parser.parse_args()
    if args.command == "init":
        initialize(args)
    else:
        root = project_root(args.project)
        if args.command == "doctor":
            doctor(root)
        else:
            with writer_lock(root):
                {"check": check, "freeze": freeze}[args.command](root, args.module)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, subprocess.CalledProcessError) as error:
        print("STANDALONE_FAILED: " + str(error), file=sys.stderr)
        sys.exit(1)
