#!/usr/bin/env python3
"""Export a source-only Lean/Scribe workspace and run its scoped upstream tools."""
from __future__ import annotations

import argparse
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
                elif not name.startswith(("Mathlib.", "Lean", "Std", "Init", "Batteries", "Qq", "Aesop")):
                    raise ValueError("unresolved upstream import: " + name)
    return found


def initialize(args):
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
    for path in closure:
        if not path.startswith("D5/"):
            continue
        for related in ("Golden/Frozen/state/" + path + ".json",
                        "Blueprint/" + path[:-5] + ".scribe.cs"):
            if related in files:
                selected.add(related)
    # Cited upstream literature is reference input, not another truth source.
    selected |= {p for p in files if p.startswith("Library/")}
    selected |= {p for p in files if p.startswith("Golden/Projection/")}
    dest.mkdir(parents=True, exist_ok=True)
    archive = subprocess.check_output(["git", "archive", "--format=tar", revision, "--", *sorted(selected)], cwd=source)
    with tarfile.open(fileobj=io.BytesIO(archive)) as bundle:
        if any(not (member.isfile() or member.isdir()) for member in bundle.getmembers()):
            raise ValueError("upstream source export contains a link or special file")
        bundle.extractall(dest, filter="data")
    (dest / "Blueprint").mkdir(exist_ok=True)
    (dest / "Trureturing.lean").write_text("-- Independent mathematical library.\n", encoding="utf-8")
    shutil.copyfile(Path(__file__).resolve(), dest / "formalize.py")
    # The standalone policy and runner are semantic build inputs.
    manifest_path = dest / "lean-report-inputs.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["producer_scopes"]["lean-report"]["include"].append({"pattern": "formalize.py", "optional": False})
    write_json(manifest_path, manifest)
    protected = {p: sha(dest / p) for p in selected if not p.startswith(("Blueprint/", "Library/", "Golden/"))}
    protected["Trureturing.lean"] = sha(dest / "Trureturing.lean")
    protected["formalize.py"] = sha(dest / "formalize.py")
    write_json(dest / "standalone-source.json", {"schema": 1, "upstream_commit": revision,
        "upstream_url": "https://github.com/the-omega-institute/trureturing", "protected": protected})
    run(["git", "init", "--quiet"], dest)
    count = sum(1 for p in dest.rglob("*") if p.is_file() and ".git" not in p.parts)
    print(f"STANDALONE_INITIALIZED project={dest} files={count} upstream={revision}")


def project_root(value):
    root = value.resolve() if value else Path(__file__).resolve().parent
    if not (root / "standalone-source.json").is_file():
        raise ValueError("not an initialized standalone project: " + str(root))
    return root


def protect(root):
    for filename, field in (("standalone-source.json", "protected"), ("standalone-frozen.json", "sources")):
        path = root / filename
        if not path.exists():
            if filename == "standalone-source.json":
                raise ValueError("missing standalone source pin")
            continue
        for name, expected in json.loads(path.read_text())[field].items():
            file = root / name
            if not file.is_file() or file.is_symlink() or sha(file) != expected:
                raise ValueError("protected source changed or missing: " + name)


def doctor(root):
    protect(root)
    for tool in ("git", "python3", "lake", "lean", "dotnet"):
        if not shutil.which(tool):
            raise ValueError("missing tool: " + tool)
    run(["lean", "--version"], root)
    run(["dotnet", "--version"], root)
    if not run(["git", "rev-parse", "--is-inside-work-tree"], root, capture=True).strip() == "true":
        raise ValueError("project must be a Git worktree")
    print("STANDALONE_DOCTOR_OK")


def report(root, modules):
    # Entry's scope discovery, report production and validation are upstream code.
    # Only the host's cache transportation wrapper is replaced for this new project.
    sys.path.insert(0, str(root / "tools/lean-inspector"))
    import scoped

    class ColdEntry(scoped.Entry):
        def guarded(self, *arguments):
            return [self.lake, "-d", str(self.root / "tools/lean-inspector-reg"), *arguments]

    output = root / ".lake/build/stratalint/standalone-scoped.json"
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
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", prefix="standalone-paths-", delete=False) as stream:
        path_file = Path(stream.name)
        stream.write("\n".join(paths) + "\n")
    try:
        env = {**os.environ, **ENVIRONMENT, "STRATALINT_LEAN_REPORT": str(output)}
        run(["dotnet", "run", "--project", scribe, "--configuration", "Release", "--",
             "emit", "--paths-from", path_file, "--scoped"], root, env=env)
    finally:
        path_file.unlink(missing_ok=True)
    protect(root)
    print("STANDALONE_CHECK_OK report=" + str(output))
    return output


def freeze(root, modules):
    output = check(root, modules)
    # Schema and full certificates have already been verified by scoped.produce.
    data = json.loads(output.read_text())
    selected = {name.replace(".", "/") + ".lean" for name in modules if name.startswith("D5.")}
    if not selected:
        raise ValueError("freeze requires a mathematical D5 module")
    targets = [row for row in data["modules"] if row["source_path"] in selected]
    require_audits(targets, data["modules"])
    cli = root / "tools/StrataLint.Cli/StrataLint.Cli.csproj"
    for path in sorted(selected):
        pin = root / "Golden/Frozen/state" / (path + ".json")
        if pin.exists():
            raise ValueError("already frozen; this path only adds modules: " + path)
    run(["dotnet", "build", cli, "--configuration", "Release", "--nologo", "--verbosity", "quiet"], root)
    arguments = ["dotnet", "run", "--no-build", "--project", cli, "--configuration", "Release", "--", "ledger-align"]
    for path in sorted(selected):
        arguments.extend(["--add", path])
    run([*arguments, "--candidate-lean-report", output], root)
    frozen = root / "standalone-frozen.json"
    state = json.loads(frozen.read_text()) if frozen.exists() else {"schema": 1, "sources": {}}
    members = {row["source_path"] for row in data["modules"]}
    members |= {"Blueprint/" + path[:-5] + suffix for path in selected for suffix in (".scribe.cs", ".md")}
    members |= {"Golden/Frozen/state/" + path + ".json" for path in selected}
    state["sources"].update({name: sha(root / name) for name in sorted(members)})
    write_json(frozen, state)
    print("STANDALONE_FROZEN modules=" + str(len(selected)))


def require_audits(targets, rows):
    """Select only current canonical binding certificates; never infer validity."""
    if not targets:
        raise ValueError("no target modules in current report")
    records = [record for row in rows for record in row.get("information_templates", {}).get("records", [])]
    for row in targets:
        theorems = [d["name"] for d in row["declarations"] if d["kind"] == "theorem" and d["include_in_statement"]]
        for name in theorems:
            if not any(r["key"]["theorem"] == name and r["state"] == "declared_validated" and r["certificate"]
                       for r in records):
                raise ValueError("escape audit unfinished: " + name)


def main():
    if sys.version_info < (3, 12):
        raise ValueError("Python >=3.12 is required")
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    init = commands.add_parser("init")
    init.add_argument("--source", type=Path, required=True)
    init.add_argument("--revision", required=True)
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
            {"check": check, "freeze": freeze}[args.command](root, args.module)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, subprocess.CalledProcessError) as error:
        print("STANDALONE_FAILED: " + str(error), file=sys.stderr)
        sys.exit(1)
