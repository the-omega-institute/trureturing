#!/usr/bin/env python3
"""Run the fork's canonical scoped producers and its own validation APIs."""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


def run(arguments, root, *, env=None, capture=False, check=True):
    return subprocess.run(arguments, cwd=root, env=env, check=check,
                          stdout=subprocess.PIPE if capture else None,
                          text=capture)


def git(root, *arguments):
    return run(["git", *arguments], root, capture=True).stdout


def lean_path(module):
    if not re.fullmatch(r"(?:D5|Reg)(?:\.[A-Za-z_][A-Za-z_0-9]*)+", module):
        raise ValueError("expected an explicit D5/Reg dotted module: " + module)
    return module.replace(".", "/") + ".lean"


def select(root, base, modules):
    changed = set(git(root, "diff", "--name-only", "-z", base, "--").split("\0"))
    changed.update(git(root, "ls-files", "--others", "--exclude-standard", "-z").split("\0"))
    changed.discard("")
    roots = {lean_path(module) for module in modules}
    roots.update(path for path in changed
                 if path.startswith(("D5/", "Reg/")) and path.endswith(".lean"))
    roots.update(path.removeprefix("Reg/") for path in list(roots)
                 if path.startswith("Reg/D5/") and (root / path.removeprefix("Reg/")).is_file())
    for path in sorted(roots):
        if not (root / path).is_file():
            raise ValueError("missing/deleted Lean input requires separate review: " + path)
        mirror = "Reg/" + path
        if path.startswith("D5/") and (root / mirror).is_file():
            roots.add(mirror)
    if not roots:
        raise ValueError("no Lean targets; specify --module or change D5/Reg sources")
    paths = set(roots)
    for path in sorted(roots):
        if path.startswith("D5/"):
            scribe = "Blueprint/" + path.removesuffix(".lean") + ".scribe.cs"
            if not (root / scribe).is_file():
                raise ValueError("missing Blueprint Scribe: " + scribe)
            paths.add(scribe)
    paths.update(path for path in changed if path.startswith("Blueprint/")
                 and path.endswith((".scribe.cs", ".md")))
    return sorted(roots), sorted(paths)


def check(args):
    root = Path(git(args.repository, "rev-parse", "--show-toplevel").strip()).resolve()
    git_dir = Path(git(root, "rev-parse", "--absolute-git-dir").strip()).resolve()
    common = Path(git(root, "rev-parse", "--path-format=absolute", "--git-common-dir").strip()).resolve()
    if git_dir == common:
        raise ValueError("use a linked worktree; main checkouts may restore the project archive")
    base = git(root, "rev-parse", "--verify", args.base + "^{commit}").strip()
    run(["git", "merge-base", "--is-ancestor", base, "HEAD"], root)
    roots, paths = select(root, base, args.module)
    assets = Path(__file__).resolve().parents[1] / "assets"
    environment = os.environ.copy()
    dotnet = shutil.which("dotnet")
    if not dotnet:
        raise ValueError("install the .NET SDK selected by the fork's global.json")
    environment["SCRIBE_DOTNET"] = str(Path(dotnet).resolve())
    with tempfile.TemporaryDirectory(prefix="lean-fork-check-") as directory:
        scratch = Path(directory)
        manifest = scratch / "paths.nul"
        manifest.write_bytes(b"\0".join(path.encode() for path in paths) + b"\0")
        scribe_inputs = []
        if any(path.endswith(".scribe.cs") for path in paths):
            run(["make", "emit", "BASE=" + base, "PATHS=" + str(manifest)], root, env=environment)
            scribe_dll = root / "tools/StrataLint.Scribe/bin/Release/net10.0/StrataLint.Scribe.dll"
            scribe_inputs = run([dotnet, str(scribe_dll), "lean-inputs", "--paths-from", str(manifest)],
                                root, env=environment, capture=True).stdout.splitlines()
        roots = sorted(set(roots) | {lean_path(module) for module in scribe_inputs})
        targets = " ".join(path.removesuffix(".lean").replace("/", ".") for path in roots)
        run(["make", "lean-report-prepare", "LEAN_TARGETS=" + targets], root, env=environment)
        run(["make", "lean-report-scoped", "LEAN_TARGETS=" + targets], root, env=environment)
        baseline = scratch / "baseline"
        for path in roots:
            old = run(["git", "show", base + ":" + path], root, capture=True, check=False)
            if old.returncode == 0:
                target = baseline / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(old.stdout)
        request = scratch / "request.json"
        request.write_text(json.dumps({
            "Report": str(root / ".lake/build/stratalint/scoped-lean-report.json"),
            "Paths": paths, "Roots": roots, "Baseline": str(baseline),
        }))
        source = scratch / "ScopedHost.cs"
        shutil.copyfile(assets / "ScopedHost.cs.template", source)
        artifacts = scratch / "artifacts"
        run([dotnet, "build", "tools/StrataLint.Scribe/StrataLint.Scribe.csproj",
             "--configuration", "Release", "--nologo", "--verbosity", "quiet",
             "--artifacts-path", str(artifacts),
             "-p:DirectoryBuildTargetsPath=" + str(assets / "ScopedHost.targets"),
             "-p:ForkScopedHostSource=" + str(source)], root, env=environment)
        host = artifacts / "bin/StrataLint.Scribe/release/StrataLint.Scribe.dll"
        run([dotnet, str(host), str(request)], root, env=environment)
    print("FORK_CHECK_OK base=" + base + " targets=" + targets)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path, default=Path.cwd())
    parser.add_argument("--base", required=True, help="protected upstream commit, not the contribution HEAD")
    parser.add_argument("--module", action="append", default=[], help="explicit D5/Reg dotted module")
    args = parser.parse_args()
    if sys.version_info < (3, 12):
        parser.error("Python 3.12 or newer is required")
    try:
        check(args)
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print("FORK_CHECK_FAILED: " + str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
