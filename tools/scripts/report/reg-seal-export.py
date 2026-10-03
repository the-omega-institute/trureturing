#!/usr/bin/env python3
"""Export numerical seals using the checkout's production assessment and analysis export.

Python 3.12+, GNU/BSD make, bash, dotnet and the pinned Lean/Lake toolchain
must be on PATH. Run from any directory:
  python3 tools/scripts/report/reg-seal-export.py --repository REPOSITORY
  python3 tools/scripts/report/reg-seal-export.py --repository REPOSITORY \
    --roots Reg.Catalogs.Example --output-dir EXTERNAL_DIRECTORY

Default discovery scans Reg for #seal_information_theory commands and
Reg/Catalogs/**/SealedCatalog.lean for typed Contract.Seal definitions. This is
source enumeration; the production producer checks the actual sealed root.
--list enumerates without building. --output-dir fixes the path prefix; otherwise
a fresh system temporary directory is retained. Output is sorted JSONL with root
and absolute artifact path, plus elapsed_seconds for completed exports. Build
logs, generated packages and real exit sentinels live alongside each artifact.
Existing seal files are removed before export, so a safe rerun cannot reuse stale
output. Roots run sequentially. Only current checkout code is built or executed.
Exit 64 denotes invalid inputs, 66 missing inputs/artifacts, 69 missing tools,
73 unavailable output; a failed make retains its exit code and names the root.
"""

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time


MODULE = re.compile(r"Reg(?:\.[A-Za-z_][A-Za-z_0-9']*)+")
SEAL_COMMAND = re.compile(r"(?<![\w'])#seal_information_theory(?![\w'])")
TYPED_SEAL = re.compile(r"\bdef\s+[\w'.]+(?:\.\{[^}]*\})?\s*:\s*"
                        r"(?:LeanInformationAuditInterface\.)?Contract\.Seal\s*:=")


class ExportError(Exception):
    def __init__(self, code, message):
        super().__init__(message)
        self.code = code


def source_code(text):
    """Erase nested comments and string literals, retaining token boundaries."""
    output, index, depth, string = [], 0, 0, False
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                index += 2
            else:
                index += 1
            output.append(" ")
        elif string:
            if text[index] == "\\":
                index += 2
            else:
                if text[index] == '"':
                    string = False
                index += 1
            output.append(" ")
        elif text.startswith("/-", index):
            depth = 1
            index += 2
            output.append(" ")
        elif text.startswith("--", index):
            end = text.find("\n", index)
            index = len(text) if end == -1 else end
            output.append(" ")
        elif text[index] == '"':
            string = True
            index += 1
            output.append(" ")
        else:
            output.append(text[index])
            index += 1
    return "".join(output)


def enumerate_roots(repository):
    roots = set()
    for path in sorted((repository / "Reg").rglob("*.lean")):
        relative = path.relative_to(repository)
        root = ".".join(relative.with_suffix("").parts)
        code = source_code(path.read_text(encoding="utf-8"))
        old = SEAL_COMMAND.search(code) is not None
        typed = relative.parts[:2] == ("Reg", "Catalogs") and path.name == "SealedCatalog.lean"
        if typed and not TYPED_SEAL.search(code) and not old:
            raise ExportError(66, f"MissingTypedSeal root={root}")
        if old or typed:
            if not MODULE.fullmatch(root):
                raise ExportError(64, f"InvalidRoot root={root}")
            roots.add(root)
    return sorted(roots)


def select_roots(repository, requested):
    for root in requested or []:
        if not MODULE.fullmatch(root):
            raise ExportError(64, f"InvalidRoot root={root}")
        if not (repository / (root.replace(".", "/") + ".lean")).is_file():
            raise ExportError(66, f"MissingRoot root={root}")
    if requested and len(set(requested)) != len(requested):
        raise ExportError(64, "DuplicateRoot")
    inventory = enumerate_roots(repository)
    for root in requested or []:
        if root not in inventory:
            raise ExportError(66, f"UnsealedRoot root={root}")
    roots = sorted(requested) if requested else inventory
    if not roots:
        raise ExportError(66, "NoSealedRoots")
    return roots


def check_export(root, code, artifact):
    if code != 0:
        raise ExportError(code if code > 0 else 128 - code,
                          f"ExportFailed root={root} exit={code}")
    if not artifact.is_file():
        raise ExportError(66, f"MissingSealArtifact root={root} path={artifact}")
    try:
        value = json.loads(artifact.read_text(encoding="utf-8"))
        if not (isinstance(value, dict) and
                value.get("schema") == "lean-intrinsic-information-escape-seal" and
                value.get("catalog_mode") == "single-compilation-leave-one-out" and
                isinstance(value.get("arenas"), list) and value["arenas"]):
            raise ValueError("missing seal schema or arenas")
    except (ValueError, OSError) as error:
        raise ExportError(66, f"InvalidSealArtifact root={root} path={artifact}: {error}") from error


def validate_build(repository):
    inputs = ["Makefile", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
              "Reg/lakefile.toml", "Reg/lake-manifest.json",
              "tools/lean-inspector/lakefile.lean",
              "tools/lean-inspector-reg/lake-manifest.json",
              "tools/scripts/worktree/lean-cache-run.sh",
              "tools/lean-inspector/LeanInformationAudit/SealCommand.lean"]
    for relative in inputs:
        if not (repository / relative).is_file():
            raise ExportError(66, f"MissingBuildInput path={repository / relative}")
    for tool in ("make", "bash", "dotnet", "lake"):
        if shutil.which(tool) is None:
            raise ExportError(69, f"MissingTool tool={tool}")


def write_package(repository, directory, root, artifact):
    """Use current manifests and the canonical cache guard from an external make door."""
    package = directory / "package"
    package.mkdir(parents=True, exist_ok=True)
    quote = lambda path: json.dumps(str(path), ensure_ascii=False)
    (package / "lakefile.toml").write_text(
        'name = "p4SealExport"\nversion = "0.1.0"\ndefaultTargets = ["SealExport"]\n'
        f'packagesDir = {quote(repository / ".lake/packages")}\n\n'
        '[[require]]\nname = "reg"\n'
        f'path = {quote(repository / "Reg")}\n\n'
        '[[require]]\nname = "leanInspector"\n'
        f'path = {quote(repository / "tools/lean-inspector")}\n\n'
        '[[lean_lib]]\nname = "SealExport"\n', encoding="utf-8")
    manifest_base = repository / "tools/lean-inspector-reg"
    manifest = json.loads((manifest_base / "lake-manifest.json").read_text(encoding="utf-8"))
    manifest["name"] = "p4SealExport"
    manifest["packagesDir"] = str(repository / ".lake/packages")
    for dependency in manifest["packages"]:
        if dependency["type"] == "path":
            dependency["dir"] = str((manifest_base / dependency["dir"]).resolve())
        dependency["inherited"] = dependency["name"] not in ("reg", "leanInspector")
    (package / "lake-manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
    shutil.copyfile(repository / "lean-toolchain", package / "lean-toolchain")
    (package / "SealExport.lean").write_text(f"""import {root}
import LeanInformationAudit.SealCommand

open Lean Lean.Elab.Command LeanInformationAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

run_cmd do
  let root := `{root}
  liftTermElabM <| assessRecordedRegistrations root
  unless !(SealRecords.forRoot (← getEnv) root).isEmpty do
    throwError "MissingSealRecords root={{root}}"
  let rootId := mkIdent (`_root_ ++ root)
  elabCommand (← `(command| #stage_information_analysis root $rootId:ident))
  let destination := Syntax.mkStrLit {quote(artifact)}
  elabCommand (← `(command| #export_information_analysis root $rootId:ident
    output $destination:str))
""", encoding="utf-8")
    makefile = directory / "Makefile"
    makefile.write_text('.PHONY: lean\nlean:\n'
                        '\t@/bin/bash "$$SEAL_EXPORT_CACHE_RUNNER" lake -d '
                        '"$$SEAL_EXPORT_PACKAGE" build SealExport\n', encoding="utf-8")
    # Lake caches success independently of export destinations. Re-elaborate
    # only the temporary exporting module on reruns, preserving all dependencies.
    (package / ".lake/build/lib/lean/SealExport.trace").unlink(missing_ok=True)
    return package, makefile


def export_root(repository, output, root):
    directory = output / root.replace(".", "/")
    directory.mkdir(parents=True, exist_ok=True)
    artifact = directory / "seal.json"
    artifact.unlink(missing_ok=True)
    package, makefile = write_package(repository, directory, root, artifact)
    environment = dict(os.environ, SEAL_EXPORT_CACHE_RUNNER=str(
        repository / "tools/scripts/worktree/lean-cache-run.sh"), SEAL_EXPORT_PACKAGE=str(package))
    log = directory / "build.log"
    start = time.monotonic()
    with log.open("w", encoding="utf-8") as stream:
        process = subprocess.run(["make", "--no-print-directory", "-C", str(repository),
                                  "-f", str(makefile), "lean"], env=environment,
                                 stdout=stream, stderr=subprocess.STDOUT)
    (directory / "build.exit").write_text(str(process.returncode) + "\n", encoding="utf-8")
    elapsed = time.monotonic() - start
    try:
        check_export(root, process.returncode, artifact)
    except ExportError as error:
        (directory / "export.exit").write_text(str(error.code) + "\n", encoding="utf-8")
        raise ExportError(error.code, f"{error} log={log}") from error
    (directory / "export.exit").write_text("0\n", encoding="utf-8")
    return dict(root=root, path=str(artifact), elapsed_seconds=round(elapsed, 3))


class Parser(argparse.ArgumentParser):
    def error(self, message):
        raise ExportError(64, f"InvalidArguments: {message}")


def main():
    try:
        parser = Parser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
        parser.add_argument("--repository", type=Path, required=True)
        parser.add_argument("--roots", nargs="+", default=None)
        parser.add_argument("--output-dir", type=Path)
        parser.add_argument("--list", action="store_true")
        arguments = parser.parse_args()
        repository = arguments.repository.resolve()
        if not repository.is_dir() or not (repository / "Reg").is_dir():
            raise ExportError(66, f"MissingRepository path={repository}")
        roots = select_roots(repository, arguments.roots)
        output = arguments.output_dir.resolve() if arguments.output_dir else None
        if output and output.is_relative_to(repository):
            raise ExportError(64, f"OutputInsideRepository path={output}")
        if not arguments.list:
            validate_build(repository)
        if output is None:
            output = Path(tempfile.mkdtemp(prefix="reg-seal-export-")).resolve()
        if not arguments.list:
            output.mkdir(parents=True, exist_ok=True)
        for root in roots:
            row = dict(root=root, path=str(output / root.replace(".", "/") / "seal.json"))
            if not arguments.list:
                print(f"SealExport root={root}", file=sys.stderr, flush=True)
                row = export_root(repository, output, root)
            print(json.dumps(row, ensure_ascii=False, sort_keys=True), flush=True)
        return 0
    except ExportError as error:
        print(f"reg-seal-export: {error}", file=sys.stderr)
        return error.code
    except OSError as error:
        print(f"reg-seal-export: OutputOrInputUnavailable: {error}", file=sys.stderr)
        return 73


if __name__ == "__main__":
    sys.exit(main())
