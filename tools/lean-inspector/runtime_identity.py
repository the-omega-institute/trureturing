"""Identity of the actual programs used by an inspector invocation."""
from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import subprocess
import sys
import sysconfig
import zipfile

import delta
import materials


def file_sha(path: pathlib.Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def lean_programs(lake: str, repository: pathlib.Path, toolchain: pathlib.Path) -> dict:
    inspector = pathlib.Path(__file__).with_name("Inspector.lean")
    dependencies = subprocess.run([lake, "env", "lean", "--deps", str(inspector)],
        cwd=repository, check=True, capture_output=True, text=True).stdout.splitlines()
    pending = [pathlib.Path(path) for path in dependencies if path]
    programs = {}
    visited = set()
    while pending:
        olean = pending.pop().resolve()
        if olean in visited:
            continue
        visited.add(olean)
        relative = olean.relative_to(toolchain / "lib/lean").as_posix()
        # The compiler's structured import index supplies the transitive closure;
        # executable olean/IR parts supply the identity, not a declared version.
        imports = json.loads(olean.with_suffix(".ilean").read_text(encoding="utf-8"))["directImports"]
        for item in imports:
            name = item[0] if isinstance(item, list) else item
            pending.append(toolchain / "lib/lean" / (name.replace(".", "/") + ".olean"))
        for suffix in ("", ".private", ".server"):
            path = pathlib.Path(str(olean) + suffix)
            if path.is_file():
                programs["lean-module:" + relative + suffix] = file_sha(path)
        ir = olean.with_suffix(".ir")
        if ir.is_file():
            programs["lean-ir:" + relative] = file_sha(ir)
    return programs


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", type=pathlib.Path, required=True)
    parser.add_argument("--lake", required=True)
    args = parser.parse_args()
    try:
        prefix = subprocess.run([args.lake, "env", "lean", "--print-prefix"],
            cwd=args.repository, check=True, capture_output=True, text=True).stdout.strip()
        toolchain = pathlib.Path(prefix).resolve()
        lean = toolchain / "bin/lean"
        if not lean.is_file():
            raise ValueError("executing Lean installation is unavailable")
        programs = {"lean": file_sha(lean), **lean_programs(args.lake, args.repository, toolchain)}
        # Lean's evaluator and primitives live in the loaded shared libraries.
        for path in sorted((toolchain / "lib/lean").glob("*")):
            if path.is_file() and path.suffix in (".so", ".dylib", ".dll"):
                programs[path.name] = file_sha(path)
        programs["python"] = file_sha(pathlib.Path(sys.executable).resolve())
        library = pathlib.Path(sysconfig.get_config_var("LIBDIR") or "") / (sysconfig.get_config_var("LDLIBRARY") or "")
        framework = sysconfig.get_config_var("PYTHONFRAMEWORK")
        if framework:
            library = (pathlib.Path(sysconfig.get_config_var("PYTHONFRAMEWORKPREFIX"))
                / (framework + ".framework") / "Versions" / sysconfig.get_config_var("VERSION") / framework)
        if library.is_file():
            programs["python-runtime"] = file_sha(library)
        # Import the actual Python programs first; enumerate their loaded module
        # closure, including extension modules, rather than declared packages.
        for name, module in sorted(sys.modules.copy().items()):
            path = getattr(module, "__file__", None)
            if path and pathlib.Path(path).is_file():
                programs["python-module:" + name] = file_sha(pathlib.Path(path))
        identity = {"schema": "lean-report-runtime-v1", "programs": programs}
        print(hashlib.sha256(json.dumps(identity, sort_keys=True, separators=(",", ":")).encode()).hexdigest())
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        print(f"lean-report-runtime: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
