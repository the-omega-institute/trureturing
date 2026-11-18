"""Project module ownership, import closure and Lake build files for cache transport."""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass, field
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import subprocess
import tomllib


# The inspector packages share a source directory. The reg inspector owns the
# test and analysis roots declared in its separate Lake workspace.
SOURCE_ROOTS = ("D5", "Reg", "Trureturing.lean", "tools/lean-inspector",
                "tools/lean-inspector-interface")
PROJECT_BUILD = Path(".lake/build")
INSPECTOR = Path("tools/lean-inspector")
REG_INSPECTOR = Path("tools/lean-inspector-reg")
INTERFACE = Path("tools/lean-inspector-interface")

LEAN_SUFFIXES = {
    "olean", "olean.server", "olean.private", "ilean", "ir", "ir.sig", "trace",
}


@dataclass(frozen=True)
class Module:
    package: str
    source: Path
    build: Path


@dataclass(frozen=True)
class Artifact:
    path: PurePosixPath
    mode: int
    size: int
    module: str | None
    kind: str


@dataclass
class Inventory:
    modules: dict[str, Module]
    artifacts: list[Artifact] = field(default_factory=list)

    def by_module(self):
        members = defaultdict(list)
        for artifact in self.artifacts:
            if artifact.module is not None:
                members[artifact.module].append(artifact)
        return members


def workspace_modules(root: Path) -> dict[str, Module]:
    """Read the current project source set without building any Lean target."""
    reg_inspector_config = tomllib.loads((root / REG_INSPECTOR / "lakefile.toml").read_text())
    reg_inspector_roots = {
        name
        for library in reg_inspector_config["lean_lib"]
        for name in library["roots"]
    }
    packages = {}
    for directory in (Path("."), Path("Reg"), INTERFACE, REG_INSPECTOR):
        config = tomllib.loads((root / directory / "lakefile.toml").read_text())
        build = Path(os.path.normpath(directory / config.get("buildDir", ".lake/build")))
        packages[directory] = (config["name"], build.relative_to(PROJECT_BUILD))
    packages[INSPECTOR] = ("leanInspector", Path("lean-inspector/producer"))
    sources = subprocess.run(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard",
         "--", *SOURCE_ROOTS], cwd=root, stdout=subprocess.PIPE, check=True,
    ).stdout
    result = {}
    for name in sorted(set(os.fsdecode(sources).split("\0"))):
        source = Path(name)
        if source.suffix != ".lean" or source.name == "lakefile.lean" or not (root / source).is_file():
            continue
        relative = source
        owner = Path("Reg") if source.parts[0] == "Reg" else Path(".")
        if source.is_relative_to(INTERFACE):
            owner = INTERFACE
            relative = source.relative_to(owner)
        if source.is_relative_to(INSPECTOR):
            relative = source.relative_to(INSPECTOR)
            owner = REG_INSPECTOR if relative.parts[0] in reg_inspector_roots else INSPECTOR
        module = ".".join(relative.with_suffix("").parts)
        package, build = packages[owner]
        if module in result:
            raise ValueError(f"ambiguous module ownership: {module}")
        result[module] = Module(package, source, build)
    return result


def lake_configuration(root: Path) -> str:
    """Bind the compiler settings and dependency pins of every local Lake package."""
    files = [Path("lean-toolchain")]
    files.extend(directory / name
                 for directory in (Path("."), Path("Reg"), INSPECTOR, REG_INSPECTOR, INTERFACE)
                 for name in ("lakefile.lean", "lakefile.toml", "lake-manifest.json"))
    config = {}
    for relative in files:
        path = root / relative
        if path.is_symlink():
            raise ValueError(f"Lake config is a symlink: {relative}")
        if path.is_file():
            config[relative.as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    return hashlib.sha256(json.dumps(config, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def project_imports(root: Path, modules: dict[str, Module]) -> dict[str, set[str]]:
    """Use the pinned Lean header parser, including module and public imports."""
    headers = subprocess.run(
        ["lean", "--deps-json", "--stdin"], cwd=root, check=True,
        input="".join(f"{module.source.as_posix()}\n" for module in modules.values()),
        text=True, stdout=subprocess.PIPE,
    )
    graph = {}
    for name, header in zip(modules, json.loads(headers.stdout)["imports"], strict=True):
        if header["errors"]:
            raise ValueError(f"invalid Lean module header for {name}: {header['errors']}")
        graph[name] = {item["module"] for item in header["result"]["imports"]} & modules.keys()
    return graph


def import_closure(graph: dict[str, set[str]], targets) -> set[str]:
    pending = list(targets)
    included = set()
    while pending:
        module = pending.pop()
        if module not in included:
            pending.extend(graph[module])
            included.add(module)
    return included


def lean_artifact_paths(name, module):
    relative = PurePosixPath(*name.split("."))
    output = set()
    for location, suffixes in (("lib/lean", LEAN_SUFFIXES), ("ir", ("c", "bc"))):
        stem = PurePosixPath(module.build, location, relative)
        for suffix in suffixes:
            path = stem.with_suffix("." + suffix)
            output.add(path)
            output.add(path.with_name(path.name + ".hash"))
    return output


def _owner(path, module_paths, modules):
    for location, kind in (("lib/lean", "lean"), ("ir", "ir")):
        owner = module_paths.get(path.parent)
        if owner is None or owner[0] != location:
            continue
        stem, _, extension = path.name.partition(".")
        suffix = extension.removesuffix(".hash")
        if location == "lib/lean" and suffix not in LEAN_SUFFIXES:
            break
        if location == "ir":
            if suffix in ("c", "bc"):
                kind = "lean"
            elif suffix.startswith(("c.o", "bc.o", "o")):
                kind = "native"
            else:
                break
        return owner[1].get(stem), kind
    if path.parent in (
        PurePosixPath("lean-inspector/modules"), PurePosixPath("lean-inspector/inputs"),
        PurePosixPath("lean-inspector/judge-inputs"),
    ):
        module = next((name for name in (
            path.name.partition(".zip")[0], path.name.removesuffix(".json"),
        ) if name in modules), None)
        return module, "report"
    return None, "other"


def build_inventory(root: Path, modules: dict[str, Module]) -> Inventory:
    """Cover the private build tree, including report files and native tools."""
    build = root / PROJECT_BUILD
    if build.parent.is_symlink() or build.is_symlink() or not build.is_dir():
        raise ValueError("private Lake build directory is unavailable")
    module_paths = {}
    for name, module in modules.items():
        relative = PurePosixPath(*name.split("."))
        for location in ("lib/lean", "ir"):
            parent = PurePosixPath(module.build, location, relative.parent)
            _, stems = module_paths.setdefault(parent, (location, {}))
            stems[relative.name] = name

    def fail(error):
        raise error

    result = Inventory(modules)
    for directory, dirs, files in build.walk(on_error=fail):
        dirs.sort()
        for name in sorted(files):
            source = directory / name
            info = source.lstat()
            if not stat.S_ISREG(info.st_mode):
                raise ValueError(f"unsupported Lake artifact: {source.relative_to(root)}")
            if name.endswith(".setup.json"):
                continue
            path = PurePosixPath(source.relative_to(build))
            module, kind = _owner(path, module_paths, modules)
            result.artifacts.append(Artifact(path, stat.S_IMODE(info.st_mode), info.st_size,
                                             module, kind if module is not None else "other"))
    return result
