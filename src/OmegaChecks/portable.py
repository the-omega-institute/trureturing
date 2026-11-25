"""Compile downstream mathematical sources against the strict and pinned standard libraries."""
import argparse
from collections import defaultdict
from graphlib import TopologicalSorter
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from strict_lake import BUILD, COMMON_SRC, INSPECTOR, lake_layout, strict_config


ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / "src"
AUDIT = ROOT / ".lake/build/bin/omegaAudit"
BASIS = {"OmegaInit", "OmegaMathlib"}


def root(name):
    return name.split(".", 1)[0]


def output(*args, **kwargs):
    return subprocess.check_output(args, cwd=ROOT, text=True, **kwargs)


def import_graph(lean, pathspecs=("strict/*.lean", "src/*.lean", "D5/*.lean", "Trureturing.lean"), *, with_reg=False):
    if with_reg:
        pathspecs = (*pathspecs, "Reg/*.lean")
    files = output("git", "ls-files", "-co", "--exclude-standard", "-z", "--",
                   *pathspecs).split("\0")
    sources = {}
    for file in files:
        if file and (ROOT / file).is_file():
            path = file.removeprefix("strict/").removeprefix("src/")
            name = path.removesuffix(".lean").replace("/", ".")
            if file.startswith("src/") and root(name) in BASIS:
                continue
            sources[name] = ROOT / file
    if with_reg:
        if not (INSPECTOR / "lakefile.toml").is_file():
            raise RuntimeError("Reg requires the pinned inspector interface; run make install-tools")
        for path in [*INSPECTOR.glob("LeanInformationAuditInterface.lean"),
                     *(INSPECTOR / "LeanInformationAuditInterface").rglob("*.lean")]:
            sources[".".join(path.relative_to(INSPECTOR).with_suffix("").parts)] = path
    names = sorted(sources)
    result = json.loads(output(lean, "--deps-json", "--stdin",
                               input="".join(str(sources[name]) + "\n" for name in names)))
    graph = {}
    for name, row in zip(names, result["imports"], strict=True):
        if row["errors"]:
            raise RuntimeError(f"{name}: {row['errors']}")
        entries = row["result"]["imports"]
        graph[name] = {entry["module"] for entry in entries}
    return sources, graph


def consumers(graph):
    touched = {}
    for name in TopologicalSorter(graph).static_order():
        deps = graph.get(name, ())
        touched[name] = root(name) in {"OmegaInit", "OmegaMathlib", "OmegaMath"} or any(touched[dep] for dep in deps)
    # Correspondence proofs import both bases deliberately. The Portable modules are clients.
    return sorted(n for n in graph if touched[n] and root(n) not in BASIS
                  and (root(n) != "OmegaChecks" or n.startswith("OmegaChecks.Portable.")))


def closure(graph, roots):
    pending = list(roots)
    seen = set()
    while pending:
        name = pending.pop()
        if name not in seen:
            seen.add(name)
            pending.extend(dep for dep in graph[name] if dep in graph)
    return list(TopologicalSorter({n: graph[n] & seen for n in sorted(seen)}).static_order())


def namespace_exports(lean, strict, basis, official_path):
    helper = SRC / "OmegaChecks/Portable/Exports.lean"
    surface = json.loads(output(lean, "--run", helper, strict, official_path, *basis,
                                env={**os.environ, "LEAN_PATH": ""}))
    exports = defaultdict(lambda: defaultdict(list))
    for module, namespace, official, leaf in surface["names"]:
        exports[module][namespace, official].append(leaf)
    seals = defaultdict(list)
    for module, official in surface["seals"]:
        seals[module].append(official)
    return dict(surface["imports"]), exports, seals


def official_module(name):
    if name == "OmegaMathlib":
        # The subset umbrella gathers its admitted ports through the strict import graph.
        return None
    return name.replace("OmegaMathlib", "Mathlib", 1) if root(name) == "OmegaMathlib" else name[5:]


def alias_sections(exports):
    lines = []
    for (namespace, original), leaves in sorted(exports.items()):
        lines.extend([f"namespace {namespace}", f"export {original} ({' '.join(sorted(leaves))})",
                      f"end {namespace}"])
    return lines


def official_basis_source(module, deps, exports, seals):
    upstream = official_module(module)
    imports = set(deps)
    if upstream:
        imports.add(upstream)
    lines = ["module", *("public import " + n for n in sorted(imports)), "",
             "/-! Namespace aliases to the pinned public interface. -/", "public section",
             *alias_sections(exports)]
    if seals:
        lines.extend(["", "set_option allowUnsafeReducibility true in",
                      "attribute [irreducible] " + " ".join("_root_." + name for name in sorted(seals))])
    return "\n".join(lines) + "\n"


def derived_facades(lean, strict, basis, official_path):
    imports, exports, seals = namespace_exports(lean, str(strict), basis, official_path)
    normal = {name: official_basis_source(name, imports[name], exports[name], []).encode() for name in basis}
    common = {name: official_basis_source(name, imports[name], exports[name], seals[name]).encode() for name in basis}
    return normal, common


def regenerate_facades():
    lean = output("lake", "env", "printenv", "LEAN").strip()
    sources, graph = import_graph(lean, ("strict/*.lean",))
    basis = sorted(name for name in graph if root(name) in BASIS)
    if not BASIS.issubset(basis):
        raise RuntimeError("strict foundation roots are missing")
    subprocess.run(["lake", "-f", strict_config(), "build", *("+" + name for name in basis)],
                   cwd=ROOT, check=True)
    generated, _ = derived_facades(lean, ROOT / BUILD / "lib/lean", basis,
                                output("lake", "env", "printenv", "LEAN_PATH").strip())
    changed = []
    with tempfile.TemporaryDirectory(dir=ROOT / ".lake") as temporary:
        for name, content in generated.items():
            relative = sources[name].relative_to(ROOT / "strict")
            target = SRC / relative
            if target.resolve() != target:
                raise ValueError(f"refusing to write a facade through a symlink: {target}")
            if target.exists() and target.read_bytes() == content:
                continue
            staged = Path(temporary) / relative
            staged.parent.mkdir(parents=True, exist_ok=True)
            staged.write_bytes(content)
            if target.exists():
                staged.chmod(target.stat().st_mode)
            changed.append((staged, target))
        for staged, target in changed:
            target.parent.mkdir(parents=True, exist_ok=True)
            staged.replace(target)
            print(f"Updated {target.relative_to(ROOT)}")
    print(f"Updated {len(changed)} of {len(basis)} official facade modules")


def backend_artifacts(strict, with_reg, sources, stage, packages, lean, environment, common_dir=None):
    lake, libraries = lake_layout(strict, with_reg, common_dir)
    paths = [Path(path).resolve() for path in
             output(*lake, "env", "printenv", "LEAN_PATH", env=environment).strip().split(os.pathsep)]
    syslib = Path(output(lean, "--print-libdir").strip()).resolve()
    if len(set(paths)) != len(paths) or set(paths) != {*packages, *libraries.values(), syslib}:
        raise RuntimeError(f"unexpected Lake import path: {paths}")

    # Querying the facets builds the selected modules through the normal Lake graph.
    # Lake supplies both the actual source owner and the resulting olean in request order.
    targets = [f"+{name}:{facet}" for name in sources for facet in ("lean", "olean")]
    resolved = [Path(p).resolve() for p in output(*lake, "query", *targets, env=environment).splitlines()]
    expected_paths = []
    hashes = {}
    for name, source in sources.items():
        base = Path(*name.split("."))
        lib = libraries.get(root(name), libraries[""])
        artifact = lib / base.with_suffix(".olean")
        expected_paths.extend([source.resolve(), artifact.resolve()])
        if any((directory / base.with_suffix(".olean")).exists() for directory in paths if directory != lib):
            raise RuntimeError(f"dependency shadows project module {name}")
        trace = json.loads((lib / base.with_suffix(".trace")).read_text())["outputs"]
        parts = [*trace["o"], *(trace[key] for key in ("rs", "r") if key in trace)]
        for part in parts:
            digest, suffix = part.split(".", 1)
            if suffix not in {"olean", "olean.server", "olean.private", "ir", "ir.sig"}:
                raise ValueError(f"unexpected import artifact {part} for {name}")
            relative = base.with_suffix("." + suffix)
            staged = stage / relative
            staged.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(lib / relative, staged)
            hashes[staged] = digest
        if stage / base.with_suffix(".olean") not in hashes:
            raise RuntimeError(f"no olean in Lake output trace for {name}")
    if resolved != expected_paths:
        raise RuntimeError("Lake selected an unexpected source file or artifact for the requested modules")
    # Audit and publish these exact immutable bytes, even if another Lake build follows.
    actual = output(lean, "--run", SRC / "OmegaChecks/Portable/ArtifactHashes.lean",
                    input="\n".join(map(str, hashes)), env=environment).splitlines()
    for (file, expected), observed in zip(hashes.items(), actual, strict=True):
        if expected != observed:
            raise RuntimeError(f"artifact differs from its Lake trace: {file}")
    return os.pathsep.join(map(str, [stage, *(path for path in paths if path not in libraries.values())]))


def publish(tree, destination):
    # Switch complete artifact sets atomically. Existing Lean processes may retain
    # their resolved generation. Identical builds reuse the same generation.
    destination = destination.absolute()
    store = destination.with_name(f".{destination.name}.generations")
    store.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256()
    for file in sorted(tree.rglob("*")):
        if not file.is_file():
            continue
        if file.suffix == ".lean":
            file.unlink()
            continue
        digest.update(str(file.relative_to(tree)).encode() + b"\0")
        with file.open("rb") as artifact:
            digest.update(hashlib.file_digest(artifact, "sha256").digest())
    generation = store / digest.hexdigest()
    with (store / ".lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if destination.is_symlink():
            if destination.readlink().parent != Path(store.name):
                raise ValueError(f"output belongs to another build: {destination}")
        elif destination.exists():
            destination.rmdir()  # Only a new, empty, or previously managed output is safe.
        if not generation.exists():
            tree.rename(generation)
        with tempfile.TemporaryDirectory(dir=store) as temp:
            link = Path(temp) / "current"
            link.symlink_to(generation.relative_to(destination.parent), target_is_directory=True)
            link.replace(destination)
    print(f"Lean artifacts: {destination}", flush=True)


def source_fingerprint(path):
    with path.open("rb") as file:
        digest = hashlib.file_digest(file, "sha256").digest()
        stat = os.fstat(file.fileno())
    return digest, stat.st_ino, stat.st_ctime_ns


def check(only, backend="mathlib", destination=None):
    lean = output("lake", "env", "printenv", "LEAN").strip()
    with_reg = backend == "both" or any(root(name) == "Reg" for name in only)
    sources, graph = import_graph(lean, with_reg=with_reg)
    selected = consumers(graph)
    portable_clients = [name for name in selected if name.startswith("OmegaChecks.Portable.")]
    if only:
        if set(only) - set(selected):
            raise ValueError(f"outside the strict downstream closure: {sorted(set(only) - set(selected))}")
        selected = sorted(set(only))
    if not selected:
        raise RuntimeError("no downstream consumers selected")
    print(f"Portable consumer targets ({len(selected)}): {' '.join(selected)}", flush=True)
    all_basis = {name for name in graph if root(name) in BASIS}
    facades = {str(path.relative_to(SRC).with_suffix("")).replace(os.sep, "."): path
               for prefix in BASIS for path in (*SRC.glob(prefix + ".lean"), *(SRC / prefix).rglob("*.lean"))}
    if backend != "strict" and all_basis != set(facades):
        raise RuntimeError(f"standard and strict module trees differ: {sorted(all_basis ^ set(facades))}")
    modules = closure(graph, selected if only else [*selected, *all_basis])
    basis = [n for n in modules if root(n) in BASIS]
    downstream = [n for n in modules if root(n) not in BASIS]
    # The admission-only profile covers the designated portable clients and the entire basis.
    common_modules = closure(graph, [*all_basis, *portable_clients]) if backend == "both" else []
    compiled = dict.fromkeys([*modules, *common_modules])
    with_reg = any(root(n) in {"Reg", "LeanInformationAuditInterface"} for n in compiled)
    strict_sources = {name: sources[name] for name in compiled}
    official_sources = {name: facades[name] if root(name) in BASIS else sources[name]
                        for name in compiled} if backend != "strict" else {}
    if backend == "both":
        certificates = closure(graph, ["OmegaChecks.Interface.Equations"])
        for name in certificates:
            official_sources[name] = sources[name]

    tracked = set()
    if backend != "mathlib":
        tracked.update(strict_sources.values())
    if backend != "strict":
        tracked.update(official_sources.values())
    tracked.update(ROOT / file for file in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"))
    if with_reg:
        tracked.update(directory / file for directory in (ROOT / "Reg", INSPECTOR)
                       for file in ("lakefile.toml", "lake-manifest.json"))
    tracked.update([Path(__file__), SRC / "OmegaChecks/strict_lake.py", SRC / "OmegaChecks/Portable/ArtifactHashes.lean"])
    if backend == "both":
        tracked.add(SRC / "OmegaChecks/Portable/Exports.lean")
    source_hashes = {path: source_fingerprint(path) for path in tracked}
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = {(ROOT / manifest["packagesDir"] / p["name"] / ".lake/build/lib/lean").resolve()
                for p in manifest["packages"]}
    environment = {k: v for k, v in os.environ.items() if k not in {"LEAN_PATH", "LEAN_SRC_PATH"}}
    if destination:
        destination = Path(destination).absolute()
        destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="omega-portable-", dir=destination.parent if destination else None) as temp:
        strict, official = (Path(temp) / x for x in ("strict", "standard"))
        if backend != "mathlib":
            strict_path = backend_artifacts(True, with_reg, strict_sources, strict, packages, lean, environment)
        if backend != "strict":
            official_path = backend_artifacts(False, with_reg, official_sources, official, packages, lean, environment)
        if backend == "both":
            common_basis = [name for name in common_modules if root(name) in BASIS]
            normal, common = derived_facades(lean, strict, common_basis, official_path)
            common_downstream = [name for name in common_modules if root(name) not in BASIS]
            common_sources = {name: official_sources[name] for name in [*common_modules, *certificates]}
            for name, expected in normal.items():
                if facades[name].read_bytes() != expected:
                    raise RuntimeError(f"{facades[name]} does not re-export the compiled strict interface")
                path = COMMON_SRC / facades[name].relative_to(SRC)
                path.parent.mkdir(parents=True, exist_ok=True)
                if not path.exists() or path.read_bytes() != common[name]:
                    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as f:
                        f.write(common[name])
                    os.replace(f.name, path)
                source_hashes[path] = source_fingerprint(path)
                if source_hashes[path][0] != hashlib.sha256(common[name]).digest():
                    raise RuntimeError(f"generated interface changed before compilation: {path}")
                common_sources[name] = path
            common_reg = any(root(name) in {"Reg", "LeanInformationAuditInterface"} for name in common_sources)
            common_path = backend_artifacts(False, common_reg, common_sources, Path(temp) / "common", packages,
                                            lean, environment, COMMON_SRC)
            subprocess.run(["lake", "build", "omegaAudit"], cwd=ROOT, env=environment, check=True)
            subprocess.run([AUDIT, "--consumer", strict_path, common_path, *common_downstream, "--basis", *common_basis], cwd=ROOT,
                           env=environment, check=True)
            print(f"Common computational interface checked: {len(common_basis)} basis modules, "
                  f"{len(portable_clients)} portable fixtures", flush=True)
            staged_report = Path(temp) / "official-axioms.json"
            subprocess.run([AUDIT, "--consumer", strict_path, official_path, *downstream, "--basis", *basis], cwd=ROOT,
                           env={**environment, "OMEGA_OFFICIAL_AXIOM_REPORT": str(staged_report)}, check=True)
        for path, original in source_hashes.items():
            if source_fingerprint(path) != original:
                raise RuntimeError(f"source changed during the backend check: {path}")
        if destination:
            keep = set(official_sources)
            if only and backend == "both":
                keep = set(modules) | set(certificates)
            elif with_reg and not only:
                # The root publication excludes the separate Reg package's research-tool artifacts.
                root_targets = [name for name in selected if root(name) not in {"Reg", "LeanInformationAuditInterface"}]
                keep = set(closure(graph, [*root_targets, *all_basis, "OmegaChecks.Interface.Equations"]))
            for name in official_sources.keys() - keep:
                base = official.joinpath(*name.split("."))
                for artifact in base.parent.glob(base.name + ".*"):
                    if artifact.is_file():
                        artifact.unlink()
            publish(strict if backend == "strict" else official, destination)
        if backend == "both":
            report_name = "selected-official-axioms.json" if only else "official-axioms.json"
            report = ROOT / ".lake/build/omega-checks" / report_name
            report.parent.mkdir(parents=True, exist_ok=True)
            with tempfile.TemporaryDirectory(dir=report.parent) as report_dir:
                local_report = Path(report_dir) / report.name
                shutil.copyfile(staged_report, local_report)
                local_report.replace(report)
            print(f"Official declaration axiom dependencies: {report}", flush=True)
            print(f"Dual compilation and exported declarations checked: {len(downstream)} modules")
        else:
            print(f"{backend} backend compiled {len(downstream)} downstream modules (single backend)")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="*", help="restrict the local check to these consumers")
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--regenerate-facades", action="store_true", help="write official aliases from the strict ports")
    modes.add_argument("--backend", choices=("both", "strict", "mathlib"), default="mathlib",
                        help="compile one backend locally or verify both (the admission check)")
    parser.add_argument("--output", type=Path, help="publish importable Lean artifacts into this directory")
    args = parser.parse_args()
    if args.regenerate_facades:
        if args.modules or args.output:
            parser.error("--regenerate-facades takes no module selection or artifact output")
        regenerate_facades()
    else:
        check(args.modules, args.backend, args.output)
