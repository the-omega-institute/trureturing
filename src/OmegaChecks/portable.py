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
STANDARD_AXIOMS = {"Classical.choice", "Quot.sound", "propext"}


def root(name):
    return name.split(".", 1)[0]


def output(*args, **kwargs):
    return subprocess.check_output(args, cwd=ROOT, text=True, **kwargs)


def import_graph(lean, pathspecs=("strict/*.lean", "src/*.lean", "D5/*.lean", "Trureturing.lean"), *,
                 with_reg=False, official_basis=False):
    if with_reg:
        pathspecs = (*pathspecs, "Reg/*.lean")
    files = output("git", "ls-files", "-co", "--exclude-standard", "-z", "--",
                   *pathspecs).split("\0")
    sources = {}
    for file in files:
        if file and (ROOT / file).is_file():
            path = file.removeprefix("strict/").removeprefix("src/")
            name = path.removesuffix(".lean").replace("/", ".")
            if file.startswith("src/") and root(name) in BASIS and not official_basis:
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
        touched[name] = root(name) in {"OmegaInit", "OmegaMathlib", "OmegaMath"} or name == "OmegaBuild.Commands" or any(touched[dep] for dep in deps)
    # Correspondence proofs import both bases deliberately. The Portable modules are clients.
    return sorted(n for n in graph if touched[n] and root(n) not in BASIS | {"OmegaBuild"}
                  and (root(n) != "OmegaChecks" or n.startswith("OmegaChecks.Portable.")))


def closure(graph, roots):
    pending = list(roots)
    seen = set()
    while pending:
        name = pending.pop()
        if name not in seen:
            seen.add(name)
            pending.extend(dep for dep in graph[name] if dep in graph)
    return list(TopologicalSorter({n: sorted(graph[n] & seen) for n in sorted(seen)}).static_order())


def backend_plan(official_path, names, environment=None, *, prepared=False):
    """Read backend restrictions from the exact official artifacts about to be consumed."""
    if not names:
        return {"mathlibOnly": {}, "declarations": []}
    if prepared:
        # Run main from the selector module restored with these official artifacts.
        env = {**(os.environ if environment is None else environment), "LEAN_PATH": official_path}
        raw = output("lean", "--stdin", "--run", "OmegaBackendPlan.lean", official_path, *names,
                     input="import OmegaBuild.Plan\n", env=env)
    else:
        subprocess.run(["lake", "build", "omegaBackendPlan"], cwd=ROOT, env=environment, check=True)
        raw = output(ROOT / ".lake/build/bin/omegaBackendPlan", official_path, *names, env=environment)
    plan = json.loads(raw)
    for name, chain in plan["mathlibOnly"].items():
        if name not in names or not chain or chain[0] != name:
            raise RuntimeError(f"invalid backend restriction for {name}: {chain}")
        if root(name) in BASIS:
            raise RuntimeError(f"strict foundation cannot opt out of verification: {name}")
        print(f"Strict build skipped: {' -> '.join(chain)} (compile_only_with_mathlib)", flush=True)
    return plan


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


def backend_artifacts(strict, with_reg, sources, stage, packages, lean, environment,
                      common_dir=None, *, snapshots=None):
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
        if snapshots is not None and (source.resolve() != source or artifact.resolve() != artifact):
            raise RuntimeError(f"unexpected linked source or artifact for {name}")
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
            compiled_part = lib / relative
            if snapshots is not None and compiled_part.resolve() != compiled_part:
                raise RuntimeError(f"unexpected linked compiler artifact: {compiled_part}")
            shutil.copyfile(compiled_part, staged)
            hashes[staged] = digest
        if stage / base.with_suffix(".olean") not in hashes:
            raise RuntimeError(f"no olean in Lake output trace for {name}")
    if resolved != expected_paths:
        raise RuntimeError("Lake selected an unexpected source file or artifact for the requested modules")
    # Audit and publish these exact immutable bytes, even if another Lake build follows.
    if snapshots is not None:
        snapshots[stage] = artifact_snapshot(stage)
    actual = output(lean, "--run", SRC / "OmegaChecks/Portable/ArtifactHashes.lean",
                    input="\n".join(map(str, hashes)), env=environment).splitlines()
    for (file, expected), observed in zip(hashes.items(), actual, strict=True):
        if expected != observed:
            raise RuntimeError(f"artifact differs from its Lake trace: {file}")
    if snapshots is not None and artifact_snapshot(stage) != snapshots[stage]:
        raise RuntimeError(f"staged compiler artifacts changed during trace verification: {stage}")
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


def read_measurement(path, names):
    rows = json.loads(path.read_text())
    if not isinstance(rows, list) or [row["module"] for row in rows] != names:
        raise RuntimeError(f"unexpected module inventory in {path}")
    for module in rows:
        if module.keys() != {"module", "declarations"}:
            raise RuntimeError(f"unexpected canonical measurement fields for {module['module']}")
        keys = set()
        for row in module["declarations"]:
            key = row["nameKey"]
            if not isinstance(key, str) or not isinstance(row["kind"], str):
                raise RuntimeError(f"invalid declaration identity for {module['module']}")
            expected = {"nameKey", "kind", "statementTypeAddress", "includeInStatement", "axioms"}
            if row["includeInStatement"]:
                expected.add("libraries")
            if row.keys() != expected:
                raise RuntimeError(f"unexpected declaration measurement fields for {key}")
            if key in keys:
                raise RuntimeError(f"duplicate declaration in {module['module']}: {key}")
            keys.add(key)
            address = row["statementTypeAddress"]
            if not (isinstance(address, str) and address.startswith("sha256:") and
                    len(address) == 71 and all(c in "0123456789abcdef" for c in address[7:])):
                raise RuntimeError(f"invalid statement address for {key}")
            if type(row["includeInStatement"]) is not bool:
                raise RuntimeError(f"invalid inclusion status for {key}")
            fields = ["axioms", "libraries"] if row["includeInStatement"] else ["axioms"]
            for field in fields:
                values = row[field]
                if not isinstance(values, list) or any(not isinstance(v, str) for v in values):
                    raise RuntimeError(f"invalid {field} for {key}")
                if len(set(values)) != len(values):
                    raise RuntimeError(f"duplicate {field} for {key}")
    return rows


def declaration_rows(module):
    return {row["nameKey"]: row for row in module["declarations"]}


def normalize_row(row):
    return {key: sorted(value) if key in {"axioms", "libraries"} else value
            for key, value in row.items()}


def same_measurement(first, second):
    return ({key: normalize_row(row) for key, row in declaration_rows(first).items()}
            == {key: normalize_row(row) for key, row in declaration_rows(second).items()})


def paired_inventory(official, staged_official, strict, eligible):
    official_by_module = {module["module"]: module for module in staged_official}
    strict_by_module = {module["module"]: module for module in strict}
    if set(official_by_module) != eligible or set(strict_by_module) != eligible:
        raise RuntimeError("paired measurement module inventory mismatch")
    inventory = []
    for module in official:
        name = module["module"]
        if name not in eligible:
            continue
        original = declaration_rows(module)
        if not same_measurement(module, official_by_module[name]):
            raise RuntimeError(f"staged official measurement differs from canonical measurement: {name}")
        counterpart = declaration_rows(strict_by_module[name])
        for key, row in counterpart.items():
            invalid_axioms = set(row["axioms"]) - STANDARD_AXIOMS
            if invalid_axioms:
                raise RuntimeError(f"inadmissible strict axioms for {name}:{key}: {sorted(invalid_axioms)}")
        shared = original.keys() & counterpart.keys()
        for key in sorted(shared):
            row, other = original[key], counterpart[key]
            if row["kind"] != other["kind"]:
                raise RuntimeError(f"strict declaration kind differs for {name}:{key}")
            if row["includeInStatement"] != other["includeInStatement"]:
                raise RuntimeError(f"strict declaration inclusion differs for {name}:{key}")
        inventory.append({
            "moduleName": name,
            "paired": sorted(key for key in shared if original[key]["includeInStatement"]),
            "officialOnly": sorted(original.keys() - counterpart.keys()),
            "strictOnly": sorted(counterpart.keys() - original.keys()),
        })
    return inventory


def attach_strict_measurement(official, strict, inventory, certified):
    eligible = {entry["moduleName"]: entry for entry in inventory}
    strict_by_module = {module["module"]: declaration_rows(module) for module in strict}
    expected = [[entry["moduleName"], key] for entry in inventory for key in entry["officialOnly"]]
    if certified != expected:
        raise RuntimeError("compiled comparison did not certify the official-only inventory")
    for module in official:
        name = module["module"]
        module["strictEligible"] = name in eligible
        if name not in eligible:
            continue
        rows = declaration_rows(module)
        for key in eligible[name]["officialOnly"]:
            if rows[key]["includeInStatement"]:
                rows[key]["officialDerivedOnly"] = True
        for key in eligible[name]["paired"]:
            row, other = rows[key], strict_by_module[name][key]
            row["strict_omega"] = {
                "declaration_name_key": key,
                "kind": other["kind"],
                "statement_type_address": other["statementTypeAddress"],
                "official_statement_type_address": row["statementTypeAddress"],
                "libraries": sorted(other["libraries"]),
                "axioms": sorted(other["axioms"]),
            }


def measure_staged(inspector, request, names, search_path, destination, environment):
    subprocess.run([inspector, "--frozen-dependencies-v1", request, destination],
                   cwd=ROOT, env={**environment, "LEAN_PATH": search_path}, check=True)
    return read_measurement(destination, names)


def artifact_snapshot(directory):
    return {path: source_fingerprint(path) for path in directory.rglob("*") if path.is_file()}


def atomic_json(path, value):
    with tempfile.TemporaryDirectory(dir=path.parent) as temp:
        file = Path(temp) / path.name
        file.write_text(json.dumps(value, separators=(",", ":")) + "\n")
        file.replace(path)


def frozen_measurement(request, official_path, inspector, destination):
    names = json.loads(request.read_text())
    if not isinstance(names, list) or not all(isinstance(name, str) for name in names):
        raise RuntimeError("expected a list of requested module names")
    if len(set(names)) != len(names):
        raise RuntimeError("duplicate requested module")
    original = read_measurement(official_path, names)
    lean = output("lake", "env", "printenv", "LEAN").strip()
    sources, graph = import_graph(lean, with_reg=any(root(n) == "Reg" for n in names))
    missing = {name for name in names if root(name) == "D5" and name not in sources}
    if missing:
        raise RuntimeError(f"frozen module outside source discovery: {sorted(missing)}")
    eligible = set(consumers(graph)) & set(names)
    if not eligible:
        attach_strict_measurement(original, [], [], [])
        atomic_json(destination, original)
        return
    check(sorted(eligible), "both", frozen=(original, inspector, destination),
          discovered=(sources, graph))


def check(only, backend="mathlib", destination=None, *, frozen=None, discovered=None,
          basis_roots=None, common_roots=()):
    lean = output("lake", "env", "printenv", "LEAN").strip()
    scoped = basis_roots is not None
    with_reg = ((backend == "both" and frozen is None and not scoped)
                or any(root(name) == "Reg" for name in only))
    sources, graph = discovered if discovered is not None else import_graph(lean, with_reg=with_reg)
    selected = consumers(graph)
    portable_clients = [name for name in selected if name.startswith("OmegaChecks.Portable.")]
    if only or scoped:
        if set(only) - set(selected):
            raise ValueError(f"outside the strict downstream closure: {sorted(set(only) - set(selected))}")
        selected = sorted(set(only))
    if not selected and not basis_roots:
        raise RuntimeError("no downstream consumers selected")
    print(f"Portable consumer targets ({len(selected)}): {' '.join(selected)}", flush=True)
    all_basis = {name for name in graph if root(name) in BASIS}
    facades = {str(path.relative_to(SRC).with_suffix("")).replace(os.sep, "."): path
               for prefix in BASIS for path in (*SRC.glob(prefix + ".lean"), *(SRC / prefix).rglob("*.lean"))}
    if all_basis != set(facades):
        raise RuntimeError(f"standard and strict module trees differ: {sorted(all_basis ^ set(facades))}")
    roots = [*selected, *basis_roots] if scoped else selected if only else [*selected, *all_basis]
    modules = closure(graph, roots)
    basis = [n for n in modules if root(n) in BASIS]
    downstream = [n for n in modules if root(n) not in BASIS | {"OmegaBuild"}]
    # The admission-only profile covers the designated portable clients and the entire basis.
    if not scoped and backend == "both" and frozen is None:
        common_roots = [*all_basis, *portable_clients]
    common_modules = closure(graph, common_roots)
    compiled = dict.fromkeys([*modules, *common_modules])
    with_reg = any(root(n) in {"Reg", "LeanInformationAuditInterface"} for n in compiled)
    strict_sources = {name: sources[name] for name in compiled}
    official_sources = {name: facades[name] if root(name) in BASIS else sources[name]
                        for name in compiled}
    if backend == "both":
        certificates = closure(graph, ["OmegaChecks.Interface.Equations"])
        for name in certificates:
            official_sources[name] = sources[name]

    tracked = set()
    if backend != "mathlib":
        tracked.update(strict_sources.values())
        tracked.update(sources[name] for name in closure(graph, ["OmegaChecks.InitCompiler"]))
    tracked.update(official_sources.values())
    tracked.update(ROOT / file for file in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"))
    if with_reg:
        tracked.update(directory / file for directory in (ROOT / "Reg", INSPECTOR)
                       for file in ("lakefile.toml", "lake-manifest.json"))
    tracked.update([Path(__file__), SRC / "OmegaChecks/strict_lake.py", SRC / "OmegaChecks/Portable/ArtifactHashes.lean"])
    if backend != "mathlib":
        tracked.update((SRC / "OmegaBuild/Commands.lean", SRC / "OmegaBuild/Plan.lean"))
    if backend == "both":
        tracked.add(SRC / "OmegaChecks/Portable/Exports.lean")
    if frozen is not None:
        tracked.update(sources[name] for name in closure(graph, ["OmegaChecks.Audit"]))
        tracked.add(frozen[1])
    source_hashes = {path: source_fingerprint(path) for path in tracked}
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = {(ROOT / manifest["packagesDir"] / p["name"] / ".lake/build/lib/lean").resolve()
                for p in manifest["packages"]}
    environment = {k: v for k, v in os.environ.items()
                   if k not in {"LEAN_PATH", "LEAN_SRC_PATH", "OMEGA_FROZEN_INVENTORY", "OMEGA_FROZEN_CERTIFICATE",
                                "OMEGA_OFFICIAL_AXIOM_REPORT", "OMEGA_CACHE_CONSUMER_MODE"}}
    if destination:
        destination = Path(destination).absolute()
        destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="omega-portable-", dir=destination.parent if destination else None) as temp:
        strict, official = (Path(temp) / x for x in ("strict", "standard"))
        snapshots = {} if frozen is not None else None
        official_path = backend_artifacts(False, with_reg, official_sources, official, packages,
                                          lean, environment, snapshots=snapshots)
        skipped = {}
        if backend != "mathlib":
            plan = backend_plan(official_path, list(compiled), environment)
            skipped = plan["mathlibOnly"]
            strict_sources = {n: path for n, path in strict_sources.items() if n not in skipped}
            downstream = [n for n in downstream if n not in skipped]
            common_modules = closure(graph, [n for n in common_roots if n not in skipped])
            strict.mkdir()
            if strict_sources:
                strict_path = backend_artifacts(True, with_reg, strict_sources, strict, packages, lean,
                                                environment, snapshots=snapshots)
        if common_modules:
            common_basis = [name for name in common_modules if root(name) in BASIS]
            normal, common = derived_facades(lean, strict, common_basis, official_path)
            common_downstream = [name for name in common_modules if root(name) not in BASIS | {"OmegaBuild"}]
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
        if backend == "both" and frozen is None:
            subprocess.run(["lake", "build", "omegaAudit"], cwd=ROOT, env=environment, check=True)
        if common_modules:
            subprocess.run([AUDIT, "--consumer", strict_path, common_path, *common_downstream, "--basis", *common_basis], cwd=ROOT,
                           env={**environment, "OMEGA_CACHE_CONSUMER_MODE": "common-interface"}, check=True)
            print(f"Common computational interface checked: {len(common_basis)} basis modules, "
                  f"{len(common_downstream)} downstream modules", flush=True)
        if backend == "both" and frozen is None:
            staged_report = Path(temp) / "official-axioms.json"
            report_data = {"backend": "mathlib", "consumerModules": [], "declarations": []}
            if downstream or basis:
                subprocess.run([AUDIT, "--consumer", strict_path, official_path, *downstream, "--basis", *basis],
                               cwd=ROOT, env={**environment, "OMEGA_CACHE_CONSUMER_MODE": "official-interface",
                                              "OMEGA_OFFICIAL_AXIOM_REPORT": str(staged_report)},
                               check=True)
                report_data = json.loads(staged_report.read_text())
            # Supplemental common-interface checks may cover unrelated consumers.
            reported = {name: skipped[name] for name in modules if name in skipped}
            report_data["mathlibOnly"] = reported
            report_data["declarations"].extend(row for row in plan["declarations"] if row["module"] in reported)
            report_data["consumerModules"].extend(reported)
            atomic_json(staged_report, report_data)
        if frozen is not None:
            canonical, inspector, response = frozen
            # Both readers and the comparator must consume the very same verified
            # staging trees, never a mutable build directory or inherited LEAN_PATH.
            for tree, before in snapshots.items():
                if artifact_snapshot(tree) != before:
                    raise RuntimeError(f"staged compiler artifacts changed before measurement: {tree}")
            request = Path(temp) / "frozen-request.json"
            eligible = [name for name in selected if name not in skipped]
            request.write_text(json.dumps(selected))
            official_rows = measure_staged(inspector, request, selected, official_path,
                                           Path(temp) / "official-dependencies.json", environment)
            canonical_by_name = {module["module"]: module for module in canonical}
            for measured in official_rows:
                name = measured["module"]
                if name in skipped:
                    if not same_measurement(measured, canonical_by_name[name]):
                        raise RuntimeError(f"staged official measurement differs from canonical measurement: {name}")
                    canonical_by_name[name]["mathlibOnly"] = skipped[name]
            inventory, strict_rows, certified = [], [], []
            if eligible:
                request.write_text(json.dumps(eligible))
                strict_rows = measure_staged(inspector, request, eligible, strict_path,
                                             Path(temp) / "strict-dependencies.json", environment)
                paired_official = [row for row in official_rows if row["module"] not in skipped]
                inventory = paired_inventory(canonical, paired_official, strict_rows, set(eligible))
                inventory_path = Path(temp) / "frozen-inventory.json"
                certificate_path = Path(temp) / "frozen-certificate.json"
                inventory_path.write_text(json.dumps(inventory))
                subprocess.run(["lake", "build", "omegaAudit"], cwd=ROOT, env=environment, check=True)
                subprocess.run([AUDIT, "--consumer", strict_path, official_path, *downstream, "--basis", *basis],
                               cwd=ROOT, env={**environment, "OMEGA_FROZEN_INVENTORY": str(inventory_path),
                                    "OMEGA_FROZEN_CERTIFICATE": str(certificate_path)}, check=True)
                certified = json.loads(certificate_path.read_text())
            for tree, before in snapshots.items():
                if artifact_snapshot(tree) != before:
                    raise RuntimeError(f"staged compiler artifacts changed during measurement: {tree}")
            attach_strict_measurement(canonical, strict_rows, inventory, certified)
        for path, original in source_hashes.items():
            if source_fingerprint(path) != original:
                raise RuntimeError(f"source changed during the backend check: {path}")
        if frozen is not None:
            atomic_json(response, canonical)
            print(f"Paired frozen measurements checked: {len(eligible)} modules", flush=True)
            return
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
            report_name = "selected-official-axioms.json" if only or scoped else "official-axioms.json"
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
    modes.add_argument("--frozen-request", type=Path, help="measure eligible requested frozen modules")
    parser.add_argument("--official-measurement", type=Path, help="canonical Inspector response")
    parser.add_argument("--inspector", type=Path, help="prepared reportInspector executable")
    parser.add_argument("--frozen-output", type=Path, help="atomic paired Inspector response")
    args = parser.parse_args()
    if args.regenerate_facades:
        if args.modules or args.output:
            parser.error("--regenerate-facades takes no module selection or artifact output")
        regenerate_facades()
    elif args.frozen_request:
        if args.modules or args.output or not all((args.official_measurement, args.inspector, args.frozen_output)):
            parser.error("--frozen-request requires --official-measurement, --inspector and --frozen-output")
        frozen_measurement(args.frozen_request.resolve(), args.official_measurement.resolve(),
                           args.inspector.resolve(), args.frozen_output.absolute())
    else:
        if any((args.official_measurement, args.inspector, args.frozen_output)):
            parser.error("measurement options require --frozen-request")
        check(args.modules, args.backend, args.output)
