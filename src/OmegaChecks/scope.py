"""Select the Omega checks and compiler cache roots for a candidate change."""
from collections import defaultdict
from pathlib import Path

from portable import BASIS, ROOT, closure, consumers, import_graph, root


LIBRARIES = BASIS | {"OmegaMath"}
CHECK_ROOTS = LIBRARIES | {"OmegaChecks"}
AUDIT = "OmegaChecks.Audit"
CERTIFICATE = "OmegaChecks.Interface.Equations"
CHECK_INPUTS = {AUDIT, CERTIFICATE, "OmegaChecks.Portable.Exports", "OmegaChecks.Portable.ArtifactHashes",
                "OmegaBuild.Commands", "OmegaBuild.Plan"}
SHARED = {"lean-toolchain", "lakefile.toml", "lake-manifest.json",
          "src/OmegaChecks/check.py", "src/OmegaChecks/audit_cache.py", "src/OmegaChecks/portable.py",
          "src/OmegaChecks/scope.py", "src/OmegaChecks/strict_lake.py", "src/OmegaChecks/hosted.py",
          "src/OmegaChecks/test_backend_plan.py", "src/OmegaChecks/test_backend_scheduling.py"}
REG_INPUTS = {"Reg/lakefile.toml", "Reg/lake-manifest.json", "Meta/tools-release.json"}
FIBONACCI = "OmegaMathlib.Data.Nat.Fib.Basic"
IMPORTER_INPUTS = {"OmegaMath", "OmegaChecks.Portable.Common"}
REQUIRED_MODULES = CHECK_INPUTS | IMPORTER_INPUTS | {FIBONACCI}
REPORT_DIR = ".lake/build/omega-checks/"


def module_path(path):
    if not path.endswith(".lean"):
        return None
    if path in {"Trureturing.lean", "OmegaMathlib.lean"} or path.startswith(("D5/", "Reg/", "OmegaMathlib/")):
        return path.removesuffix(".lean").replace("/", ".")
    if path.startswith(("src/", "strict/")):
        directory, _, relative = path.partition("/")
        name = relative.removesuffix(".lean").replace("/", ".")
        if root(name) in (CHECK_ROOTS | {"OmegaBuild"} if directory == "src" else {"OmegaInit"}):
            return name
    return None


def plan(graph, official_basis, changed, missing, shared, reg_inputs):
    # Both sides can import a changed module, including a deleted target that
    # is still named by an import in the candidate.
    reverse = defaultdict(set)
    for imports in (graph, official_basis):
        for name, deps in imports.items():
            for dep in deps:
                reverse[dep].add(name)
    if unresolved := {name for name in missing if reverse[name] or name in REQUIRED_MODULES}:
        raise ValueError(f"missing changed Omega input still required by an import or check: {sorted(unresolved)}")
    strict_basis = {name for name in graph if root(name) in BASIS}
    if mismatch := strict_basis ^ official_basis.keys():
        raise ValueError(f"standard and strict module trees differ: {sorted(mismatch)}")

    check_inputs = closure(graph, CHECK_INPUTS & graph.keys())
    shared = sorted(set(shared) | (changed & set(check_inputs)))
    affected = set(graph) if shared else set(changed)
    if reg_inputs:
        affected.update(name for name in graph if root(name) in {"Reg", "LeanInformationAuditInterface"})
    pending = list(affected)
    while pending:
        for importer in reverse[pending.pop()] - affected:
            affected.add(importer)
            pending.append(importer)
    affected.intersection_update(graph)

    library = sorted(name for name in affected if root(name) in CHECK_ROOTS)
    basis = sorted(affected & strict_basis)
    downstream = sorted(affected & set(consumers(graph)))
    common = sorted(set(basis) | {name for name in downstream if name.startswith("OmegaChecks.Portable.")})
    return dict(shared=shared, library=library, basis=basis, consumers=downstream, common=common)


def discover(changed_file):
    raw = changed_file.read_bytes()
    if raw and not raw.endswith(b"\0"):
        raise ValueError(f"invalid NUL-separated changed paths: {changed_file}")
    paths = set(raw.decode().split("\0")) - {""}
    changed = {path: name for path in paths if (name := module_path(path))}
    shared = (paths & SHARED) | {path for path in paths if path == "src/OmegaChecks/InitCompiler.lean"
                                or path.startswith(("src/OmegaChecks/InitCompiler/", "src/OmegaChecks/InitPort/",
                                                    "strict/OmegaChecks/InitPort/"))}
    reg_inputs = paths & REG_INPUTS
    if not (changed or shared or reg_inputs):
        return plan({}, {}, set(), set(), [], [])
    _, graph = import_graph("lean", with_reg=True)
    _, official_basis = import_graph("lean", ("src/OmegaInit.lean", "src/OmegaInit/*.lean",
                                             "src/OmegaMathlib.lean", "src/OmegaMathlib/*.lean"),
                                     official_basis=True)
    missing = {name for path, name in changed.items() if not (ROOT / path).is_file()}
    if missing:
        print(f"Removed Omega scope inputs: {' '.join(sorted(missing))}", flush=True)
    return plan(graph, official_basis, set(changed.values()), missing, shared, reg_inputs)


def importer_affected(scope):
    return not IMPORTER_INPUTS.isdisjoint(scope["library"])


def cache_targets(scope):
    targets = set(scope["library"] + scope["basis"] + scope["consumers"] + scope["common"])
    if importer_affected(scope):
        targets.update(IMPORTER_INPUTS)
    if targets:
        targets.update({AUDIT, CERTIFICATE})
    return sorted(targets)


def report_file(scope):
    if scope["shared"]:
        return REPORT_DIR + "official-axioms.json"
    if scope["basis"] or scope["consumers"]:
        return REPORT_DIR + "selected-official-axioms.json"
    return ""
