"""Select the Omega checks and compiler cache roots for a candidate change."""
from collections import defaultdict
from pathlib import Path

from portable import BASIS, ROOT, closure, consumers, import_graph, root


LIBRARIES = BASIS
CHECK_ROOTS = LIBRARIES | {"OmegaChecks"}
AUDIT = "OmegaChecks.Audit"
CERTIFICATE = "OmegaChecks.Interface.Equations"
CHECK_INPUTS = {AUDIT, CERTIFICATE, "OmegaChecks.QualifiedReferences", "OmegaChecks.RetiredDeclarations", "OmegaChecks.StandardUses",
                "OmegaChecks.Portable.Exports", "OmegaChecks.Portable.ArtifactHashes"}
SHARED = {"lean-toolchain", "lakefile.toml", "lake-manifest.json",
          "src/OmegaChecks/check.py", "src/OmegaChecks/portable.py",
          "src/OmegaChecks/scope.py", "src/OmegaChecks/strict_lake.py",
          "src/OmegaChecks/retirement.py", "src/OmegaChecks/test_retirement.py",
          "src/OmegaChecks/test_object_origins.py"}
REG_INPUTS = {"Reg/lakefile.toml", "Reg/lake-manifest.json", "Meta/tools-release.json"}
FIBONACCI = "OmegaMathlib.Data.Nat.Fib.Basic"
IMPORTER_INPUTS = {"OmegaMathlib", "OmegaChecks.Portable.Common"}
REQUIRED_MODULES = CHECK_INPUTS | IMPORTER_INPUTS | {FIBONACCI}
REPORT_DIR = ".lake/build/omega-checks/"


def module_path(path):
    if not path.endswith(".lean"):
        return None
    if path == "Trureturing.lean" or path.startswith(("D5/", "Reg/")):
        return path.removesuffix(".lean").replace("/", ".")
    if path.startswith(("src/", "strict/")):
        directory, _, relative = path.partition("/")
        name = relative.removesuffix(".lean").replace("/", ".")
        if directory == "src" or root(name) in BASIS | {"OmegaMath"}:
            return name
    return None


def plan(graph, official_basis, changed, missing, shared, reg_inputs, protected_clients=()):
    # Both sides can import a changed module, including a deleted target that
    # is still named by an import in the candidate.
    reverse = defaultdict(set)
    for imports in (graph, official_basis):
        for name, deps in imports.items():
            for dep in deps:
                reverse[dep].add(name)
    if unresolved := {name for name in missing if reverse[name] or name in REQUIRED_MODULES}:
        raise ValueError(f"missing changed Omega input still required by an import or check: {sorted(unresolved)}")
    if removed := set(protected_clients) - graph.keys():
        raise ValueError(f"missing protected retirement consumers: {sorted(removed)}")
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
    downstream = sorted(affected & set(consumers(graph, protected_clients)))
    common = sorted(set(basis) | {name for name in downstream if name.startswith("OmegaChecks.Portable.")})
    return dict(shared=shared, library=library, basis=basis, consumers=downstream, common=common)


def discover(changed_file, base=None):
    raw = changed_file.read_bytes()
    if raw and not raw.endswith(b"\0"):
        raise ValueError(f"invalid NUL-separated changed paths: {changed_file}")
    paths = set(raw.decode().split("\0")) - {""}
    changed = {path: name for path in paths if (name := module_path(path))}
    shared = paths & SHARED
    reg_inputs = paths & REG_INPUTS
    if not (changed or shared or reg_inputs):
        return plan({}, {}, set(), set(), [], [])
    from retirement import protected_omega_consumers
    protected = protected_omega_consumers(base) if base else ()
    _, graph = import_graph("lean", with_reg=True)
    _, official_basis = import_graph("lean", ("src/OmegaInit*.lean", "src/OmegaMathlib*.lean"),
                                     official_basis=True)
    missing = {name for path, name in changed.items() if not (ROOT / path).is_file()}
    if missing:
        print(f"Removed Omega scope inputs: {' '.join(sorted(missing))}", flush=True)
    return plan(graph, official_basis, set(changed.values()), missing, shared, reg_inputs, protected)


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
