"""Run from anywhere in this checkout. --incremental temporarily edits two clean sources."""
import argparse
from functools import cache
from graphlib import TopologicalSorter
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

import portable
import scope as affected_scope
from portable import BASIS, closure, import_graph, root
from strict_lake import BUILD, COMMON_SRC, lake_layout, strict_config

ROOT = Path(__file__).resolve().parents[2]
LIB = ROOT / BUILD / "lib/lean"
SRC = ROOT / "src"


STRICT = BASIS
TOPIC = "D5.S3.Geometry.ProjectiveCoordinates.Scaling"
AUDIT = ROOT / ".lake/build/bin/omegaAudit"
# Resolved once: each `lake env` call re-reads the workspace configuration.
ENV = {}
FIB_ITERATOR = """Omega.Nat.rec (motive := fun _ => Omega.Bool → Omega.Nat)
    (Omega.Bool.rec Omega.Nat.zero Omega.Nat.zero.succ)
    (fun _ pair => Omega.Bool.rec (pair .true) ((pair .true).add (pair .false))) n .false"""


def run(*args):
    return subprocess.run(args, cwd=ROOT, text=True, check=True)


def build(targets):
    run("lake", "-f", strict_config(), "build", *("+" + target for target in targets))


@cache
def library_graph():
    # Lake's source roots agree in both configurations except for the basis facades.
    return import_graph(ENV["LEAN"])[1]


def terminal_modules(graph, names):
    imported = {dep for name in names for dep in graph[name]}
    return sorted(set(names) - imported)


def check_library(selected=()):
    graph = library_graph()
    for name in selected:
        if name not in graph or root(name) not in STRICT | {"OmegaChecks"}:
            raise ValueError(f"unknown Omega module {name}")
    # Imported-only modules and new modules outside an umbrella are both in scope.
    if not selected or "OmegaChecks.Audit" in selected:
        modules = sorted(name for name in graph if root(name) in STRICT)
    else:
        modules = [name for name in closure(graph, selected) if root(name) in STRICT]
    roots = terminal_modules(graph, modules)
    targets = set(roots) | set(selected)
    if not selected:
        # Build every external witness against the actual strict implementation.
        external = [name for name in graph if root(name) == "OmegaChecks"]
        targets.update(terminal_modules(graph, external))
    build(sorted(targets))
    if roots:
        subprocess.run([AUDIT, "--exact-roots", LIB, *roots, "--", *modules],
                       cwd=ROOT, env=audit_environment(), check=True)


def lake_environment():
    script = "import json, os; print(json.dumps(dict(os.environ)))"
    output = subprocess.run(["lake", "-f", strict_config(), "env", sys.executable, "-c", script], cwd=ROOT,
                            stdout=subprocess.PIPE, text=True, check=True).stdout
    return json.loads(output)


def lean(*args, **options):
    return subprocess.run([ENV["LEAN"], *map(str, args)], cwd=ROOT, env=ENV, text=True, check=True, **options)


def audit_environment():
    # The reference certificates are built by ordinary Lake. The audit explicitly
    # sets a separate strict-only search path when it loads its inputs.
    official = ROOT / ".lake/build/lib/lean"
    return {**ENV, "LEAN_PATH": os.pathsep.join([str(official), ENV["LEAN_PATH"]])}


def audit(name, modules, paths, error=None):
    args = [AUDIT, "--exact", name, os.pathsep.join(map(str, paths)), *modules]
    result = subprocess.run(args, cwd=ROOT, env=audit_environment(), capture_output=True, text=True)
    output = result.stdout + result.stderr
    if error is None:
        if result.returncode:
            raise RuntimeError(output)
        print(output.strip(), flush=True)
    elif not result.returncode or error not in output:
        raise RuntimeError(f"Expected audit failure containing {error!r}: {output}")
    else:
        print(f"{name}: rejected ({error})", flush=True)


def check_audits():
    check_library()
    check_representation()
    build(["OmegaChecks.ModuleSurface"])
    with tempfile.TemporaryDirectory(prefix="omega-olean-") as tmp:
        tmp = Path(tmp)
        for name, source, reason in [
            ("UnusedAxiom", "module\nprelude\nimport OmegaInit.Prelude\npublic axiom hiddenAssumption : Prop\n",
             "hiddenAssumption"),
            ("ImplicitInit", "module\nimport OmegaInit.Prelude\n", "unknown module prefix 'Init'"),
        ]:
            source_file = tmp / f"{name}.lean"
            source_file.write_text(source)
            lean("-R", tmp, "-o", tmp / f"{name}.olean", source_file)
            audit(name, ["OmegaInit.Prelude", name], [tmp, LIB], reason)
    check_standard_admission()
    check_module_surface()
    check_consumer_exports()
    run(sys.executable, "-B", SRC / "OmegaChecks/test_object_origins.py")
    run(sys.executable, "-B", SRC / "OmegaChecks/test_retirement.py")


def check_consumer_exports():
    name = "ConsumerExportProbe"
    local = ("public def A.item : Prop := ∀ p : Prop, p → p\n"
             "public def B.item : Prop := ∀ p q : Prop, p → q → p\n")
    alias = "namespace Visible\nexport A (item)\nend Visible\n"
    generated = "public inductive Choice where | first | second\n"
    size_of = ("public import Init\npublic import OmegaInit.Prelude\n"
               "public structure Wrapper where value : Omega.Nat\n"
               "public noncomputable def derivedSize : Nat := sizeOf (Wrapper.mk Omega.Nat.zero.succ)\n")
    field = ("public import OmegaInit.Prelude\npublic section\n"
             "abbrev FieldReceiver := Omega.Nat\n"
             "def Omega.Nat.projectField (value : FieldReceiver) := value\n")
    field_alias = "namespace Nat\nexport _root_.Omega.Nat (projectField)\nend Nat\n"
    alias_method = (field.replace("def Omega.Nat.", "def Example.")
                    + "namespace Omega.Nat\nexport _root_.Example (projectField)\nend Omega.Nat\n")
    official = audit_environment()
    with tempfile.TemporaryDirectory(prefix="omega-exports-") as directory:
        tmp = Path(directory)
        for strict_code, official_code, error, marker in [
            (field + field_alias, field + field_alias, False, "Compared"),
            (field, field, True, "field resolution mismatch for Omega.Nat.projectField"),
            (alias_method, alias_method, True, "field resolution mismatch for Omega.Nat.projectField"),
            ((field + field_alias).replace("projectField", "gcd"),
             (field + field_alias).replace("projectField", "gcd"), True,
             "field resolution mismatch for Omega.Nat.gcd"),
            (local + alias, local + alias, False, "Compared"),
            (local + alias, local, True, "missing consumer alias Visible.item for A.item"),
            (local, local + alias, True, "additional official-side consumer alias Visible.item for A.item"),
            (local + alias, local + alias.replace("export A", "export B"), True,
             "missing consumer alias Visible.item for A.item"),
            ("public import OmegaInit.Prelude\nnamespace Public\nexport Omega.And (left)\nend Public",
             "public import OmegaInit.Prelude\nnamespace Public\nexport Omega.And (left)\nend Public",
             False, "1 roots"),
            (generated, generated, False, "Choice.casesOn"),
            (size_of + "example : derivedSize = 1 := rfl\n",
             size_of + "example : derivedSize = 2 := rfl\n", True, "Wrapper"),
            (local, "public import Lean\n" + local + "public section\nrun_meta do\n"
             "  discard <| Lean.Meta.getEqnsFor? `Nat.mul\n"
             "  discard <| Lean.Meta.getUnfoldEqnFor? `Nat.mul", False, "Nat.mul.eq_1"),
            (local, "public import Lean\n" + local + "public section\nopen Lean in\nrun_cmd Elab.Command.liftCoreM do\n"
             "  addDecl (.thmDecl {name := `Nat.mul.eq_1, levelParams := [], "
             "type := mkConst `True, value := mkConst `True.intro})", True,
             "additional official-side consumer export Nat.mul.eq_1"),
            (local, local + "public def proof_manual := A.item\n", True,
             "additional official-side consumer export proof_manual"),
            (local, local + "private def proof_internal := A.item\n", False, "Compared"),
            (generated, "set_option genCtorIdx false in\n" + generated +
             "public def Choice.ctorIdx (_ : Choice) : Nat := 0\n", True,
             "additional official-side consumer export Choice.ctorIdx"),
        ]:
            paths = []
            for side, header, body, env in [("strict", "module\nprelude\n", strict_code, ENV),
                                            ("official", "module\n", official_code, official)]:
                base = tmp / side
                base.mkdir(exist_ok=True)
                path = base / (name + ".lean")
                path.write_text(header + body + "\n")
                subprocess.run([env["LEAN"], "-R", base, "-o", path.with_suffix(".olean"), path],
                               cwd=ROOT, env=env, check=True)
                paths.append(os.pathsep.join([str(base), env["LEAN_PATH"]]))
            result = subprocess.run([AUDIT, "--consumer", *paths, name], cwd=ROOT, env=official,
                                    text=True, capture_output=True)
            if (result.returncode != 0) != error or marker not in result.stdout + result.stderr:
                raise RuntimeError(f"Expected {marker!r}: {result.stdout}{result.stderr}")


def check_representation():
    # Legacy importers load private .olean data. Cover ordinary elaboration in both file formats.
    examples = [
        ("p", "Omega.And.left h", None),
        ("p", "h p (fun hp _ => hp)", "Function expected"),
        ("∀ r : Prop, (p → q → r) → r", "h", "Type mismatch"),
        ("p", "by\n  change ∀ r : Prop, (p → q → r) → r at h\n  exact h p (fun hp _ => hp)",
         "'change' tactic failed"),
    ]
    consumers = [
        ("import OmegaInit.Prelude\n" + f"example {{p q : Prop}} (h : Omega.And p q) : {goal} := {term}\n", error)
        for goal, term, error in examples
    ]
    consumers.append(("import OmegaMathlib.Data.Nat.Fib.Basic\n"
                      f"example (n : Omega.Nat) : Omega.Eq (Omega.Nat.fib n) ({FIB_ITERATOR}) := Omega.rfl\n",
                      "Type mismatch"))
    consumers.append(("import OmegaInit.Prelude\n"
                      "example (a : Omega.Nat) : Omega.Eq a.pred "
                      "(Omega.Nat.rec Omega.Nat.zero (fun n _ => n) a) := Omega.rfl\n", "Type mismatch"))
    for lake in [["lake"], ["lake", "-f", strict_config()]]:
        for header in ["", "module\n"]:
            for consumer, error in consumers:
                source = header + consumer
                result = subprocess.run([*lake, "env", "lean", "--stdin"], cwd=ROOT,
                                        input=source, capture_output=True, text=True)
                output = result.stdout + result.stderr
                if error is None and result.returncode or error is not None and (
                    result.returncode == 0 or error.lower() not in output.lower()
                ):
                    raise RuntimeError(f"Unexpected consumer result for {lake}:\n{source}\n{output}")


def check_fibonacci_reduction():
    profiles = {"publication": (False, None), "common": (False, COMMON_SRC), "strict": (True, None)}
    module = "OmegaMathlib.Data.Nat.Fib.Basic"
    for mode, (strict, common_dir) in profiles.items():
        lake, _ = lake_layout(strict, False, common_dir)
        path = subprocess.check_output([*lake, "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True).strip()
        for header in ("", "module\n"):
            prefix = header + f"import {module}\n"
            named = "example : Omega.Eq (Omega.Nat.fib Omega.Nat.zero) Omega.Nat.zero := Omega.Nat.fib_zero\n"
            # Check the endpoints and an input whose evaluation uses several additions.
            closed = [f"example : Omega.Eq (Omega.Nat.fib Omega.Nat.zero{'.succ' * n}) "
                      f"Omega.Nat.zero{'.succ' * value} := Omega.rfl\n" for n, value in [(0, 0), (5, 5)]]
            boolean = f"example (n : Omega.Nat) : Omega.Eq (Omega.Nat.fib n) ({FIB_ITERATOR}) := Omega.rfl\n"
            for body, accepts in [(named, True), (boolean, False), *((s, mode == "publication") for s in closed)]:
                proc = subprocess.run([ENV["LEAN"], "--stdin"], input=prefix + body, cwd=ROOT, text=True,
                                      env={**os.environ, "LEAN_PATH": path}, capture_output=True)
                if accepts != (proc.returncode == 0) or (not accepts and "type mismatch" not in proc.stdout.lower()):
                    raise RuntimeError(f"Unexpected Fibonacci reduction in {mode}:\n{prefix}{body}{proc.stdout}{proc.stderr}")


def check_module_surface():
    port = "OmegaMathlib.Logic.Function.Defs"
    prelude = "OmegaInit.Prelude"
    core = "OmegaInit.Core"
    for lake in [["lake"], ["lake", "-f", strict_config()]]:
        header = "module\nprelude\nimport OmegaInit.Data.Nat.Basic\nopen Omega.Nat\n"
        for expression, visible in [("Omega.Nat.add_comm", True), ("add_comm", False)]:
            result = subprocess.run([*lake, "env", "lean", "--stdin"], cwd=ROOT,
                                    input=header + f"#check {expression}\n", capture_output=True, text=True)
            if (result.returncode == 0) != visible or (not visible and "unknownIdentifier" not in result.stdout):
                raise RuntimeError(f"Unexpected visibility of {expression}: {result.stdout}{result.stderr}")
    with tempfile.TemporaryDirectory(prefix="omega-module-") as directory:
        tmp = Path(directory)
        # Lean resolves a module prefix in the first matching directory on the search path.
        (tmp / "OmegaInit").mkdir()
        for artifact in (LIB / "OmegaInit").glob("Prelude.*"):
            (tmp / "OmegaInit" / artifact.name).symlink_to(artifact)
        for name, imports, body, reason in [
            ("OmegaMathlib.EmptyModuleProbe", [], "", "no official module Mathlib.EmptyModuleProbe"),
            ("OmegaInit.EmptyModuleProbe", [], "", "no official module Init.EmptyModuleProbe"),
            (port, [prelude], "namespace And\nexport Omega.And (left)\nend And", None),
            (core, [prelude], "namespace And\nexport Omega.And (left)\nend And", None),
            (core, [prelude], "import all OmegaInit.Prelude\nattribute [local semireducible] Omega.Nat.add", None),
            (port, [prelude], "attribute [class] Omega.True", "public class registration mismatch for Omega.True"),
            (core, [prelude], "attribute [class] Omega.True", "public class registration mismatch for Omega.True"),
            ("OmegaInit", [prelude], "attribute [class] Omega.True", "unmatched class registration"),
            (core, [prelude], "import all OmegaInit.Prelude\nset_option allowUnsafeReducibility true in\n"
             "attribute [semireducible] Omega.Nat.add",
             "unverified public reducibility override for Omega.Nat.add"),
            ("OmegaInit.Data.Nat.Basic", [prelude],
             "import all OmegaInit.Prelude\nattribute [local semireducible] Omega.Nat.mul\n"
             "public theorem Omega.Nat.mul_zero (n : Omega.Nat) : "
             "Omega.Eq (n.mul Omega.Nat.zero) Omega.Nat.zero := Omega.rfl",
             "protected modifier mismatch for Omega.Nat.mul_zero"),
            (core, [prelude], "@[expose, match_pattern] public def Omega.Iff (a b : Prop) := "
             "Omega.And (a → b) (b → a)", "unmatched match_pattern attribute for Omega.Iff"),
            (core, [], "noncomputable section\n@[simp] public abbrev Omega.inline {α : Sort u} (a : α) := a", None),
            (core, [prelude], "@[simp] public abbrev Omega.Iff (a b : Prop) := Omega.And (a → b) (b → a)",
             "unmatched public simp unfolding for Omega.Iff"),
            (core, [prelude], "namespace Omega.OnlyHere\nexport Omega.And (left)\nend Omega.OnlyHere",
             "unmatched public alias Omega.OnlyHere.left"),
            ("OmegaInit", [prelude], "namespace Omega.OnlyHere\nexport Omega.And (left)\nend Omega.OnlyHere",
             "unmatched export alias in the OmegaInit umbrella"),
            (port, [prelude], "namespace Omega.PublicProjection\nexport Omega.And (left)\nend Omega.PublicProjection",
             "unmatched public alias Omega.PublicProjection.left"),
            (port, [prelude], "namespace Nat\nexport Omega.Bool (rec)\nend Nat", "unmatched public alias Nat.rec"),
        ]:
            source = tmp.joinpath(*name.split(".")).with_suffix(".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            header = ["module", "prelude", *("public import " + dep for dep in imports)]
            source.write_text("\n".join([*header, body, ""]))
            lean("-R", tmp, "-o", source.with_suffix(".olean"), source)
            audit(name, [*imports, name], [tmp, LIB], reason)

        # Supply the class-registering artifact to a fresh client and use the same expression
        # with the standard facade. The two actual elaboration results motivate the rejection.
        fixture = tmp / "ClassRegistration.lean"
        fixture.write_text("module\nprelude\npublic import OmegaInit.Prelude\nattribute [class] Omega.True\n")
        lean("-R", tmp, "-o", fixture.with_suffix(".olean"), fixture)
        for env, module, accepted in [(ENV, "ClassRegistration", True),
                                      (audit_environment(), prelude, False)]:
            source = f"module\nprelude\nimport {module}\nexample [h : Omega.True] : Omega.True := h\n"
            env = {**env, "LEAN_PATH": os.pathsep.join([str(tmp), env["LEAN_PATH"]])} if accepted else env
            result = subprocess.run([env["LEAN"], "--stdin"], env=env, cwd=ROOT,
                                    input=source, text=True, capture_output=True)
            if (result.returncode == 0) != accepted or (not accepted and "invalid binder annotation" not in result.stdout):
                raise RuntimeError(f"Unexpected class-binder result for {module}: {result.stdout}{result.stderr}")

        for name in [core, "OmegaInit"]:
            source = tmp.joinpath(*name.split(".")).with_suffix(".lean")
            source.write_text(f"module\nprelude\npublic import all {prelude}\n")
            result = subprocess.run([ENV["LEAN"], "-R", tmp, source], cwd=ROOT, env=ENV,
                                    capture_output=True, text=True)
            if result.returncode == 0 or "cannot use `all` with `public import`" not in result.stdout:
                raise RuntimeError(f"Expected Lean to reject public import all: {result.stdout}{result.stderr}")

        # Import the syntax infrastructure to produce a real public parser entry.
        # The layer audit independently rejects that import in a strict library.
        probe = tmp / "SyntaxProbe.lean"
        probe.write_text("""import OmegaChecks.ModuleSurface
open Lean
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  searchPathRef.modify (System.FilePath.mk args.head! :: ·)
  let env ← importModules #[{module := args[1]!.toName}] {} (level := .exported)
  discard <| OmegaChecks.ModuleSurface.check env
""")
        with tempfile.TemporaryDirectory(prefix="omega-class-") as directory:
            classes = Path(directory)
            definition = classes / "OmegaInit/Prelude.lean"
            definition.parent.mkdir()
            # Exercise just the elaborator metadata, including both output-position arrays.
            nonempty = "public axiom Omega.Nonempty (α : Sort u) : Prop"
            registered = nonempty + "\nattribute [class] Omega.Nonempty"
            for body, accepted in [
                (registered, True),
                (nonempty, False),
                (registered + "\nattribute [univ_out_params u] Omega.Nonempty", False),
                ("public axiom Omega.HAdd (α : Type u) (β : Type v) (γ : Type w) : Type\n"
                 "attribute [class] Omega.HAdd\nattribute [univ_out_params w] Omega.HAdd", False),
            ]:
                definition.write_text("module\nprelude\n" + body + "\n")
                lean("-R", classes, "-o", definition.with_suffix(".olean"), definition)
                result = subprocess.run([ENV["LEAN"], "--run", probe, classes, prelude], cwd=ROOT, env=ENV,
                                        capture_output=True, text=True)
                if ((result.returncode == 0) != accepted or
                        (not accepted and "public class registration mismatch" not in result.stderr)):
                    raise RuntimeError(f"Unexpected class metadata for {body}: {result.stdout}{result.stderr}")
        for name, body, kind in [
            (port, 'notation "$$$" => Omega.True', "parser"),
            (core, 'notation "$$$" => Omega.True', "parser"),
            (core, 'public instance : Inhabited Omega.Nat := ⟨Omega.Nat.zero⟩', "instance"),
            (core, '@[deprecated "use Omega.True.intro" (since := "1")] public theorem '
             'Omega.oldIntro : Omega.True := Omega.True.intro', "environment extension"),
        ]:
            source = tmp.joinpath(*name.split(".")).with_suffix(".lean")
            source.write_text(f"module\nprelude\npublic import Lean\npublic import {prelude}\n{body}\n")
            lean("-R", tmp, "-o", source.with_suffix(".olean"), source)
            result = subprocess.run([ENV["LEAN"], "--run", probe, tmp, name], cwd=ROOT, env=ENV,
                                    capture_output=True, text=True)
            if result.returncode == 0 or f"no elaboration correspondence for public {kind}" not in result.stderr:
                raise RuntimeError(f"Expected {kind} rejection in {name}: {result.stdout}{result.stderr}")


def check_standard_admission():
    # Compile the negative fixtures against the same upstream artifacts as the admitted library.
    init = "OmegaInit.Data.Nat.Basic"
    prime = "OmegaMathlib.Data.Nat.Prime.Defs"
    with tempfile.TemporaryDirectory(prefix="omega-pred-") as directory:
        tmp = Path(directory)
        prelude = "OmegaInit.Prelude"
        source = tmp / "OmegaInit/Prelude.lean"
        source.parent.mkdir()
        source.write_text("module\nprelude\n@[expose] public section\nnamespace Omega\n"
                          "inductive Nat where\n  | zero\n  | succ (n : Nat)\n"
                          "@[no_expose] noncomputable def Nat.pred : Nat → Nat := Nat.rec Nat.zero (fun n _ => n)\n"
                          "end Omega\n")
        lean("-R", tmp, "-o", source.with_suffix(".olean"), source)
        audit(prelude, [prelude], [tmp], "legacy importer can unfold the hidden implementation of Omega.Nat.pred")
    with tempfile.TemporaryDirectory(prefix="omega-name-") as tmp:
        tmp = Path(tmp)
        for name, declaration, error in [
            (init, "def Omega.Nat.add", "official owner of Nat.add is Init.Prelude"),
            (init, "def OutsideOmega", "public name outside Omega"),
            (init, "def Omega.Nat.unknownOfficialName", "missing official declaration Nat.unknownOfficialName"),
            (prime, "def Omega.Nat.Prime", "public binder mismatch for Omega.Nat.Prime"),
            (prime, "def Omega.Nat.unknownMathlibName", "missing official declaration Nat.unknownMathlibName"),
            (prime, "def Omega.Nat.add", "official owner of Nat.add is Init.Prelude"),
        ]:
            source = tmp / (name.replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text(f"module\nprelude\npublic {declaration} : Prop := ∀ p : Prop, p → p\n")
            lean("-R", tmp, "-o", source.with_suffix(".olean"), source)
            audit(name, [name], [tmp], error)
    with tempfile.TemporaryDirectory(prefix="omega-interface-") as directory:
        tmp = Path(directory)
        always_prime = tmp / "OmegaMathlib/Data/Nat/Prime/Defs.lean"
        always_prime.parent.mkdir(parents=True)
        always_prime.write_text("module\nprelude\npublic import OmegaInit.Prelude\n"
                                "/-! Omega original. -/\n"
                                "public def Omega.Nat.Prime (_ : Omega.Nat) : Prop := Omega.True\n")
        lean("-R", tmp, "-o", always_prime.with_suffix(".olean"), always_prime)
        audit(prime, ["OmegaInit.Prelude", prime], [tmp, LIB], "certificate statement mismatch for Omega.Nat.Prime")
        fib = "OmegaMathlib.Data.Nat.Fib.Basic"
        altered = tmp / "OmegaMathlib/Data/Nat/Fib/Basic.lean"
        altered.parent.mkdir(parents=True)
        altered.write_text("module\nprelude\npublic import OmegaInit.Prelude\n"
                           "public def Omega.Nat.fib (n : Omega.Nat) : Omega.Nat := n\n")
        lean("-R", tmp, "-o", altered.with_suffix(".olean"), altered)
        audit(fib, ["OmegaInit.Prelude", fib], [tmp, LIB], "certificate statement mismatch for Omega.Nat.fib")
        altered.write_text("module\nprelude\npublic import OmegaInit.Prelude\n"
                           f"public noncomputable def Omega.Nat.fib (n : Omega.Nat) : Omega.Nat := {FIB_ITERATOR}\n")
        lean("-R", tmp, "-o", altered.with_suffix(".olean"), altered)
        audit(fib, ["OmegaInit.Prelude", fib], [tmp, LIB],
              "legacy importer can unfold the hidden implementation of Omega.Nat.fib")
        # A transitive dependency on project-specific mathematics invalidates a standard port.
        reverse = tmp / "OmegaMathlib/Reverse.lean"
        reverse.write_text("module\nprelude\nimport D5.S0.Arithmetic.Exact.Nat\n")
        lean("-R", tmp, "-o", reverse.with_suffix(".olean"), reverse)
        audit("OmegaMathlib.Reverse", [*closure(library_graph(), ["D5.S0.Arithmetic.Exact.Nat"]), "OmegaMathlib.Reverse"],
              [tmp, LIB], "forbidden strict import")


def versions(artifacts):
    return {name: path.stat().st_mtime_ns for name, path in artifacts.items()}


def check_incremental():
    graph = library_graph()
    # Track the strict libraries and every mathematical check importing them.
    imports = {}
    for name in TopologicalSorter(graph).static_order():
        deps = graph.get(name, ())
        if root(name) in STRICT or any(dep in imports for dep in deps):
            imports[name] = {name}.union(*(imports[dep] for dep in deps if dep in imports))
    modules = sorted(imports)
    targets = terminal_modules(graph, modules)
    build(targets)
    artifacts = {name: LIB / (name.replace(".", "/") + ".olean") for name in modules}
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = ROOT / manifest["packagesDir"] / "mathlib/.lake/build/lib/lean"
    for name in modules:
        for dep in graph[name]:
            if root(dep) == "Mathlib":
                artifacts[dep] = mathlib / (dep.replace(".", "/") + ".olean")

    def dependents(module):
        return {name for name in modules if module in imports[name]}

    probes = [
        ("D5/S3/Geometry/SeparateTopicProbe.lean", None,
         "module\nprelude\npublic import OmegaInit\n", set()),
        ("D5/S3/Geometry/ProjectiveCoordinates/Scaling.lean", "he.symm\n", "he.symm.symm.symm\n", {TOPIC}),
        ("D5/S3/Geometry/ProjectiveCoordinates/Scaling.lean", None,
         "\npublic theorem Omega.Projective.probe (p : Omega.Nat) : Omega.Eq p p := Omega.rfl\n",
         dependents(TOPIC)),
        ("strict/OmegaInit/Prelude.lean", None,
         "\npublic theorem Omega.congrFun' {α β : Sort u} {f g : α → β} (h : Omega.Eq f g) (a : α) : Omega.Eq (f a) (g a) := Omega.congrArg (fun k : α → β => k a) h\n",
         dependents("OmegaInit.Prelude")),
    ]
    for filename, replace, text, expected in probes:
        path = ROOT / filename
        run("git", "diff", "--quiet", "HEAD", "--", filename)
        before = versions(artifacts)
        new_file = not expected
        original = b"" if new_file else path.read_bytes()
        if replace is None:
            modified = original + text.encode()
        else:
            if original.count(replace.encode()) != 1:
                raise RuntimeError(f"Expected one proof fragment in {filename}")
            modified = original.replace(replace.encode(), text.encode())
        with path.open("xb" if new_file else "wb") as out:
            out.write(modified)
        try:
            build(targets)
            after = versions(artifacts)
            changed = {m for m in after if before[m] != after[m]}
            print(f"{filename}: rebuilt {sorted(changed)}", flush=True)
            if changed != expected:
                raise RuntimeError(f"Expected {sorted(expected)}")
        finally:
            if path.read_bytes() != modified:
                raise RuntimeError(f"{filename} changed during the probe; leaving it intact")
            if new_file:
                path.unlink()
            else:
                path.write_bytes(original)
            build(targets)


def check_ordinary_importer():
    # A fresh ordinary importer must be able to apply project declarations to official types.
    for name in ("OmegaMath", "OmegaMath.Arithmetic.Euclidean.Prime"):
        result = subprocess.run(["lake", "query", f"+{name}:lean"], cwd=ROOT, text=True,
                                capture_output=True)
        if not result.returncode or f"unknown module `{name}`" not in result.stderr:
            raise RuntimeError(f"retired import {name} is still available or could not be tested: {result.stderr}")
    run("lake", "build", *("+" + name for name in sorted(affected_scope.IMPORTER_INPUTS)))
    subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT, check=True, text=True, input="""
import OmegaMathlib
import OmegaChecks.Portable.Common
example : Nat.fib 0 = 0 := rfl
example : Nat.fib 5 = 5 := rfl
example (n : Nat) : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) :=
  OmegaChecks.Portable.Common.fibonacciRecurrence n
example {p q : Prop} (h : p ∧ q) : p := OmegaChecks.Portable.Common.projectLeft h
""")


def full_check(incremental=False, protected=()):
    manifest = ROOT / "lake-manifest.json"
    initial = manifest.read_bytes()
    check_ordinary_importer()
    # The compiled driver runs the current Audit.lean without elaborating it for every audit.
    run("lake", "build", "omegaAudit")
    check_audits()
    portable.check([], "both", protected=protected)
    check_fibonacci_reduction()
    if incremental:
        check_incremental()
    if manifest.read_bytes() != initial:
        raise RuntimeError("Lake manifest changed")
    print("manifest SHA-256:", hashlib.sha256(initial).hexdigest())


def scoped_check(scope):
    if scope["shared"]:
        print(f"Shared Omega inputs changed: {' '.join(scope['shared'])}", flush=True)
        ENV.update(lake_environment())
        full_check(protected=scope["consumers"])
        return
    if not affected_scope.cache_targets(scope):
        print("No affected Omega modules", flush=True)
        return
    print(f"Affected Omega library and witness targets: {' '.join(scope['library'])}", flush=True)
    if scope["library"]:
        ENV.update(lake_environment())
        run("lake", "build", "omegaAudit")
        check_library(scope["library"])
    if affected_scope.importer_affected(scope):
        check_ordinary_importer()
    if affected_scope.report_file(scope):
        portable.check(scope["consumers"], "both", basis_roots=scope["basis"], common_roots=scope["common"],
                       protected=scope["consumers"])
    if affected_scope.FIBONACCI in scope["basis"]:
        check_fibonacci_reduction()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--incremental", action="store_true")
    modes.add_argument("--library", nargs="*", metavar="MODULE",
                       help="build selected Omega modules and audit their strict import closure")
    modes.add_argument("--full", action="store_true", help="run the complete audit and regression probes")
    modes.add_argument("--write-scope", type=Path, help="plan from the CI changed-path manifest")
    parser.add_argument("--changed", type=Path, default=os.environ.get("CI_CHANGED_PATHS_FILE"))
    parser.add_argument("--scope", type=Path, default=os.environ.get("OMEGA_SCOPE_FILE"))
    parser.add_argument("--cache-targets", type=Path, help="write the cache restore roots during planning")
    parser.add_argument("--protected-base", default=os.environ.get("CI_BASE"),
                        help="protected revision supplied by the PR or push selection")
    args = parser.parse_args()
    if args.protected_base and not (args.library is not None or args.write_scope):
        run(sys.executable, "-B", SRC / "OmegaChecks/retirement.py", "--verify",
            "--protected-base", args.protected_base,
            "--output", ROOT / ".lake/build/omega-checks/retirement.json")
    if args.write_scope:
        if not args.changed or not args.cache_targets or args.scope:
            parser.error("--write-scope requires --changed and --cache-targets")
        scope = affected_scope.discover(args.changed, args.protected_base)
        args.write_scope.write_text(json.dumps(scope) + "\n")
        targets = affected_scope.cache_targets(scope)
        args.cache_targets.write_text("".join(name + "\n" for name in targets))
        report = affected_scope.report_file(scope)
        if output := os.environ.get("GITHUB_OUTPUT"):
            with open(output, "a") as stream:
                if targets:
                    print(f"targets-file={args.cache_targets}", file=stream)
                if report:
                    print(f"report-file={report}", file=stream)
        print(f"Omega scope: {len(targets)} cache roots, {len(scope['consumers'])} consumer targets, "
              f"{len(scope['common'])} common targets", flush=True)
    elif args.library is not None:
        ENV.update(lake_environment())
        check_library(args.library)
    elif args.full or args.incremental or not (args.scope or args.changed):
        ENV.update(lake_environment())
        full_check(args.incremental)
    else:
        scope = json.loads(args.scope.read_text()) if args.scope else affected_scope.discover(args.changed, args.protected_base)
        scoped_check(scope)
