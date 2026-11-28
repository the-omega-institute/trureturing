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
from strict_lake import BUILD, COMMON_SRC, build_profiles, lake_layout, strict_config, isolated_config

ROOT = Path(__file__).resolve().parents[2]
LIB = ROOT / BUILD / "lib/lean"
SRC = ROOT / "src"


STRICT = BASIS | {"OmegaMath"}
TOPIC = "OmegaMath.Projective"
AUDIT = ROOT / ".lake/build/bin/omegaAudit"
# Resolved once: each `lake env` call re-reads the workspace configuration.
ENV = {}
FIB_ITERATOR = """Omega.Nat.rec (motive := fun _ => Omega.Bool → Omega.Nat)
    (Omega.Bool.rec Omega.Nat.zero Omega.Nat.zero.succ)
    (fun _ pair => Omega.Bool.rec (pair .true) ((pair .true).add (pair .false))) n .false"""


def run(*args):
    return subprocess.run(args, cwd=ROOT, text=True, check=True)


def build(targets):
    selections = {"+" + name: {name} for name in targets}
    result = build_profiles(library_graph(), selections)
    if result:
        raise subprocess.CalledProcessError(result, ["lake", "build", *selections])


def extend_project_imports(lean, graph, targets=()):
    # A witness can reach a marked project module through the public umbrella.
    # Read the requested project branches without scanning every unrelated D5 source.
    pending = set(targets).union(*graph.values())
    while project := sorted(name for name in pending - graph.keys() if root(name) in {"D5", "Trureturing"}):
        paths = [name.replace(".", "/") + ".lean" for name in project]
        # Lake's default D5 library glob can expand beyond the OS argument limit.
        if len(paths) > 1000:
            paths = ["D5/*.lean", "Trureturing.lean"]
        _, extra = import_graph(lean, paths)
        graph.update(extra)
        pending = set().union(*extra.values())


def strict_import_graph(lean, targets=()):
    _, graph = import_graph(lean, (*portable.STRICT_LIBRARIES, "src/*.lean"))
    extend_project_imports(lean, graph, targets)
    return graph


@cache
def library_graph():
    return strict_import_graph(ENV["LEAN"])


def terminal_modules(graph, names):
    imported = {dep for name in names for dep in graph[name]}
    return sorted(set(names) - imported)


def library_backend_candidates(graph, names):
    # Mixed witnesses can use the concrete strict implementation. Only resolve
    # their official artifacts if the command is reachable.
    reachable = {"OmegaBuild.Commands"}
    for name in names:
        if graph[name] & reachable:
            reachable.add(name)
    return [name for name in names if name in reachable and root(name) != "OmegaBuild"]


def library_mathlib_only(graph, targets):
    candidates = library_backend_candidates(graph, closure(graph, targets))
    if not candidates:
        return {}
    run("lake", "build", *("+" + name for name in terminal_modules(graph, candidates)))
    official_path = portable.output("lake", "env", "printenv", "LEAN_PATH").strip()
    return portable.backend_plan(official_path, candidates)["mathlibOnly"]


def check_library(selected=()):
    graph = library_graph()
    for name in selected:
        if name not in graph or root(name) not in STRICT | {"OmegaChecks", "OmegaBuild"}:
            raise ValueError(f"unknown Omega module {name}")
    # The current check passes every changed program under src to the Lake test
    # driver. The command frontend and planner run in the official environment.
    support = {name for name in selected if root(name) == "OmegaBuild"}
    if support:
        run("lake", "build", *("+" + name for name in terminal_modules(graph, support)))
        selected = [name for name in selected if name not in support]
        if not selected:
            return
    # Imported-only modules and new modules outside an umbrella are both in scope.
    if not selected or "OmegaChecks.Audit" in selected:
        modules = sorted(name for name in graph if root(name) in STRICT)
    else:
        modules = [name for name in closure(graph, selected) if root(name) in STRICT]
    targets = set(modules) | set(selected)
    if not selected:
        # Build every external witness against the actual strict implementation.
        targets.update(name for name in graph if root(name) == "OmegaChecks")
    dependencies = closure(graph, targets)
    skipped = library_mathlib_only(graph, targets)
    if skipped:
        modules = [name for name in modules if name not in skipped]
        targets.update(name for name in dependencies if root(name) != "OmegaBuild")
        targets.difference_update(skipped)
    if targets:
        build(terminal_modules(graph, targets))
    roots = terminal_modules(graph, modules)
    if roots:
        subprocess.run([AUDIT, "--exact-roots", LIB, *roots, "--", *modules],
                       cwd=ROOT, env=audit_environment(), check=True)


def lake_environment():
    script = "import json, os; print(json.dumps(dict(os.environ)))"
    output = subprocess.run(["lake", "-f", isolated_config(), "env", sys.executable, "-c", script], cwd=ROOT,
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
        other_quot = tmp / "OtherQuot.lean"
        other_quot.write_text("module\nprelude\npublic inductive Eq {α : Sort u} : α → α → Prop where\n"
                              "  | refl (a : α) : Eq a a\ninit_quot\n")
        lean("-R", tmp, "-o", other_quot.with_suffix(".olean"), other_quot)
        audit("OtherQuot", ["OtherQuot"], [tmp], "unexpected native quotient support OtherQuot/")
        for name, source, reason in [
            ("UnusedAxiom", "module\nprelude\nimport OmegaInit.Prelude\npublic axiom hiddenAssumption : Prop\n",
             "hiddenAssumption"),
            ("ImplicitInit", "module\nimport OmegaInit.Prelude\n", "unknown module prefix 'Init'"),
        ]:
            source_file = tmp / f"{name}.lean"
            source_file.write_text(source)
            if name == "ImplicitInit":
                run("lake", "-f", strict_config(), "env", "lean", "-R", tmp, "-o", tmp / f"{name}.olean", source_file)
            else:
                lean("-R", tmp, "-o", tmp / f"{name}.olean", source_file)
            audit(name, ["OmegaInit.Prelude", name], [tmp, LIB], reason)
    check_standard_admission()
    check_module_surface()
    check_consumer_exports()


def check_consumer_exports():
    name = "ConsumerExportProbe"
    local = ("public def A.item : Prop := ∀ p : Prop, p → p\n"
             "public def B.item : Prop := ∀ p q : Prop, p → q → p\n")
    alias = "namespace Visible\nexport A (item)\nend Visible\n"
    generated = "public inductive Choice where | first | second\n"
    size_of = ("public import Init\npublic import OmegaInit.Prelude\n"
               "public structure Wrapper where value : Omega.Option Omega.Nat\n"
               "public noncomputable def derivedSize : Nat := sizeOf (Wrapper.mk Omega.Option.none)\n")
    field = ("public import OmegaInit.Prelude\npublic section\n"
             "abbrev FieldReceiver := Omega.Option Omega.Nat\n"
             "def Omega.Option.projectField (value : FieldReceiver) := value\n")
    field_alias = "namespace Option\nexport _root_.Omega.Option (projectField)\nend Option\n"
    alias_method = (field.replace("def Omega.Option.", "def Example.")
                    + "namespace Omega.Option\nexport _root_.Example (projectField)\nend Omega.Option\n")
    official = audit_environment()
    hosted_path = portable.output("lake", "-f", strict_config(), "env", "printenv", "LEAN_PATH").strip()
    hosted = {**ENV, "LEAN_PATH": hosted_path}
    with tempfile.TemporaryDirectory(prefix="omega-exports-") as directory:
        tmp = Path(directory)
        for strict_code, official_code, error, marker in [
            (field + field_alias, field + field_alias, False, "Compared"),
            (field, field, True, "field resolution mismatch for Omega.Option.projectField"),
            (alias_method, alias_method, True, "field resolution mismatch for Omega.Option.projectField"),
            ((field + field_alias).replace("projectField", "filter"),
             (field + field_alias).replace("projectField", "filter"), True,
             "field resolution mismatch for Omega.Option.filter"),
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
            strict_env = hosted if strict_code.startswith("public import Init\n") else ENV
            for side, header, body, env in [("strict", "module\nprelude\n", strict_code, strict_env),
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
    run("lake", "build", "+OmegaMathlib.Data.Nat.Fib.Basic")
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
        lake = ["lake", "-f", strict_config()] if strict else lake_layout(False, False, common_dir)[0]
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
            (port, [prelude], "namespace And\nexport Omega.And (left)\nend And",
             "unmatched public alias And.left"),
            (core, [prelude], "namespace And\nexport Omega.And (left)\nend And",
             "unmatched public alias And.left"),
            (core, [prelude], "public theorem Omega.Bool.of_not_eq_false {b : Bool} : "
             "Not (Eq b Bool.false) → Eq b Bool.true := Omega.Bool.eq_true_of_ne_false\n"
             "namespace Bool\nexport Omega.Bool (of_not_eq_false)\nend Bool", None),
            (core, [prelude], "import all OmegaInit.Prelude\nattribute [local semireducible] Nat.div", None),
            (core, [prelude], "attribute [default_instance 77] Omega.instDecidableAnd",
             "unmatched default instance Omega.instDecidableAnd"),
            (port, [prelude], "attribute [class] Omega.True", "public class registration mismatch for Omega.True"),
            (core, [prelude], "attribute [class] Omega.True", "public class registration mismatch for Omega.True"),
            ("OmegaInit", [prelude], "attribute [class] Omega.True", "unmatched class registration"),
            (core, [prelude], "import all OmegaInit.Prelude\nset_option allowUnsafeReducibility true in\n"
             "attribute [semireducible] Nat.div",
             "unverified public reducibility override for Nat.div"),
            ("OmegaInit.Data.Nat.Basic", [prelude],
             "import all OmegaInit.Prelude\n"
             "public theorem Omega.Nat.mul_zero (n : Nat) : Eq (Nat.mul n Nat.zero) Nat.zero := Eq.refl Nat.zero",
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
            (port, 'notation "$$$" => True', "parser"),
            (core, 'notation "$$$" => True', "parser"),
            (core, 'public instance Omega.extraNat : Inhabited Nat := ⟨Nat.zero⟩', "instance"),
            (core, '@[deprecated "use True.intro" (since := "1")] public theorem '
             'Omega.oldIntro : True := True.intro', "environment extension"),
        ]:
            source = tmp.joinpath(*name.split(".")).with_suffix(".lean")
            source.write_text(f"module\nprelude\npublic import Lean\n{body}\n")
            lean("-R", tmp, "-o", source.with_suffix(".olean"), source)
            result = subprocess.run([ENV["LEAN"], "--run", probe, tmp, name], cwd=ROOT, env=ENV,
                                    capture_output=True, text=True)
            if result.returncode == 0 or f"no elaboration correspondence for public {kind}" not in result.stderr:
                raise RuntimeError(f"Expected {kind} rejection in {name}: {result.stdout}{result.stderr}")


def check_standard_admission():
    # Compile the negative fixtures against the same upstream artifacts as the admitted library.
    init = "OmegaInit.Data.Nat.Basic"
    prime = "OmegaMathlib.Data.Nat.Prime.Defs"
    original = "OmegaMath.Projective.Local"
    with tempfile.TemporaryDirectory(prefix="omega-pred-") as directory:
        tmp = Path(directory)
        prelude = "OmegaInit.Prelude"
        source = tmp / "OmegaInit/Prelude.lean"
        source.parent.mkdir()
        source.write_text("module\nprelude\n@[expose] public section\nset_option genCtorIdx false\n"
                          "inductive Nat where\n  | zero\n  | succ (n : Nat)\n"
                          "@[no_expose] noncomputable def Nat.pred : Nat → Nat := Nat.rec Nat.zero (fun n _ => n)\n"
                          "namespace Omega\nexport _root_ (Nat)\nend Omega\n"
                          "namespace Omega.Nat\nexport _root_.Nat (zero succ rec pred)\nend Omega.Nat\n")
        lean("-R", tmp, "-o", source.with_suffix(".olean"), source)
        audit(prelude, [prelude], [tmp], "invalid Lean.OLeanLevel.private natural bootstrap declaration OmegaInit.Prelude/Nat.pred")
    with tempfile.TemporaryDirectory(prefix="omega-name-") as tmp:
        tmp = Path(tmp)
        for name, declaration, error in [
            (init, "def Omega.Nat.add", "official owner of Nat.add is Init.Prelude"),
            (init, "def OutsideOmega", "public name outside Omega"),
            (init, "def Omega.Nat.unknownOfficialName", "missing official declaration Nat.unknownOfficialName"),
            (prime, "def Omega.Nat.Prime", "public binder mismatch for Omega.Nat.Prime"),
            (prime, "def Omega.Nat.unknownMathlibName", "missing official declaration Nat.unknownMathlibName"),
            (prime, "def Omega.Nat.add", "official owner of Nat.add is Init.Prelude"),
            (original, "def Omega.Projective.localValue", None),
            (original, "axiom Omega.Projective.unused", "inadmissible declaration Omega.Projective.unused"),
        ]:
            source = tmp / (name.replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            marker = "/-! Omega original. -/\n" if name == original else ""
            body = "" if declaration.startswith("axiom ") else " := ∀ p : Prop, p → p"
            field = declaration.removeprefix("def Omega.Nat.")
            alias = (f"public section\nnamespace Nat\nexport Omega.Nat ({field})\nend Nat\n"
                     if declaration.startswith("def Omega.Nat.") and field != "add" else "")
            source.write_text(f"module\nprelude\n{marker}public {declaration} : Prop{body}\n{alias}")
            lean("-R", tmp, "-o", source.with_suffix(".olean"), source)
            audit(name, [name], [tmp], error)
    with tempfile.TemporaryDirectory(prefix="omega-interface-") as directory:
        tmp = Path(directory)
        always_prime = tmp / "OmegaMathlib/Data/Nat/Prime/Defs.lean"
        always_prime.parent.mkdir(parents=True)
        always_prime.write_text("module\nprelude\npublic import OmegaInit.Prelude\n"
                                "/-! Omega original. -/\n"
                                "public def Omega.Nat.Prime (_ : Omega.Nat) : Prop := Omega.True\npublic section\nnamespace Nat\nexport Omega.Nat (Prime)\nend Nat\n")
        lean("-R", tmp, "-o", always_prime.with_suffix(".olean"), always_prime)
        audit(prime, ["OmegaInit.Prelude", prime], [tmp, LIB], "certificate statement mismatch for Omega.Nat.Prime")
        fib = "OmegaMathlib.Data.Nat.Fib.Basic"
        altered = tmp / "OmegaMathlib/Data/Nat/Fib/Basic.lean"
        altered.parent.mkdir(parents=True)
        altered.write_text("module\nprelude\npublic import OmegaInit.Prelude\n"
                           "public def Omega.Nat.fib (n : Omega.Nat) : Omega.Nat := n\npublic section\nnamespace Nat\nexport Omega.Nat (fib)\nend Nat\n")
        lean("-R", tmp, "-o", altered.with_suffix(".olean"), altered)
        audit(fib, ["OmegaInit.Prelude", fib], [tmp, LIB], "certificate statement mismatch for Omega.Nat.fib")
        altered.write_text("module\nprelude\npublic import OmegaInit.Prelude\n"
                           f"public noncomputable def Omega.Nat.fib (n : Omega.Nat) : Omega.Nat := {FIB_ITERATOR}\npublic section\nnamespace Nat\nexport Omega.Nat (fib)\nend Nat\n")
        lean("-R", tmp, "-o", altered.with_suffix(".olean"), altered)
        audit(fib, ["OmegaInit.Prelude", fib], [tmp, LIB],
              "legacy importer can unfold the hidden implementation of Omega.Nat.fib")
        # A transitive dependency on project-specific mathematics invalidates a standard port.
        reverse = tmp / "OmegaMathlib/Reverse.lean"
        reverse.write_text("module\nprelude\nimport OmegaMath.Data.Nat\n")
        lean("-R", tmp, "-o", reverse.with_suffix(".olean"), reverse)
        audit("OmegaMathlib.Reverse", [*closure(library_graph(), ["OmegaMath.Data.Nat"]), "OmegaMathlib.Reverse"],
              [tmp, LIB], "forbidden strict import")


def versions(artifacts):
    return {name: path.stat().st_mtime_ns for name, path in artifacts.items()}


def check_incremental():
    graph = library_graph()
    # Track the strict libraries and every mathematical check importing them.
    imports = {name: set(closure(graph, [name])) for name in graph if root(name) in STRICT | {"OmegaChecks"}}
    modules = sorted(name for name, deps in imports.items() if any(root(dep) in STRICT for dep in deps))
    skipped = library_mathlib_only(graph, modules)
    modules = [name for name in modules if name not in skipped]
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
        ("src/OmegaMath/SeparateTopicProbe.lean", None,
         "module\nprelude\npublic import OmegaInit\n", set()),
        ("src/OmegaMath/Projective.lean", "he.symm\n", "he.symm.symm.symm\n", {TOPIC}),
        ("src/OmegaMath/Projective.lean", None,
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
    run("lake", "build", *("+" + name for name in sorted(affected_scope.IMPORTER_INPUTS)))
    subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT, check=True, text=True, input="""
import OmegaMath
import OmegaChecks.Portable.Common
example : Nat.fib 0 = 0 := rfl
example : Nat.fib 5 = 5 := rfl
example (n : Nat) : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) :=
  OmegaChecks.Portable.Common.fibonacciRecurrence n
example {p q : Prop} (h : p ∧ q) : p := OmegaChecks.Portable.Common.projectLeft h
""")


def check_generated_init():
    with tempfile.TemporaryDirectory(prefix="omega-generated-init-") as directory:
        product = Path(directory) / "port"
        consumers, imports = import_graph(ENV["LEAN"], ("strict/OmegaChecks/InitPort/*.lean",))
        roots = {"Init.Prelude", "Init.Data.Function", "Init.Data.List.Impl", "Init.Data.List.TakeDrop",
                 "Init.Data.Nat.Coprime"}
        for dependencies in imports.values():
            roots.update(name.removeprefix("Omega") for name in dependencies if root(name) == "OmegaInit")
        run(sys.executable, "-B", SRC / "OmegaChecks/InitPort/build.py", product, *sorted(roots))
        environment = {**ENV, "LEAN_PATH": str(product / "lib")}
        clients = Path(directory) / "clients"
        clients.mkdir()
        sources = {source.stem: source for source in consumers.values()}
        deps = {source.stem: imports[name] & sources.keys() for name, source in consumers.items()}
        client_env = {**environment, "LEAN_PATH": os.pathsep.join((str(clients), environment["LEAN_PATH"]))}
        for name in TopologicalSorter(deps).static_order():
            source = sources[name]
            subprocess.run([ENV["LEAN"], "-R", source.parent, "-o", clients / (name + ".olean"), source],
                           cwd=ROOT, env=client_env, check=True)
        run("lean", "--run", SRC / "OmegaChecks/InitPort/NativeConsumer.lean", product / "lib")
        quotient = """module
prelude
import OmegaInit.Prelude
example {α : Sort u} {r : α → α → Prop} {β : Sort v} (a : α) (f : α → β)
    (h : ∀ a b, r a b → Omega.Eq (f a) (f b)) :
    Omega.Eq (Omega.Quot.lift f h (Omega.Quot.mk r a)) (f a) := Omega.rfl
example {α : Sort u} {r : α → α → Prop} {p : Omega.Quot r → Prop}
    (f : ∀ a, p (Omega.Quot.mk r a)) (a : α) :
    Omega.Eq (Omega.Quot.ind f (Omega.Quot.mk r a)) (f a) := Omega.rfl
"""
        subprocess.run([ENV["LEAN"], "--stdin"], cwd=ROOT, env=environment, text=True,
                       input=quotient, check=True)
        # The upstream addition helper must preserve the strict seed's definitional reduction.
        source = ("module\nprelude\nimport all OmegaInit.Prelude\n"
                  "example (x : Omega.Nat) : Omega.Eq (x.add .zero) x := Omega.rfl\n")
        subprocess.run([ENV["LEAN"], "--stdin"], cwd=ROOT, text=True, input=source, check=True,
                       env=environment)
        subprocess.run([ENV["LEAN"], "--stdin"], cwd=ROOT, env=environment, text=True, check=True,
                       input="""module
prelude
import OmegaInit.Data.List.Basic
example {α : Type} (a : α) :
    Omega.Eq (Omega.List.reverse (Omega.List.cons a .nil)) (Omega.List.cons a .nil) := Omega.rfl
""")
        # These two official modules prove the same public equations with different private helpers.
        names = ("Omega.List.take.eq_def", "Omega.List.takeWhile.eq_def")
        for module in ("OmegaInit.Data.List.Impl", "OmegaInit.Data.List.TakeDrop"):
            probe = f"module\nprelude\nimport {module}\n" + "".join(f"#print axioms {n}\n" for n in names)
            result = subprocess.run([ENV["LEAN"], "--stdin"], cwd=ROOT, env=environment,
                                    text=True, input=probe, stdout=subprocess.PIPE, check=True)
            for name in names:
                if f"'{name}' does not depend on any axioms" not in result.stdout:
                    raise RuntimeError(f"{module}: {result.stdout}")
        # GCD has a builtin reduction even though its public official body is sealed.
        coprime = "example : Nat.Coprime (.succ (.succ .zero)) (.succ (.succ (.succ .zero))) := rfl\n"
        official_import = "module\nprelude\nimport Init.Data.Nat.Coprime\n"
        subprocess.run([ENV["LEAN"], "--stdin"], cwd=ROOT, text=True, check=True,
                       input=official_import + coprime, env={**ENV, "LEAN_PATH": ""})
        strict_import = "module\nprelude\nimport OmegaInit.Data.Nat.Coprime\nopen Omega\n"
        subprocess.run([ENV["LEAN"], "--stdin"], cwd=ROOT, text=True, input=strict_import + coprime,
                       env=environment, check=True)
        large_arithmetic = """
example : Omega.Eq (Omega.Nat.gcd 18446744073709551616 27670116110564327424) 9223372036854775808 := Omega.rfl
example : Omega.Eq (Omega.Nat.div 1208925819614629174706177 65536) 18446744073709551616 := Omega.rfl
example : Omega.Eq (Omega.Nat.mod 1208925819614629174706177 65536) 1 := Omega.rfl
example : Omega.Eq (Omega.Nat.div 1208925819614629174706177 0) 0 := Omega.rfl
example : Omega.Eq (Omega.Nat.mod 1208925819614629174706177 0) 1208925819614629174706177 := Omega.rfl
"""
        subprocess.run([ENV["LEAN"], "--stdin"], cwd=ROOT, text=True, input=strict_import + large_arithmetic,
                       env=environment, check=True)


def full_check(incremental=False):
    manifest = ROOT / "lake-manifest.json"
    initial = manifest.read_bytes()
    check_ordinary_importer()
    # The compiled driver runs the current Audit.lean without elaborating it for every audit.
    run("lake", "build", "omegaAudit")
    check_audits()
    check_generated_init()
    run(sys.executable, "-B", SRC / "OmegaChecks/portable.py", "--backend", "both")
    run(sys.executable, "-B", SRC / "OmegaChecks/test_backend_plan.py")
    run(sys.executable, "-B", SRC / "OmegaChecks/test_backend_scheduling.py")
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
        full_check()
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
        portable.check(scope["consumers"], "both", basis_roots=scope["basis"], common_roots=scope["common"])
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
    args = parser.parse_args()
    if args.write_scope:
        if not args.changed or not args.cache_targets or args.scope:
            parser.error("--write-scope requires --changed and --cache-targets")
        scope = affected_scope.discover(args.changed)
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
        run("lake", "build", "omegaAudit")
        ENV.update(lake_environment())
        check_library(args.library)
    elif args.full or args.incremental or not (args.scope or args.changed):
        ENV.update(lake_environment())
        full_check(args.incremental)
    else:
        scope = json.loads(args.scope.read_text()) if args.scope else affected_scope.discover(args.changed)
        scoped_check(scope)
