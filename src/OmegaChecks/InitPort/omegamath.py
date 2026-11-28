"""Build the repository's OmegaMath sources against an audited generated OmegaInit library."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from graphlib import TopologicalSorter
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check import extend_project_imports, library_mathlib_only
from portable import STRICT_LIBRARIES, ROOT, closure, import_graph, root, source_fingerprint


def lean_options(options, prefix=""):
    for key, value in options.items():
        name = prefix + key
        if isinstance(value, dict):
            yield from lean_options(value, name + ".")
        else:
            setting = str(value).lower() if isinstance(value, bool) else str(value)
            yield f"-D{name}={setting}"


def build(basis, output, workers, audit_log):
    lean = subprocess.check_output(["lake", "env", "printenv", "LEAN"], cwd=ROOT, text=True).strip()
    sources, graph = import_graph(lean, (*STRICT_LIBRARIES, "src/*.lean"))
    extend_project_imports(lean, graph)
    foundation = dict(json.loads((basis / "modules.json").read_text()))
    graph.update((name, set(deps)) for name, deps in foundation.items())
    clients = sorted(name for name in sources if root(name) in {"OmegaMath", "OmegaMathlib"})
    if not {"OmegaMath", "OmegaMathlib"}.issubset(clients):
        raise RuntimeError("missing tracked OmegaMath or OmegaMathlib library sources")
    official_only = library_mathlib_only(graph, clients)
    clients = [name for name in clients if name not in official_only]
    imported = {dep for name in clients for dep in graph[name]}
    roots = [name for name in clients if name not in imported]
    modules = closure(graph, roots)
    schedule = TopologicalSorter({name: set(graph[name]).intersection(clients) for name in clients})
    schedule.prepare()
    options = tomllib.loads((ROOT / "lakefile.toml").read_text())["leanOptions"]
    args = list(lean_options(options))
    paths = os.pathsep.join(map(str, dict.fromkeys((output, basis / "lib"))))
    env = {**os.environ, "LEAN_PATH": paths}
    before = {name: source_fingerprint(sources[name]) for name in clients}

    def compile_module(name):
        project = ROOT if root(name) == "OmegaMathlib" else ROOT / "src"
        target = output.joinpath(*name.split(".")).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run([lean, "-j1", *args, "-R", project, "-o", target, sources[name]],
                       cwd=ROOT, env=env, check=True)

    with ThreadPoolExecutor(max_workers=workers) as pool:
        running = {}
        while schedule.is_active():
            for name in schedule.get_ready():
                running[pool.submit(compile_module, name)] = name
            completed, _ = wait(running, return_when=FIRST_COMPLETED)
            for job in completed:
                job.result()
                schedule.done(running.pop(job))
    if any(before[name] != source_fingerprint(sources[name]) for name in clients):
        raise RuntimeError("consumer sources changed during compilation")
    subprocess.run([lean, "--stdin"], cwd=ROOT, env=env, check=True, text=True,
                   input="""module
prelude
import OmegaMath
#check Omega.Nat.fib
example {α : Type u} (xs ys : Omega.Array α) :
    Omega.Eq (Omega.Array.append xs ys)
      (Omega.Array.foldl Omega.Array.push xs ys Omega.Nat.zero (Omega.Array.size ys)) := Omega.rfl
example {α : Type u} {β : Type v} (f : α → β) (xs : Omega.Array α) :
    Omega.Eq (Omega.Array.map f xs) (@Omega.Array.mapM α β Omega.Id Omega.Id.instMonad f xs) := Omega.rfl
example (a b : Omega.Nat) :
    Omega.Eq ({ fst := a, snd := b } : Omega.Prod Omega.Nat Omega.Nat).fst a := Omega.rfl
example (p : Omega.Prod Omega.Nat Omega.Nat) (b : Omega.Nat) :
    Omega.Eq ({ p with snd := b }).snd b := Omega.rfl
example {p q : Prop} (h : Omega.And p q) : p := h.left
example {p q : Prop} (pq : p → q) (qp : q → p) : Omega.Iff p q := { mp := pq, mpr := qp }
example {p q : Prop} (h : Omega.Iff p q) : q → p := h.mpr
example {n m : Omega.Nat} (h : Omega.Nat.le n m) :
    Omega.Or (Omega.Eq n m) (Omega.Nat.lt n m) :=
  match h with
  | .refl => .inl Omega.rfl
  | .step g => .inr (Omega.Nat.succ_le_succ g)
example {p q : Prop} (h : Omega.Or p q) : Omega.Or q p :=
  match h with
  | .inl a => .inr a
  | .inr b => .inl b
example {α : Sort u} (h : Omega.Nonempty α) : Omega.Exists fun _ : α => Omega.True :=
  match h with
  | .intro a => .intro a Omega.True.intro
example {α : Sort u} {P : α → Prop} (h : Omega.Exists P) : Omega.Nonempty α :=
  match h with
  | .intro a _ => .intro a
example {p : Prop} (d : Omega.Decidable p) : Omega.Eq d d :=
    Omega.Decidable.falseTrueCases (fun _ => Omega.rfl) (fun _ => Omega.rfl) d
example {p : Prop} (h : p) :
    Omega.Eq (@Omega.decide p (Omega.isTrue h)) Omega.true := Omega.rfl
def decisionTag {p : Prop} (d : Omega.Decidable p) : Omega.Bool :=
  match d with
  | Omega.isTrue _ => Omega.true
  | Omega.isFalse _ => Omega.false
example {p : Prop} (h : p) : Omega.Eq (decisionTag (Omega.isTrue h)) Omega.true := Omega.rfl
example {p : Prop} (h : Omega.Not p) : Omega.Eq (decisionTag (Omega.isFalse h)) Omega.false := Omega.rfl
def bothTrue : Omega.Bool → Omega.Bool → Omega.Bool
  | Omega.true, Omega.true => Omega.true
  | _, _ => Omega.false
example : Omega.Eq (bothTrue Omega.true Omega.true) Omega.true := Omega.rfl
example : Omega.Eq (bothTrue Omega.false Omega.true) Omega.false := Omega.rfl
""")
    subprocess.run(["lake", "env", "lean", "--run", Path(__file__).with_name("RootImports.lean"),
                    output, basis / "lib", *foundation], cwd=ROOT, check=True)
    audit = ROOT / ".lake/build/bin/omegaAudit"
    subprocess.run(["lake", "build", "omegaAudit", "+OmegaChecks.Interface.Equations"], cwd=ROOT, check=True)
    with audit_log.open("w") as log:
        result = subprocess.run(["lake", "env", audit, "--exact-roots", paths, *roots, "--", *modules],
                                cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    print(audit_log.read_text(), end="", flush=True)
    result.check_returncode()
    print(f"Rebuilt {len(clients)} OmegaMath and OmegaMathlib modules against {basis / 'lib'}")


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("basis", type=Path, help="output directory of InitPort/build.py")
    cli.add_argument("output", type=Path, help="new directory for compiled consumer modules")
    cli.add_argument("-j", type=int, default=4, help="number of parallel Lean modules")
    args = cli.parse_args()
    target, basis = args.output.resolve(), args.basis.resolve()
    if target.exists() or args.j < 1:
        cli.error("expected a new output directory and a positive job count")
    if not (basis / "lib/OmegaInit.olean.private").is_file():
        cli.error("the generated library must include OmegaInit")
    target.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=target.parent, prefix=".omegamath-") as stage:
        product = Path(stage) / "product"
        (product / "lib").mkdir(parents=True)
        build(basis, product / "lib", args.j, product / "audit.txt")
        product.rename(target)


if __name__ == "__main__":
    main()
