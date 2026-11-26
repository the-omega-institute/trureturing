"""Exercise per-occurrence standard and project identities on both compiled backends."""
import json
import os
from pathlib import Path
import subprocess
import tempfile

from portable import backend_plan
from strict_lake import ROOT, strict_config


PORTS = ["OmegaMathlib.Data.Nat.Prime.Defs", "OmegaMathlib.Data.Nat.Choose.Basic",
         "OmegaMathlib.Logic.Function.Defs"]
CHECKER = ROOT / "src/OmegaChecks/QualifiedReferences.lean"


def cases():
    head = f"module\nprelude\npublic import {PORTS[0]}\n"
    for owner, name, params, body, term in [
        ("D5", "Prime", "(_ : Omega.Nat)", "Omega.True", "REF p"),
        ("OmegaMath", "choose", "(_ _ : Omega.Nat)", "Omega.Nat.zero", "Omega.Eq (REF p p) Omega.Nat.zero"),
    ]:
        module = f"{owner}.LocalIdentity"
        target = f"{module}.{name}"
        port = f"OmegaMathlib.Nat.{name}"
        source = (head + f"namespace {module}\npublic noncomputable def {name} {params} := {body}\n"
                  f"public theorem claim (p : Omega.Nat) (_ : OmegaMathlib.Nat.Prime p) : {term} := "
                  + ("Omega.True.intro" if name == "Prime" else "Omega.rfl") + "\n")
        yield module, source.replace("REF", name), [":6:", f"uses {target} from {module}", port]
        yield module, source.replace("REF", target), []
        yield module, source.replace("REF", "_root_." + target), []

    module = "D5.Project"
    base = "module\nprelude\npublic import OmegaInit.Prelude\nnamespace D5.Project\n"
    yield module, (base + "public def Prime (_ : Omega.Bool) := Omega.True\n"
                   "public theorem unrelated : Prime Omega.Bool.true := Omega.True.intro\n"), []
    yield module, (base + "public def Prime (_ : Omega.Nat) := Omega.True\n"
                   "public theorem bare : Prime Omega.Nat.zero := Omega.True.intro\n"), [
                       "uses D5.Project.Prime", "OmegaMathlib.Nat.Prime"]
    yield module, (head + "public theorem D5.standard (p : Omega.Nat) (h : OmegaMathlib.Nat.Prime p) : "
                   "OmegaMathlib.Nat.Prime p := h\n"), []
    yield module, (head + "public theorem D5.ambiguous (p : Omega.Nat) (h : Omega.Nat.Prime p) : "
                   "OmegaMathlib.Nat.Prime p := h\n"), ["qualify this identifier as OmegaMathlib.Nat.Prime"]
    yield module, (head + "open OmegaMathlib.Nat renaming Prime → PortPrime in\n"
                   "public theorem D5.opened (p : Omega.Nat) (h : PortPrime p) : "
                   "OmegaMathlib.Nat.Prime p := h\n"), ["qualify this identifier as OmegaMathlib.Nat.Prime"]
    choose = f"module\nprelude\npublic import {PORTS[1]}\n"
    yield module, (choose + "public theorem D5.projected (p : Omega.Nat) : "
                   "Omega.Eq (p.choose p) (OmegaMathlib.Nat.choose p p) := Omega.rfl\n"), [
                       "qualify this identifier as OmegaMathlib.Nat.choose"]
    yield module, (head + "namespace Shadow.OmegaMathlib.Nat\n"
                   "public def Prime (_ : Omega.Nat) := Omega.True\nend Shadow.OmegaMathlib.Nat\n"
                   "namespace Shadow\npublic theorem claim (p : Omega.Nat) : "
                   "OmegaMathlib.Nat.Prime p := Omega.True.intro\n"), [
                       "OmegaMathlib.Nat.Prime requires", "at this occurrence"]
    function_head = f"module\nprelude\npublic import {PORTS[2]}\n"
    for name in ["@OmegaMathlib.Function.Bijective", "@OmegaMathlib.Function.Bijective.{1,1}"]:
        yield module, (function_head + f"public def D5.explicitArgs : {name} Omega.Nat Omega.Nat "
                       "(fun n => n) → Prop := fun _ => Omega.True\n"), []
    yield module, (function_head + "universe u v\n"
                   "public def D5.explicitLevels {α : Sort u} {β : Sort v} (f : α → β) : Prop := "
                   "OmegaMathlib.Function.Bijective.{u,v} f\n"), []
    yield module, (choose + "public noncomputable def D5.projectedValue (a b : Omega.Nat) : Omega.Nat := "
                   "(OmegaMathlib.Nat.choose a b).succ\n"), []
    for body in ["public def D5.standardPrime := REF",
                 "public def D5.explicitValue : Omega.Nat → Prop := fun p => REF p",
                 "public def D5.typedPrime : Omega.Nat → Prop := REF",
                 "public abbrev D5.parenthesized : Omega.Nat → Prop := (REF)",
                 "public def D5.standardProof := fun (p : Omega.Nat) (h : REF p) => h"]:
        yield module, head + body.replace("REF", "Omega.Nat.Prime") + "\n", [
            "qualify this identifier as OmegaMathlib.Nat.Prime"]
        yield module, head + body.replace("REF", "OmegaMathlib.Nat.Prime") + "\n", []
    yield module, (head + "public abbrev etaPrime := fun p : Omega.Nat => OmegaMathlib.Nat.Prime p\n"
                   "public theorem D5.etaClaim (p : Omega.Nat) (h : etaPrime p) : etaPrime p := h\n"), [
                       "etaPrime", "explicit source reference", "OmegaMathlib.Nat.Prime"]
    for body in ["let m := n; OmegaMathlib.Nat.Prime m",
                 "(fun f => fun m => f m) (fun k => let j := k; OmegaMathlib.Nat.Prime j) n"]:
        definition = f"public abbrev D5.reviewPrime (n : Omega.Nat) : Prop := {body}\n"
        claim = "public theorem D5.review (n : Omega.Nat) (h : REF n) : REF n := h\n"
        yield module, head + definition + claim.replace("REF", "_root_.D5.reviewPrime"), [
            "D5.reviewPrime", "explicit source reference", "OmegaMathlib.Nat.Prime"]
        yield module, head + definition + claim.replace("REF", "OmegaMathlib.Nat.Prime"), []
    yield module, (head + "public abbrev D5.Prime (n : Omega.Nat) : Prop := "
                   "let m := n; OmegaMathlib.Nat.Prime m.succ\n"
                   "public theorem D5.shifted (n : Omega.Nat) (h : D5.Prime n) : D5.Prime n := h\n"), []
    yield module, (head + "public def wrap (n : Omega.Nat) := (fun m => OmegaMathlib.Nat.Prime m) n\n"
                   "public abbrev D5.reviewPrime (n : Omega.Nat) : Prop := let m := n; wrap m\n"
                   "public theorem D5.review (n : Omega.Nat) (h : D5.reviewPrime n) : D5.reviewPrime n := h\n"), [
                       "explicit source reference", "OmegaMathlib.Nat.Prime"]
    legacy = "D5.S3.Arith.Primes.DivisorCharacterization"
    yield "IndependentRepresentation", (head + f"public import {legacy}\npublic theorem D5.review (p : Omega.Nat) : "
                   f"Omega.Iff ({legacy}.IsPrime p) (OmegaMathlib.Nat.Prime p) := "
                   f"{legacy}.isPrime_iff_prime p\n"), []
    # The public body reaches a private opaque computation through a second helper.
    for ref, errors in [("OmegaMathlib.Nat.Prime", []),
                        ("Omega.Nat.Prime", ["OmegaMathlib.Nat.Prime"])]:
        yield module, (head + f"private opaque helper (p : Omega.Nat) : Prop := {ref} p.succ\n"
                       "private def middle (p : Omega.Nat) := helper p\n"
                       "public def D5.claim (p : Omega.Nat) : Prop := middle p\n"), errors
    yield module, (head + "private def unused (p : Omega.Nat) : Prop := Omega.Nat.Prime p.succ\n"
                   "public def D5.claim (_ : Omega.Nat) : Prop := Omega.True\n"), []
    # A proof inside a public data field cannot expose a computation used only to build the proof.
    yield module, (head.replace("prelude\n", "") +
                   "private def privatePredicate (p : Omega.Nat) : Prop := Omega.Nat.Prime p.succ\n"
                   "public def D5.pair : {n : Nat // True} := "
                   "⟨0, (fun (_ : Prop) => True.intro) (privatePredicate Omega.Nat.zero)⟩\n"), []
    local_head = head.replace("prelude\n", "prelude\nimport Lean\n")
    for target, local in [("Omega.Nat.Prime", ""),
                          ("D5.Project.Prime", "public def D5.Project.Prime (_ : Omega.Nat) := Omega.True\n")]:
        hidden = local_head + local + f'local notation "Prime〚" p "〛" => {target} p\n'
        yield module, hidden + ("public theorem D5.claim (p : Omega.Nat) (_ : OmegaMathlib.Nat.Prime p) "
                                "(h : Prime〚p〛) : Prime〚p〛 := h\n"), [
                                    "without an explicit source reference", "OmegaMathlib.Nat.Prime"]
        yield module, hidden + ("public def D5.opaquePredicate : Omega.Nat → Prop := fun p => Prime〚p〛\n"), [
            "without an explicit source reference", "OmegaMathlib.Nat.Prime"]
    yield module, (head + "public abbrev D5.localPredicate := OmegaMathlib.Nat.Prime\n"
                   "public theorem D5.claim (p : Omega.Nat) (h : D5.localPredicate p) : "
                   "D5.localPredicate p := h\n"), ["D5.localPredicate", "explicit source reference"]
    notation = head.replace("prelude\n", "prelude\nimport Lean\n") + (
        'local notation "OmegaMathlib.Nat.Prime" => fun (_ : Omega.Nat) => Omega.True\n')
    yield module, notation + ("public theorem D5.forged (p : Omega.Nat) : "
                              "OmegaMathlib.Nat.Prime p := Omega.True.intro\n"), [
                                  "OmegaMathlib.Nat.Prime requires", "at this occurrence"]
    yield module, notation + "public abbrev D5.forged := OmegaMathlib.Nat.Prime\n", [
        "OmegaMathlib.Nat.Prime requires", "at this occurrence"]


def native_cases(backend):
    header = ("module\npublic import OmegaBuild.Commands\npublic import " + PORTS[0] +
              "\npublic import Mathlib.Data.Nat.Prime.Defs\n")
    name = "D5.MixedReference"
    ref = "native% OmegaMathlib.Nat.Prime"
    yield name, header + (
        f"public theorem observed (p : Nat) (h : ({ref}) p) : ({ref}) p := h\n"
        f"public def predicate : Nat → Prop := {ref}\n"
        "example : predicate = _root_.Nat.Prime := rfl\n"), []
    yield name, header + (
        f"public theorem mixed (p : Nat) (h : ({ref}) p) (hp : _root_.Nat.Prime p) : ({ref}) p := h\n"
    ), ["qualify this identifier as OmegaMathlib.Nat.Prime"] if backend == "official" else []
    # A replacement elaborator can emit an incorrect object at the genuine grammar node.
    forged = (header + "public meta import Lean\n"
              "public def Shadow.Prime (_ : Nat) : Prop := True\n"
              "open Lean Elab Term in\n"
              "@[term_elab OmegaBuild.nativePort] public meta def forgedNative : TermElab := fun _ _ => do\n"
              "  return mkConst `Shadow.Prime\n")
    for source in (forged, forged.replace("public import " + PORTS[0] + "\n", "")
                                 .replace("mkConst `Shadow.Prime", "mkConst `Nat.Prime")):
        yield name, source + f"public def forgedAtSamePosition : Nat → Prop := {ref}\n", [
            "native% OmegaMathlib.Nat.Prime requires Nat.Prime in Mathlib.Data.Nat.Prime.Defs at this occurrence"]


def computational_cases(backend):
    header = "module\npublic import OmegaMathlib.Data.Nat.Choose.Basic\n"
    if backend == "official":
        header += "meta import Mathlib.Data.Nat.Choose.Basic\n"
        for kind in ("def", "opaque"):
            yield "D5.Computation", (header + "private opaque helper (n k : Nat) : Nat := OmegaMathlib.Nat.choose n k\n"
                                     f"public {kind} D5.observed (n k : Nat) : Nat := helper n k\n"
                                     "/-- info: 10 -/\n#guard_msgs in\n#eval D5.observed 5 2\n"), []
    else:
        yield "D5.Computation", (header + "noncomputable section\n"
                                 "private opaque helper (n k : Omega.Nat) : Omega.Nat := OmegaMathlib.Nat.choose n k\n"
                                 "public def D5.observed (n k : Omega.Nat) : Omega.Nat := helper n k\n"), []


def check_case(lean, label, path, sources, errors, *, ports=PORTS, expected_count=None, read_plan=False):
    with tempfile.TemporaryDirectory(prefix="omega-refs-") as temp:
        directory = Path(temp)
        search = os.pathsep.join([temp, path])
        records = []
        for module, source in sources:
            file = directory.joinpath(*module.split(".")).with_suffix(".lean")
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_text(source)
            index = file.with_suffix(".ilean")
            subprocess.run([lean, "-R", temp, "-o", file.with_suffix(".olean"), "-i", index, file],
                           cwd=ROOT, env={**os.environ, "LEAN_PATH": search}, check=True)
            records.append(dict(moduleName=module, source=str(file), index=str(index), mathlibOnly=False))
        if read_plan:
            skipped = backend_plan(search, [r["moduleName"] for r in records])["mathlibOnly"]
            for record in records:
                record["mathlibOnly"] = record["moduleName"] in skipped
        request = directory / "request.json"
        request.write_text(json.dumps(records))
        environment = {**os.environ, "LEAN_PATH": str(ROOT / ".lake/build/lib/lean")}
        if len(sources) > 1:
            environment["PATH"] = temp
            environment.pop("LEAN_SYSROOT", None)
        result = subprocess.run([lean, "--run", CHECKER, label, search, request, *ports],
                                cwd=directory, env=environment, capture_output=True, text=True)
        message = result.stdout + result.stderr
        if bool(result.returncode) != bool(errors) or any(error not in message for error in errors):
            raise AssertionError(f"{label} expected {errors or 'success'} for {sources!r}\ngot {message}")
        if expected_count is not None:
            summary = f"Verified {expected_count} qualified standard references on the {label} backend."
            if result.stdout.strip() != summary:
                raise AssertionError(f"expected {summary!r}, got {message!r}")


def check_reflected(lean, label, path):
    header = f"module\npublic import {PORTS[0]}\n"
    owner = ("D5.AuthenticatedTheorem", header +
             "public theorem evidence (p : Omega.Nat) (h : OmegaMathlib.Nat.Prime p) : "
             "OmegaMathlib.Nat.Prime p := h\n")
    imported = (f"module\npublic import {owner[0]}\npublic import Lean\n"
                "public def withProof {p : Prop} (_ : p) : Prop := p\n")
    good = ("public def observed : Prop := type_of% @evidence\n"
            "public def implicit : Prop := withProof (@evidence)\n")
    check_case(lean, label, path, [owner, ("D5.Reflected", imported + good)], [])
    # The genuine reflected type is independently checked at its occurrence.
    # A hidden port introduced beside it still has no authenticated source position.
    hidden = ('local notation "unmarked" n => Omega.Nat.Prime n\n'
              'public def wrong (n : Omega.Nat) : Prop := (type_of% @evidence) ∧ unmarked n\n')
    check_case(lean, label, path, [owner, ("D5.Reflected", imported + hidden)],
               ["D5.Reflected", "without an explicit source reference", "OmegaMathlib.Nat.Prime"])


def check_mathlib_only(lean, path):
    port = "OmegaMathlib.Data.Nat.Fib.Basic"
    marked = ("D5.OfficialOrigin", "module\npublic import OmegaBuild.Commands\n" +
              f"public import {port}\ncompile_only_with_mathlib\n")
    header = "module\npublic import D5.OfficialOrigin\n"
    use = "public def observed (n : Nat) : Nat := Nat.fib n + OmegaMathlib.Nat.fib n\n"
    # Keep the spelling and source position identical when the local namespace shadows the port.
    column = use.index("OmegaMathlib.Nat.fib") + 1
    forged = [f":7:{column}: OmegaMathlib.Nat.fib requires Nat.fib",
              "in Mathlib.Data.Nat.Fib.Basic at this occurrence"]
    for namespace, errors in [("Independent", []), ("OmegaMathlib", forged)]:
        body = (header + f"namespace Shadow.{namespace}.Nat\npublic def fib (n : Nat) := n\n"
                f"end Shadow.{namespace}.Nat\nnamespace Shadow\n" + use + "end Shadow\n")
        check_case(lean, "official", path, [marked, ("D5.OfficialConsumer", body)], errors,
                   ports=[port], expected_count=None if errors else 1, read_plan=True)


def check():
    lean = subprocess.check_output(["lake", "env", "printenv", "LEAN"], cwd=ROOT, text=True).strip()
    subprocess.run(["lake", "build", "+OmegaBuild.Commands.Origin"], cwd=ROOT, check=True)
    for label, layout in [("strict", ["lake", "-f", strict_config()]), ("official", ["lake"])]:
        subprocess.run([*layout, "build", "+OmegaBuild.Commands", *("+" + port for port in PORTS),
                        "+OmegaMathlib.Data.Nat.Fib.Basic", "+D5.S3.Arith.Primes.DivisorCharacterization"],
                       cwd=ROOT, check=True)
        path = subprocess.check_output([*layout, "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True).strip()
        for module, source, errors in (*cases(), *computational_cases(label)):
            check_case(lean, label, path, [(module, source)], errors)
        check_reflected(lean, label, path)
        for module, source, errors in native_cases(label):
            check_case(lean, label, path, [(module, source)], errors)
        owner = ("D5.RefOwner", "module\nprelude\npublic import OmegaInit.Prelude\n"
                 "@[expose] public def D5.RefOwner.Prime (_ : Omega.Nat) := Omega.True\n")
        consumer = ("module\nprelude\npublic import D5.RefOwner\npublic import " + PORTS[0] +
                    "\nnamespace D5.RefOwner\npublic theorem use (n : Omega.Nat) "
                    "(_ : OmegaMathlib.Nat.Prime n) : REF n := Omega.True.intro\nend D5.RefOwner\n")
        for spelling, errors in [("Prime", ["uses D5.RefOwner.Prime", "OmegaMathlib.Nat.Prime"]),
                                 ("_root_.D5.RefOwner.Prime", [])]:
            check_case(lean, label, path, [owner, ("D5.RefUse", consumer.replace("REF", spelling))], errors)
        fib_port = "OmegaMathlib.Data.Nat.Fib.Basic"
        sibling = ("D5.OtherPort", f"module\nprelude\npublic import {fib_port}\n"
                   "public noncomputable def D5.firstFib := OmegaMathlib.Nat.fib\n")
        if label == "official":
            # This consumer references native Fibonacci without importing its port.
            use = ("module\npublic import Mathlib.Data.Nat.Fib.Basic\npublic import " + PORTS[0] +
                   "\npublic def D5.observed (n : Nat) (_ : OmegaMathlib.Nat.Prime n) : Nat := Nat.fib n\n")
            errors = ["official replay D5.FibConsumer (exit 1)", "qualify this identifier as OmegaMathlib.Nat.fib"]
        else:
            use = ("module\nprelude\npublic import " + PORTS[0] + "\nnamespace D5.FibConsumer\n"
                   "public noncomputable def fib (n : Omega.Nat) := n\n"
                   "public noncomputable def observed (n : Omega.Nat) (_ : OmegaMathlib.Nat.Prime n) := fib n\n"
                   "end D5.FibConsumer\n")
            errors = ["strict replay D5.FibConsumer (exit 1)", "uses D5.FibConsumer.fib", "OmegaMathlib.Nat.fib"]
        check_case(lean, label, path, [sibling, ("D5.FibConsumer", use)], errors, ports=[PORTS[0]])
        valid = ("D5.FibConsumer", f"module\nprelude\npublic import {PORTS[0]}\n"
                 "public def D5.observed (n : Omega.Nat) := OmegaMathlib.Nat.Prime n\n")
        check_case(lean, label, path, [sibling, valid], [], ports=[PORTS[0]], expected_count=2)
        if label == "official":
            check_mathlib_only(lean, path)
        print(f"Checked occurrence fixtures on {label}", flush=True)


if __name__ == "__main__":
    check()
