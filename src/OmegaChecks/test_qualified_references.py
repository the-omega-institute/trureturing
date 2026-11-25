"""Exercise per-occurrence standard and project identities on both compiled backends."""
import json
import os
from pathlib import Path
import subprocess
import tempfile

from strict_lake import ROOT, strict_config


PORTS = ["OmegaMathlib.Data.Nat.Prime.Defs", "OmegaMathlib.Data.Nat.Choose.Basic"]
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
    for body in ["public def D5.standardPrime := REF",
                 "public def D5.typedPrime : Omega.Nat → Prop := REF",
                 "public def D5.standardProof := fun (p : Omega.Nat) (h : REF p) => h"]:
        yield module, head + body.replace("REF", "Omega.Nat.Prime") + "\n", [
            "qualify this identifier as OmegaMathlib.Nat.Prime"]
        yield module, head + body.replace("REF", "OmegaMathlib.Nat.Prime") + "\n", []
    local_head = head.replace("prelude\n", "prelude\nimport Lean\n")
    for target, local in [("Omega.Nat.Prime", ""),
                          ("D5.Project.Prime", "public def D5.Project.Prime (_ : Omega.Nat) := Omega.True\n")]:
        hidden = local_head + local + f'local notation "Prime〚" p "〛" => {target} p\n'
        yield module, hidden + ("public theorem D5.claim (p : Omega.Nat) (_ : OmegaMathlib.Nat.Prime p) "
                                "(h : Prime〚p〛) : Prime〚p〛 := h\n"), [
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


def check():
    lean = subprocess.check_output(["lake", "env", "printenv", "LEAN"], cwd=ROOT, text=True).strip()
    for label, layout in [("strict", ["lake", "-f", strict_config()]), ("official", ["lake"])]:
        subprocess.run([*layout, "build", *("+" + port for port in PORTS)], cwd=ROOT, check=True)
        path = subprocess.check_output([*layout, "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True).strip()
        with tempfile.TemporaryDirectory(prefix="omega-refs-") as temp:
            directory = Path(temp)
            search = os.pathsep.join([temp, path])
            for module, source, errors in cases():
                file = directory.joinpath(*module.split(".")).with_suffix(".lean")
                file.parent.mkdir(parents=True, exist_ok=True)
                file.write_text(source)
                index = file.with_suffix(".ilean")
                subprocess.run([lean, "-R", temp, "-o", file.with_suffix(".olean"), "-i", index, file], cwd=ROOT,
                               env={**os.environ, "LEAN_PATH": search}, check=True)
                request = directory / "request.json"
                request.write_text(json.dumps([[module, str(file), str(index)]]))
                result = subprocess.run([lean, "--run", CHECKER, label, search, request, *PORTS],
                                        cwd=ROOT, capture_output=True, text=True)
                message = result.stdout + result.stderr
                if bool(result.returncode) != bool(errors) or any(error not in message for error in errors):
                    raise AssertionError(f"{label} expected {errors or 'success'} for\n{source}\ngot {message}")
        print(f"Checked occurrence fixtures on {label}", flush=True)


if __name__ == "__main__":
    check()
