"""Compile public consumers and exercise object provenance on the two isolated backends."""
import json
import os
from pathlib import Path
import subprocess
import tempfile

from strict_lake import ROOT, strict_config


def check():
    audit = ROOT / ".lake/build/bin/omegaAudit"
    lean = subprocess.check_output(["lake", "env", "printenv", "LEAN"], text=True, cwd=ROOT).strip()
    layouts = (["lake", "-f", strict_config()], ["lake"])
    ports = ["OmegaMathlib.Data.Nat.Prime.Defs", "OmegaMathlib.Data.Nat.Choose.Basic"]
    for i, layout in enumerate(layouts):
        targets = ["+" + p for p in ports]
        if i == 1:
            targets += ["+OmegaChecks.Interface.Equations", "omegaAudit"]
        subprocess.run(layout + ["build", *targets], check=True, cwd=ROOT)
    paths = [subprocess.check_output(layout + ["env", "printenv", "LEAN_PATH"], cwd=ROOT,
                                     text=True).strip() for layout in layouts]
    with tempfile.TemporaryDirectory(prefix="omega-qualified-") as temp:
        temp = Path(temp)
        report = temp / "official.json"
        backend = [temp / "strict", temp / "official"]
        search = [str(directory) + os.pathsep + path for directory, path in zip(backend, paths)]
        def compile_case(module, strict_source, official_source=None):
            for i, source in enumerate((strict_source, official_source or strict_source)):
                path = backend[i].joinpath(*module.split(".")).with_suffix(".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
                subprocess.run([lean, "-R", backend[i], "-o", path.with_suffix(".olean"),
                                "-i", path.with_suffix(".ilean"), path],
                               cwd=ROOT, env={**os.environ, "LEAN_PATH": search[i]}, check=True)

        def compare(modules, roots, *errors):
            proc = subprocess.run([audit, "--consumer", *search, *modules, "--basis", "--object-roots", *roots],
                                  cwd=ROOT, env={**os.environ, "LEAN_PATH": paths[1],
                                                "OMEGA_OFFICIAL_AXIOM_REPORT": str(report)},
                                  capture_output=True, text=True)
            output = proc.stdout + proc.stderr
            if bool(proc.returncode) != bool(errors) or any(error not in output for error in errors):
                raise AssertionError(f"expected {errors or 'success'}, got exit {proc.returncode}: {output}")

        def qualified(module, error=None, labels=("strict", "official")):
            for label in labels:
                i = ("strict", "official").index(label)
                base = backend[i].joinpath(*module.split("."))
                request = temp / "qualified.json"
                request.write_text(json.dumps([[module, str(base.with_suffix(".lean")),
                                                str(base.with_suffix(".ilean"))]]))
                proc = subprocess.run([lean, "--run", ROOT / "src/OmegaChecks/QualifiedReferences.lean",
                                       label, search[i], request], cwd=ROOT,
                                      capture_output=True, text=True)
                output = proc.stdout + proc.stderr
                if error:
                    if not proc.returncode or error not in output:
                        raise AssertionError(f"expected {error} on {label}: {output}")
                elif proc.returncode or "Verified 1 qualified" not in output:
                    raise AssertionError(f"expected qualified identifier on {label}: {output}")

        for port, name, args in [(ports[0], "Nat.Prime", "p"), (ports[1], "Nat.choose", "p p")]:
            module = "D5.ObjectTest"
            head = f"module\nprelude\npublic import {port}\n"
            term = f"(OmegaMathlib.{name} {args})"
            source = (head + f"public noncomputable abbrev D5.localObject (p : Omega.Nat) := {term}\n"
                      + f"public theorem D5.claim (p : Omega.Nat) : Omega.Eq {term} (D5.localObject p) := Omega.rfl\n")
            compile_case(module, source)
            compare([module], [module])
            qualified(module)
            rows = json.loads(report.read_text())["standardObjectUses"]
            if not any(row["declaration"] == "D5.claim" and row["upstreamName"] == name and
                       row["upstreamModule"] == port.replace("OmegaMathlib", "Mathlib", 1) for row in rows):
                raise AssertionError(f"missing verified occurrence of {name}: {rows}")

            # Both statements are convertible and contain the genuine constant. Its positions differ.
            replaced = source.replace(f"Omega.Eq {term} (D5.localObject p)",
                                      f"Omega.Eq (D5.localObject p) {term}")
            compile_case(module, source, replaced)
            compare([module], [module], "D5.claim", name, "D5.localObject")

        compile_case("D5.Legacy", f"module\nprelude\npublic import {ports[0]}\n"
                     + "public theorem D5.legacy (p : Omega.Nat) (h : Omega.Nat.Prime p) : Omega.True := Omega.True.intro\n")
        qualified("D5.Legacy", "qualify this identifier as OmegaMathlib.Nat.Prime", labels=("strict",))

        # An identifier-shaped notation can disappear entirely from the compiled type.
        compile_case("D5.BadNotation", f"module\nprelude\nimport Lean\npublic import {ports[0]}\n"
                     + "local notation \"OmegaMathlib.Nat.Prime\" => fun (_ : Omega.Nat) => Omega.True\n"
                     + "public theorem D5.bogus (p : Omega.Nat) : OmegaMathlib.Nat.Prime p := Omega.True.intro\n")
        qualified("D5.BadNotation", "OmegaMathlib.Nat.Prime requires")
        head = "module\nprelude\npublic import OmegaInit.Prelude\n"
        compile_case("D5.Hidden", head + "private def D5.OmegaMathlib.Nat.Prime (_ : Omega.Nat) := Omega.True\n")
        compile_case("D5.ImportHidden", "module\nprelude\nimport D5.Hidden\n")
        compare(["D5.Hidden", "D5.ImportHidden"], ["D5.ImportHidden"], "reserved standard declaration", "D5.Hidden")

        compile_case("D5.FakeAlias", head + "public def Fake.Prime (_ : Omega.Nat) := Omega.True\n"
                     + "namespace OmegaMathlib.Nat\nexport Fake (Prime)\nend OmegaMathlib.Nat\n")
        compare(["D5.FakeAlias"], ["D5.FakeAlias"], "reserved standard alias OmegaMathlib.Nat.Prime", "Fake.Prime")

        compile_case("NewProvider", head + "public def MadeUp (_ : Omega.Nat) := Omega.True\n")
        compare(["NewProvider"], ["NewProvider"], "MadeUp", "NewProvider", "requires a D5 owner")
        compile_case("D5.Wrapper", "module\nprelude\npublic import OmegaInit.Prelude\nimport all NewProvider\n"
                     + "private def D5.hidden := MadeUp\npublic def D5.wrapped := D5.hidden\n")
        compare(["NewProvider", "D5.Wrapper"], ["D5.Wrapper"], "D5.wrapped", "MadeUp", "NewProvider")


if __name__ == "__main__":
    check()
