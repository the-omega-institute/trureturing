"""Check protected D5 use sites and consumers dropping their last Omega import."""
import os
from pathlib import Path
import subprocess
import tempfile

from portable import ROOT, output
from protected_uses import affected, compare


def check():
    before = {"OmegaMathlib.Port": set(), "OmegaMath.Helper": {"OmegaMathlib.Port"},
              "D5.Client": {"OmegaMath.Helper"}, "D5.Next": {"D5.Client"}, "D5.Unrelated": set()}
    after = {**before, "D5.Client": set()}
    for change in [{"OmegaMathlib.Port"}, {"D5.Client"}]:
        assert affected(before, after, change) == ["D5.Client", "D5.Next"]

    candidates = {**after, "D5.NewLeaf": {"OmegaMathlib.Port"}, "D5.OfficialOnly": {"Mathlib.Library"}}
    assert affected(before, candidates, {"D5.NewLeaf", "D5.OfficialOnly"}) == ["D5.NewLeaf"]
    assert affected(before, {**before, "D5.Unrelated": {"OmegaMathlib.Port"}}, {"D5.Unrelated"}) == ["D5.Unrelated"]

    module = "D5.FidelityFixture"
    lean = output("lake", "env", "printenv", "LEAN").strip()
    search = output("lake", "env", "printenv", "LEAN_PATH").strip()
    with tempfile.TemporaryDirectory(prefix="omega-positions-") as temp:
        def compile_source(directory, text, library_path=search, name=module):
            directory = Path(temp) / directory
            source = directory.joinpath(*name.split(".")).with_suffix(".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text(text)
            subprocess.run([lean, "-R", directory, "-o", source.with_suffix(".olean"), source],
                           cwd=ROOT, env={**os.environ, "LEAN_PATH": library_path}, check=True)
            return os.pathsep.join([str(directory), library_path])

        for port, signature, hypotheses, actual in [
            ("Data.Nat.Prime.Defs", "Nat → Prop", "(p : Nat) (h : P p) (g : Q p) : True := True.intro", "Nat.Prime"),
            ("Data.Nat.Choose.Basic", "Nat → Nat → Nat", "(p : Nat) : P p p = Q p p := rfl", "Nat.choose"),
        ]:
            # A transparent alias makes the forgery definitionally equal on both builds.
            prefix = f"import Mathlib.{port}\nnamespace D5.FidelityFixture\nabbrev localObject : {signature} := {actual}\n"
            theorem = "theorem published " + hypotheses + "\n"
            old = compile_source("old", prefix + theorem.replace("P ", actual + " ").replace("Q ", "localObject "))
            renamed = hypotheses.replace("(p :", "(n :").replace(" p", " n")
            unchanged = prefix + "theorem published " + renamed.replace("P ", actual + " ").replace("Q ", "localObject ") + "\n"
            new = compile_source("new", unchanged)
            compare(ROOT, [module], [module], old, new)
            swapped = compile_source("new", prefix + theorem.replace("P ", "localObject ").replace("Q ", actual + " "))
            try:
                compare(ROOT, [module], [module], old, swapped)
            except ValueError as error:
                message = str(error)
                assert all(fragment in message for fragment in ("published at type.", actual, "from Mathlib.",
                           "found D5.FidelityFixture.localObject from D5.FidelityFixture")), message
            else:
                raise AssertionError("protected identity accepted a transparent alias in its original position")

        for port, signature, target, substitute in [
            ("Data.Nat.Prime.Defs", "Nat → Prop", "Nat.Prime", "fun _ => True"),
            ("Data.Nat.Choose.Basic", "Nat → Nat → Nat", "Nat.choose", "fun n _ => n"),
        ]:
            port_ref = "OmegaMathlib." + target
            form = f"@[expose] public def D5.published : {signature} := "
            old = compile_source("old", f"module\npublic import OmegaMathlib.{port}\n{form}{port_ref}\n")
            # Direct upstream reuse retains this exact compiled object after the final Omega import disappears.
            same = compile_source("new", f"module\npublic import Mathlib.{port}\n{form}{target}\n")
            compare(ROOT, [module], [module], old, same)
            for body in (f"module\n{form}{substitute}\n",
                         f"module\npublic import Mathlib.{port}\npublic def D5.published : {signature} := {target}\n"):
                new = compile_source("new", body)
                try:
                    compare(ROOT, [module], [module], old, new)
                except ValueError as error:
                    assert f"D5.published at value: expected {target} from Mathlib." in str(error), error
                else:
                    raise AssertionError(f"lost exposed body reference to {target} was accepted")

        native = "D5.NativeFixture"
        inner = "D5.TransitiveFixture"
        obj = "@[expose] public def D5.naturalObject (n k : Nat) := Nat.choose n k\n"
        owner_header = "module\npublic import Mathlib.Data.Nat.Choose.Basic\n"
        old = compile_source("old", owner_header + obj)
        folder = Path(temp) / "new"
        search_new = os.pathsep.join([str(folder), search])
        facade = f"module\npublic import {native}\n"
        for owner_source, outer, passing in [
            (owner_header + obj, facade, True),
            (owner_header + obj, f"import {native}\n", True),
            (owner_header + obj.replace(" := ", " := Nat.succ <| "), facade, False),
            (owner_header + obj.replace("k : Nat)", "k : Nat) (_ : Unit)"), facade, False),
            (owner_header + obj, f"module\nimport {native}\n", False),
            (owner_header + obj, f"module\npublic import {inner}\n", False),
            (owner_header + "public import OmegaInit.Prelude\n" + obj, facade, False),
        ]:
            compile_source("new", owner_source, search_new, native)
            compile_source("new", facade, search_new, inner)
            new = compile_source("new", outer, search_new)
            if passing:
                client = f"import {module}\nexample (n k : Nat) : D5.naturalObject n k = Nat.choose n k := rfl\n"
                subprocess.run([lean, "--stdin"], input=client, cwd=ROOT, text=True,
                               env={**os.environ, "LEAN_PATH": new}, check=True)
                compare(ROOT, [module], [module], old, new)
            else:
                try:
                    compare(ROOT, [module], [module], old, new)
                except subprocess.CalledProcessError:
                    pass
                else:
                    raise AssertionError("accepted a changed definition, invalid owner, or non-public direct import")

        # New leaves and new positions in existing consumers need a compiled, admitted port.
        header = ("module\npublic import OmegaMathlib.Data.Nat.Prime.Defs\n"
                  "public import Mathlib.Data.Nat.Prime.Defs\n")
        from strict_lake import strict_config
        strict_path = output("lake", "-f", strict_config(), "env", "printenv", "LEAN_PATH").strip()
        old = compile_source("old", header + "public theorem D5.other : True := True.intro\n")
        valid_source = header + ("public theorem D5.test (h : OmegaMathlib.Nat.Prime 2) : True := True.intro\n"
                                 "public opaque D5.primality (n : Omega.Nat) : Prop := OmegaMathlib.Nat.Prime n\n")
        valid = compile_source("new", valid_source)
        compile_source("strict", header + "public opaque D5.primality (n : Omega.Nat) : Prop := OmegaMathlib.Nat.Prime n\n",
                       strict_path)
        compare(ROOT, [], [module], old, valid)
        for body in ("public theorem D5.measure (n : Nat) : Nat.minFac n = Nat.minFac n := rfl\n",
                     "@[expose] public def D5.measure (n : Nat) := Nat.minFac n\n",
                     "public def D5.measure (n : Nat) := Nat.minFac n\n",
                     "public opaque D5.measure (n : Nat) : Nat := Nat.minFac n\n",
                     "private def fixtureMinFac (n : Nat) := Nat.minFac n\n"
                     "private opaque inner (n : Nat) : Nat := fixtureMinFac n\n"
                     "public def D5.measure (n : Nat) := inner n + inner n\n"):
            compile_source("strict", header + body, strict_path)
            new = compile_source("new", header + body)
            for previous in ([], [module]):
                try:
                    compare(ROOT, previous, [module], old, new)
                except ValueError as error:
                    assert "Nat.minFac from Mathlib.Data.Nat.Prime.Defs requires a verified OmegaMathlib port" in str(error), error
                else:
                    raise AssertionError("accepted an unported Mathlib object in a new consumer declaration")
            compare(ROOT, [module], [module], new, new)
            compare(ROOT, [], [module], old, new, omega_modules=[])

        # Both a theorem and a proof packaged inside computational data can change proof methods.
        header = "module\npublic import OmegaMathlib.Data.Nat.Prime.Defs\n"
        before = ("public theorem D5.witness : True := (fun (_ : Nat.Prime 2) => True.intro) Nat.prime_two\n"
                  "@[expose] public def D5.pair : {n : Nat // True} := ⟨2, D5.witness⟩\n")
        after = ("public theorem D5.witness : True := True.intro\n"
                 "@[expose] public def D5.pair : {n : Nat // True} := ⟨2, True.intro⟩\n")
        old = compile_source("old", header + before)
        new = compile_source("new", "module\n" + after)
        compare(ROOT, [module], [module], old, new)


if __name__ == "__main__":
    check()
