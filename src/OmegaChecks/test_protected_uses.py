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

    module = "D5.FidelityFixture"
    lean = output("lake", "env", "printenv", "LEAN").strip()
    search = output("lake", "env", "printenv", "LEAN_PATH").strip()
    with tempfile.TemporaryDirectory(prefix="omega-positions-") as temp:
        def compile_source(directory, text):
            directory = Path(temp) / directory
            source = directory.joinpath(*module.split(".")).with_suffix(".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text(text)
            subprocess.run([lean, "-R", directory, "-o", source.with_suffix(".olean"), source],
                           cwd=ROOT, env={**os.environ, "LEAN_PATH": search}, check=True)
            return os.pathsep.join([str(directory), search])

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


if __name__ == "__main__":
    check()
