"""Compile protected and candidate OmegaMath fixtures through the publication comparator."""
import os
from pathlib import Path
import subprocess
import shutil
import tempfile

from portable import AUDIT, ROOT, output
from strict_lake import strict_config
from protected_objects import compiled_path, strict_witnesses

MODULE = "OmegaMath.StandaloneFixture"
HEADER = "module\nprelude\npublic import OmegaInit.Prelude\n@[expose] public section\nnamespace Omega\n"
OBJECT = "def Subject (p : Prop) : Prop := p\n"
THEOREM = "theorem stable (p : Prop) (h : p) : Subject p := h\n"


def compile_source(lean, search, folder, body, header=HEADER):
    file = folder.joinpath(*MODULE.split(".")).with_suffix(".lean")
    file.parent.mkdir(parents=True, exist_ok=True)
    file.write_text(header + body + "end Omega\n")
    subprocess.run([lean, "-R", folder, "-o", file.with_suffix(".olean"), file],
                   cwd=ROOT, env={**os.environ, "LEAN_PATH": search}, check=True)
    return os.pathsep.join([str(folder), search])


def check_client(lean, search, module, declaration, succeeds):
    result = subprocess.run([lean, "--stdin"], input=f"module\nprelude\nimport {module}\n{declaration}\n",
                            cwd=ROOT, env={**os.environ, "LEAN_PATH": search}, text=True, capture_output=True)
    if (result.returncode == 0) != succeeds:
        raise RuntimeError(f"Unexpected client reduction: {result.stdout}{result.stderr}")


def check_archive_build():
    with tempfile.TemporaryDirectory(prefix="protected-archive-") as temporary:
        archive = Path(temporary)
        for folder in ("src/OmegaChecks", "src/OmegaMath", "strict/OmegaInit"):
            (archive / folder).mkdir(parents=True)
        (archive / "lakefile.toml").write_text(
            'name = "fixture"\n' + "".join(
                f'[[lean_lib]]\nname = "{name}"\nsrcDir = "src"\n'
                for name in ("OmegaInit", "OmegaMathlib", "OmegaMath")))
        shutil.copyfile(ROOT / "lean-toolchain", archive / "lean-toolchain")
        shutil.copyfile(ROOT / "src/OmegaChecks/strict_lake.py", archive / "src/OmegaChecks/strict_lake.py")
        (archive / "src/OmegaChecks/InitCompiler.lean").write_text("import Lean\n")
        (archive / "strict/OmegaInit/Source.lean").write_text("def strictWitness := 1\n")
        (archive / "src/OmegaMath/Consumer.lean").write_text(
            "import OmegaInit.Source\nexample : strictWitness = 1 := rfl\n")
        path = compiled_path(archive, ["OmegaMath.Consumer"], True)
        assert any((Path(p) / "OmegaMath/Consumer.olean").is_file() for p in path.split(os.pathsep))


def check_witness_backends(lean, search):
    with tempfile.TemporaryDirectory(prefix="protected-witnesses-") as temporary:
        directory = Path(temporary)
        path = os.pathsep.join([str(directory), search])
        for name, body in [
            ("D5.StrictWitness", "def portableWitness := 1"),
            ("D5.OfficialWitness", "import OmegaBuild.Commands\ncompile_only_with_mathlib"),
            ("D5.InheritedWitness", "import D5.OfficialWitness"),
            ("OmegaMath.RestrictedPublication", "import D5.OfficialWitness"),
        ]:
            source = directory.joinpath(*name.split(".")).with_suffix(".lean")
            source.parent.mkdir(exist_ok=True)
            source.write_text(body + "\n")
            subprocess.run([lean, "-R", directory, "-o", source.with_suffix(".olean"), source],
                           cwd=ROOT, env={**os.environ, "LEAN_PATH": path}, check=True)
        owners = ["D5.StrictWitness", "D5.OfficialWitness", "D5.InheritedWitness"]
        assert strict_witnesses(path, owners) == ["D5.StrictWitness"]
        try:
            strict_witnesses(path, ["OmegaMath.RestrictedPublication"])
        except RuntimeError as error:
            assert "Omega publication requires both backends" in str(error), error
        else:
            raise AssertionError("accepted an official-only protected publication")


def check():
    lean = output("lake", "env", "printenv", "LEAN").strip()
    check_archive_build()
    subprocess.run(["lake", "build", "+OmegaBuild.Commands"], cwd=ROOT, check=True)
    check_witness_backends(lean, output("lake", "env", "printenv", "LEAN_PATH").strip())
    for profile in (["-f", strict_config()], []):
        search = output("lake", *profile, "env", "printenv", "LEAN_PATH").strip()
        with tempfile.TemporaryDirectory(prefix="omega-protected-") as temp:
            base = compile_source(lean, search, Path(temp) / "base", OBJECT + THEOREM)
            client = "example (p : Prop) : Omega.Eq (Omega.Subject p) p := Omega.Eq.refl p"
            check_client(lean, base, MODULE, client, True)
            hidden = compile_source(lean, search, Path(temp) / "candidate", "@[no_expose] " + OBJECT + THEOREM)
            check_client(lean, hidden, MODULE, client, False)
            irreducible = OBJECT + THEOREM + "attribute [irreducible] Subject\n"
            sealed = compile_source(lean, search, Path(temp) / "candidate", irreducible)
            check_client(lean, sealed, MODULE, client, False)
            for body, marker in [
                (irreducible, "protected public unfolding changed"),
                (OBJECT + THEOREM + "attribute [reducible] Subject\n", ""),
                ("@[no_expose] " + OBJECT + THEOREM, "no longer exposes its body"),
                (OBJECT + THEOREM + "theorem extra (p : Prop) : p → p := fun x => x\n", ""),
                (OBJECT + THEOREM + "private def hiddenPrime (p : Prop) : Prop := p\n", "new OmegaMath object"),
                (OBJECT + THEOREM + "structure HiddenObject where value : Nat\n", "new OmegaMath object"),
                (OBJECT + THEOREM + "axiom fake : ∀ p : Prop, p\n", "new OmegaMath object"),
                ("def Subject (_p : Prop) : Prop := True\ntheorem stable (p : Prop) (_h : p) : Subject p := True.intro\n",
                 "Subject"),
                (OBJECT, "removed protected declaration"),
                (OBJECT + "theorem stable (p : Prop) : p → p → p := fun h _ => h\n", "stable"),
                (OBJECT + "def stable := Subject\n", "kind changed"),
            ]:
                new = compile_source(lean, search, Path(temp) / "candidate", body)
                result = subprocess.run([AUDIT, "--protected-objects", base, new, MODULE, "--", MODULE],
                                        cwd=ROOT, capture_output=True, text=True)
                if bool(result.returncode) != bool(marker) or marker not in result.stderr:
                    raise RuntimeError(f"Expected {marker!r}: {result.stdout}{result.stderr}")
            result = subprocess.run([AUDIT, "--protected-objects", base, new, MODULE, "--"],
                                    cwd=ROOT, capture_output=True, text=True)
            if not result.returncode or "removed protected OmegaMath module" not in result.stderr:
                raise RuntimeError(f"Expected missing module: {result.stdout}{result.stderr}")
            for reexport in (MODULE, "OmegaMathlib.Data.Nat.Prime.Defs", "OmegaInit.Prelude"):
                for folder, modifier in [("base", "public "), ("candidate", "")]:
                    directory = Path(temp) / folder
                    file = directory / "OmegaMath.lean"
                    file.write_text(f"module\nprelude\n{modifier}import {reexport}\n")
                    subprocess.run([lean, "-R", directory, "-o", file.with_suffix(".olean"), file], cwd=ROOT,
                                   env={**os.environ, "LEAN_PATH": str(directory) + os.pathsep + search}, check=True)
                result = subprocess.run([AUDIT, "--protected-objects", base, new, "OmegaMath", "--", "OmegaMath"],
                                        cwd=ROOT, capture_output=True, text=True)
                if not result.returncode or "no longer re-exports protected module" not in result.stderr:
                    raise RuntimeError(f"Expected hidden public import: {result.stdout}{result.stderr}")
            legacy = ("inductive Carrier where | one\n"
                      "def Predicate (_ : Nat) : Prop := True\n"
                      "theorem Helper (n : Nat) : Predicate n := True.intro\n")
            base = compile_source(lean, search, Path(temp) / "base", legacy)
            for addition, marker in [
                ("theorem extra (r : Carrier) : Eq r r := Eq.refl r\n", "statement uses project object Omega.Carrier"),
                ("theorem extra (n : Nat) : Predicate n := Helper n\n",
                 "statement uses project object Omega.Predicate"),
                ("def extra (n : Nat) : Predicate n := Helper n\n", "statement uses project object Omega.Predicate"),
                ("namespace More\nexport Omega (Helper)\nend More\n", "statement uses project object Omega.Predicate"),
                ("private theorem inner (n : Nat) : Predicate n := Helper n\n"
                 "theorem extra (n : Nat) : True := inner n\n", ""),
            ]:
                new = compile_source(lean, search, Path(temp) / "candidate", legacy + addition)
                result = subprocess.run([AUDIT, "--protected-objects", base, new, MODULE, "--", MODULE],
                                        cwd=ROOT, capture_output=True, text=True)
                if bool(result.returncode) != bool(marker) or marker not in result.stderr:
                    raise RuntimeError(f"Expected {marker!r}: {result.stdout}{result.stderr}")
            port_header = HEADER.replace("OmegaInit.Prelude", "OmegaMathlib.Data.Nat.Prime.Defs")
            old_helper = "def Historical (p : Prop) : Prop := And p True\n"
            old_object = "def Subject (n : Nat) : Prop := Historical (OmegaMathlib.Nat.Prime n)\n"
            alias = "abbrev Subject := OmegaMathlib.Nat.Prime\n"
            witness = ("theorem bridge (n : Nat) : Iff (Historical (OmegaMathlib.Nat.Prime n)) "
                       "(OmegaMathlib.Nat.Prime n) := Iff.intro And.left (fun h => And.intro h True.intro)\n")
            base = compile_source(lean, search, Path(temp) / "base", old_helper + old_object, port_header)
            d5 = "D5.Preserved"
            representation = ("@[expose] public def D5.old (n : Omega.Nat) : Prop := "
                              "Omega.Historical (OmegaMathlib.Nat.Prime n)\n")
            relation = ("public theorem D5.bridge (n : Omega.Nat) : "
                        "Omega.Iff (D5.old n) (OmegaMathlib.Nat.Prime n) := "
                        "Omega.Iff.intro Omega.And.left (fun h => Omega.And.intro h Omega.True.intro)\n")
            for body, d5_source, expected in [
                (alias, representation + relation, ""),
                (alias, representation + relation + "attribute [irreducible] D5.old\n",
                 "missing observable D5 representation"),
                (alias, representation.replace("@[expose]", "@[no_expose]") + relation,
                 "missing observable D5 representation"),
                (old_object + "abbrev direct := OmegaMathlib.Nat.Prime\n", None, ""),
                (old_object + "abbrev copy := Subject\n", None, "new OmegaMath object"),
                (alias, None, "missing observable D5 representation"),
                (alias + witness, None, "missing observable D5 representation"),
                (alias, representation, "missing all-input correspondence in D5"),
                (alias, representation + "public theorem D5.irrelevant (n : Omega.Nat) : "
                 "Omega.Iff (D5.old n) (D5.old n) := Omega.Iff.intro (fun h => h) (fun h => h)\n",
                 "missing all-input correspondence in D5"),
            ]:
                folder = Path(temp) / "candidate"
                new = compile_source(lean, search, folder, old_helper + body, port_header)
                owners = []
                if d5_source:
                    file = folder.joinpath(*d5.split(".")).with_suffix(".lean")
                    file.parent.mkdir(parents=True, exist_ok=True)
                    file.write_text(f"module\nprelude\npublic import {MODULE}\n" + d5_source)
                    subprocess.run([lean, "-R", folder, "-o", file.with_suffix(".olean"), file],
                                   cwd=ROOT, env={**os.environ, "LEAN_PATH": new}, check=True)
                    check_client(lean, new, d5, "example (n : Omega.Nat) : Omega.Eq (D5.old n) "
                                 "(Omega.Historical (OmegaMathlib.Nat.Prime n)) := Omega.Eq.refl _",
                                 "@[no_expose]" not in d5_source and "[irreducible]" not in d5_source)
                    owners.append(d5)
                result = subprocess.run([AUDIT, "--protected-objects", base, new, MODULE, "--", MODULE,
                                         "--legacy", *owners], cwd=ROOT, capture_output=True, text=True)
                if bool(result.returncode) != bool(expected) or expected not in result.stderr:
                    raise RuntimeError(f"Expected {expected!r}: {result.stdout}{result.stderr}")



if __name__ == "__main__":
    check()
