"""Relocate a bounded native Census package using the existing warm fixture owner."""

import json
import pathlib
import re
import shutil
import sys
import tomllib
import unittest

INSPECTOR = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(INSPECTOR / "tests"))
from test_native_support import NativeTestSupport, ROOT


class NativeRelocationTests(NativeTestSupport, unittest.TestCase):
    def test_census_callers_in_relocated_package_with_spaces(self):
        shutil.copytree(ROOT / "tools/lean-inspector-interface", self.root / "declaration package",
                        ignore=shutil.ignore_patterns(".lake", "__pycache__"))
        shutil.copytree(INSPECTOR / "Census", self.root / "tools/lean-inspector/Census",
                        ignore=shutil.ignore_patterns("__pycache__"))
        for name in ("NameWire", "RegistryTypes", "BindingRecords", "CatalogRecords",
                     "EscapeEvidence", "StructuralProvenance", "Census/Ownership",
                     "Census/Stream", "Census/Membership"):
            self.copy("tools/lean-inspector/LeanInformationAudit/" + name + ".lean")
        # Follow the copied packages' actual imports, including the contract's
        # mathematical types. Keep compiler/toolchain imports external.
        pending = list((self.root / "declaration package").rglob("*.lean")) + list(
            (self.root / "tools/lean-inspector/LeanInformationAudit").rglob("*.lean"))
        seen = set()
        while pending:
            source = pending.pop()
            if source in seen:
                continue
            seen.add(source)
            for module in re.findall(r"(?m)^(?:public )?import (\S+)", source.read_text()):
                relative = module.replace(".", "/") + ".lean"
                if module.startswith("D5."):
                    relative = pathlib.Path(relative)
                elif module.startswith("LeanInformationAudit."):
                    relative = pathlib.Path("tools/lean-inspector") / relative
                else:
                    continue
                target = self.root / relative
                if not target.is_file():
                    self.copy(str(relative))
                pending.append(target)
        # The typed contract imports real mathematics, so use its pinned
        # upstream packages rather than the support fixture's Cache-only provider.
        upstream = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
        mathlib = next(package for package in upstream if package["name"] == "mathlib")
        config = self.root / "lakefile.toml"
        text = config.read_text()
        requirement = next(requirement for requirement in tomllib.loads(text)["require"]
                           if requirement["name"] == "mathlib")
        text = text.replace(f'git = "{requirement["git"]}"\nrev = "{requirement["rev"]}"',
                            f'git = "{mathlib["url"]}"\nrev = "{mathlib["inputRev"]}"')
        config.write_text(text)
        for relative in ("lake-manifest.json", "Reg/lake-manifest.json",
                         "tools/lean-inspector-reg/lake-manifest.json"):
            manifest = json.loads((self.root / relative).read_text())
            manifest["packages"] = [package for package in manifest["packages"]
                                    if package["type"] != "git"] + [
                dict(package, inherited=relative != "lake-manifest.json" or package["inherited"])
                for package in upstream]
            self.write(relative, json.dumps(manifest))
        # Keep the support fixture's synthetic driver in this library's source root.
        (self.root / "LeanInformationAudit/SealCommand.lean").rename(
            self.root / "tools/lean-inspector/LeanInformationAudit/SealCommand.lean")
        (self.root / "LeanInformationAudit").rmdir()
        policy = self.root / "lean-report-inputs.json"
        policy.write_text(policy.read_text().replace('"LeanInformationAudit/SealCommand.lean"',
            '"tools/lean-inspector/LeanInformationAudit/SealCommand.lean"'))
        # This fixture puts the same dependency under a different source root.
        # Only Lake knows that location; Census cannot name it as a special case.
        config = self.root / "declaration package/lakefile.toml"
        config.write_text(config.read_text().replace('"../../.lake/', '"../.lake/').replace(
            'path = "../.."', 'path = ".."'))
        manifest = json.loads((config.parent / "lake-manifest.json").read_text())
        manifest["packagesDir"] = "../.lake/packages"
        next(package for package in manifest["packages"]
             if package["name"] == "trureturing")["dir"] = ".."
        self.write("declaration package/lake-manifest.json", json.dumps(manifest))
        config = self.root / "lakefile.toml"
        config.write_text(config.read_text().replace('name = "LeanInformationAudit"\n',
            'name = "LeanInformationAudit"\nsrcDir = "tools/lean-inspector"\n') +
            '\n[[require]]\nname = "leanInspectorInterface"\npath = "declaration package"\n')
        manifest = json.loads((self.root / "lake-manifest.json").read_text())
        manifest["packages"].append(dict(type="path", scope="", name="leanInspectorInterface",
            manifestFile="lake-manifest.json", inherited=False, dir="declaration package",
            configFile="lakefile.toml"))
        self.write("lake-manifest.json", json.dumps(manifest))
        # Fetch the exact pinned snapshots, without unrelated upstream history.
        # The canonical cache owner still supplies and validates their build cache.
        for package in upstream:
            directory = self.root / ".lake/packages" / package["name"]
            directory.mkdir(parents=True)
            for arguments in (("init", "--quiet"),
                              ("remote", "add", "origin", package["url"]),
                              ("fetch", "--quiet", "--depth=1", "origin", package["rev"]),
                              ("checkout", "--quiet", "--detach", package["rev"])):
                result = self.guarded_command(["git", "-C", str(directory), *arguments])
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        # The cache producer receives precisely the external import roots of
        # this bounded fixture. Lake still checks every compiled dependency.
        imports = {module for source in seen for module in
                   re.findall(r"(?m)^(?:public )?import (\S+)", source.read_text())
                   if module.split(".")[0] not in
                   {"D5", "LeanInformationAudit", "LeanInformationAuditInterface", "Lean", "Init", "Std"}}
        self.write("bin/lake", "#!/usr/bin/env python3\nimport os, sys\n"
                   + f"lake, roots = {self.lake!r}, {sorted(imports)!r}\n"
                   + "args = sys.argv[1:]\n"
                   + "if args == ['exe', 'cache', 'get']: args += roots\n"
                   + "os.execv(lake, [lake, *args])\n")
        (self.root / "bin/lake").chmod(0o755)
        self.env["LAKE_BIN"] = str(self.root / "bin/lake")
        self.ensure()
        command = ["make", "lean", "LEAN_TARGETS=@trureturing/LeanInformationAudit.Census.Stream "
                   "@trureturing/LeanInformationAudit.Census.Membership"]
        result = self.guarded_command(command, cwd=self.root, env=self.env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        donor = self.root
        destination = donor / "relocated census with spaces"
        destination.mkdir()
        for child in list(donor.iterdir()):
            if child == destination:
                continue
            if child.is_dir():
                shutil.copytree(child, destination / child.name)
            else:
                shutil.copy2(child, destination / child.name)
        original_env = self.env
        self.root = destination
        self.env = {key: value.replace(str(donor), str(destination))
                    for key, value in original_env.items()}
        try:
            # Revalidate the relocated warm inputs through the canonical make owner.
            result = self.guarded_command(command, cwd=self.root, env=self.env)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            result = self.guarded_command([sys.executable,
                "tools/lean-inspector/Census/tests/native_fixtures.py", "-v"],
                cwd=self.root, env=self.env)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn("Ran 2 tests", result.stderr)
        finally:
            self.root, self.env = donor, original_env


if __name__ == "__main__":
    unittest.main()
