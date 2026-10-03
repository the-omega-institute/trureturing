"""Behavioral contracts for source enumeration and seal export inputs."""

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


PROGRAM = Path(__file__).resolve().parents[1] / "reg-seal-export.py"


class ExportTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="seal export inputs ")
        self.addCleanup(self.temporary.cleanup)
        self.repository = Path(self.temporary.name) / "repository with spaces"
        (self.repository / "Reg").mkdir(parents=True)

    def source(self, relative, contents):
        path = self.repository / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents, encoding="utf-8")

    def invoke(self, *arguments):
        return subprocess.run([sys.executable, str(PROGRAM), "--repository",
                               str(self.repository), *arguments], text=True,
                              capture_output=True, cwd=self.temporary.name)

    def test_missing_repository_named(self):
        result = self.invoke("--repository", str(self.repository / "missing"), "--list")
        self.assertEqual(result.returncode, 66)
        self.assertIn("MissingRepository", result.stderr)
        self.assertEqual(result.stdout, "")

    def test_missing_root_named_before_build(self):
        self.source("Reg/Catalogs/Present.lean", "#seal_information_theory\n")
        result = self.invoke("--roots", "Reg.Catalogs.Absent", "--list")
        self.assertEqual(result.returncode, 66)
        self.assertIn("MissingRoot root=Reg.Catalogs.Absent", result.stderr)
        self.assertEqual(result.stdout, "")

    def test_existing_unsealed_root_named(self):
        self.source("Reg/Catalogs/Plain.lean", "def x := 1\n")
        result = self.invoke("--roots", "Reg.Catalogs.Plain", "--list")
        self.assertEqual(result.returncode, 66)
        self.assertIn("UnsealedRoot root=Reg.Catalogs.Plain", result.stderr)

    def test_invalid_root_name_rejected(self):
        result = self.invoke("--roots", "Reg/../D5", "--list")
        self.assertEqual(result.returncode, 64)
        self.assertIn("InvalidRoot", result.stderr)

    def test_duplicate_root_rejected(self):
        self.source("Reg/Catalogs/Present.lean", "#seal_information_theory\n")
        result = self.invoke("--roots", "Reg.Catalogs.Present", "Reg.Catalogs.Present", "--list")
        self.assertEqual(result.returncode, 64)
        self.assertIn("DuplicateRoot", result.stderr)

    def test_empty_inventory_named(self):
        result = self.invoke("--list")
        self.assertEqual(result.returncode, 66)
        self.assertIn("NoSealedRoots", result.stderr)

    def test_unreadable_source_names_root(self):
        self.source("Reg/Catalogs/Broken.lean", "")
        (self.repository / "Reg/Catalogs/Broken.lean").write_bytes(b"\xff")
        result = self.invoke("--list")
        self.assertEqual(result.returncode, 66)
        self.assertIn("UnreadableRoot root=Reg.Catalogs.Broken", result.stderr)

    def test_typed_reserved_root_without_seal_named(self):
        self.source("Reg/Catalogs/Missing/SealedCatalog.lean", "def x := 1\n")
        result = self.invoke("--list")
        self.assertEqual(result.returncode, 66)
        self.assertIn("MissingTypedSeal root=Reg.Catalogs.Missing.SealedCatalog", result.stderr)

    def test_enumerates_both_forms_in_sorted_order(self):
        self.source("Reg/Catalogs/Zeta.lean", "set_option maxHeartbeats 100 in\n#seal_information_theory\n")
        self.source("Reg/Catalogs/Alpha/SealedCatalog.lean", """
namespace Reg.Catalogs.Alpha.SealedCatalog
def seal : LeanInformationAuditInterface.Contract.Seal := {
  rootId := `Reg.Catalogs.Alpha.SealedCatalog, options := #[] }
end Reg.Catalogs.Alpha.SealedCatalog
""")
        result = self.invoke("--list")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual([json.loads(line)["root"] for line in result.stdout.splitlines()],
                         ["Reg.Catalogs.Alpha.SealedCatalog", "Reg.Catalogs.Zeta"])

    def test_comments_strings_and_other_paths_are_not_roots(self):
        self.source("Reg/Catalogs/Real.lean", "#seal_information_theory\n")
        self.source("Reg/Catalogs/Noise.lean", '''
/- #seal_information_theory /- nested -/ -/
-- #seal_information_theory
def text := "#seal_information_theory \\\" Contract.Seal"
''')
        self.source("Reg/D5/SealedCatalog.lean", "def x : Contract.Seal := { }\n")
        result = self.invoke("--list")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual([json.loads(line)["root"] for line in result.stdout.splitlines()],
                         ["Reg.Catalogs.Real"])

    def test_typed_short_contract_form(self):
        self.source("Reg/Catalogs/Short/SealedCatalog.lean",
                    "def seal : Contract.Seal := { rootId := `Reg.Catalogs.Short.SealedCatalog, options := #[] }\n")
        result = self.invoke("--list")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["root"], "Reg.Catalogs.Short.SealedCatalog")

    def test_explicit_roots_sorted_and_output_paths_deterministic(self):
        for leaf in ("Zeta", "Alpha"):
            self.source(f"Reg/Catalogs/{leaf}.lean", "#seal_information_theory\n")
        output = (Path(self.temporary.name) / "output with spaces").resolve()
        arguments = ("--roots", "Reg.Catalogs.Zeta", "Reg.Catalogs.Alpha",
                     "--output-dir", str(output), "--list")
        first, second = self.invoke(*arguments), self.invoke(*arguments)
        self.assertEqual(first.returncode, 0, first.stderr)
        self.assertEqual(first.stdout, second.stdout)
        rows = [json.loads(line) for line in first.stdout.splitlines()]
        self.assertEqual([row["path"] for row in rows],
                         [str(output / "Reg/Catalogs/Alpha/seal.json"),
                          str(output / "Reg/Catalogs/Zeta/seal.json")])

    def test_repository_output_rejected(self):
        self.source("Reg/Catalogs/Real.lean", "#seal_information_theory\n")
        result = self.invoke("--output-dir", str(self.repository / "output"), "--list")
        self.assertEqual(result.returncode, 64)
        self.assertIn("OutputInsideRepository", result.stderr)

    def test_repository_tmpdir_rejected_before_allocating_output(self):
        self.source("Reg/Catalogs/Real.lean", "#seal_information_theory\n")
        temporary = self.repository / "temporary"
        temporary.mkdir()
        result = subprocess.run([sys.executable, str(PROGRAM), "--repository",
                                 str(self.repository), "--list"], text=True,
                                capture_output=True, env=dict(os.environ, TMPDIR=str(temporary)))
        self.assertEqual(result.returncode, 64)
        self.assertIn("OutputInsideRepository", result.stderr)
        self.assertEqual(list(temporary.iterdir()), [])

    def test_output_child_symlink_into_repository_rejected(self):
        self.source("Reg/Catalogs/Real.lean", "#seal_information_theory\n")
        output = Path(self.temporary.name) / "outside output"
        output.mkdir()
        (output / "Reg").symlink_to(self.repository / "Reg", target_is_directory=True)
        result = self.invoke("--output-dir", str(output), "--list")
        self.assertEqual(result.returncode, 64)
        self.assertIn("OutputInsideRepository", result.stderr)
        self.assertEqual(result.stdout, "")


class ProducerResultTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        spec = importlib.util.spec_from_file_location("seal_export", PROGRAM)
        cls.program = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.program)

    def test_export_failure_has_root_and_original_exit(self):
        with self.assertRaises(self.program.ExportError) as caught:
            self.program.check_export("Reg.Catalogs.Example", 7, Path("missing.json"))
        self.assertEqual(caught.exception.code, 7)
        self.assertIn("ExportFailed root=Reg.Catalogs.Example exit=7", str(caught.exception))

    def test_invalid_dependency_manifest_named(self):
        with tempfile.TemporaryDirectory() as directory:
            repository = Path(directory)
            manifest = repository / "tools/lean-inspector-reg/lake-manifest.json"
            manifest.parent.mkdir(parents=True)
            for value in ('broken json', '{}', '{"packages":[{}]}'):
                manifest.write_text(value)
                with self.assertRaises(self.program.ExportError) as caught:
                    self.program.export_manifest(repository)
                self.assertEqual(caught.exception.code, 66)
                self.assertIn("InvalidBuildManifest", str(caught.exception))

    def test_success_without_artifact_named(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(self.program.ExportError) as caught:
                self.program.check_export("Reg.Catalogs.Example", 0, Path(directory) / "missing.json")
        self.assertEqual(caught.exception.code, 66)
        self.assertIn("MissingSealArtifact root=Reg.Catalogs.Example", str(caught.exception))

    def test_malformed_or_empty_artifact_named(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "seal.json"
            for contents in ("not json", '{}', '{"schema":"lean-intrinsic-information-escape-seal","arenas":[]}'):
                path.write_text(contents, encoding="utf-8")
                with self.assertRaises(self.program.ExportError) as caught:
                    self.program.check_export("Reg.Catalogs.Example", 0, path)
                self.assertIn("InvalidSealArtifact root=Reg.Catalogs.Example", str(caught.exception))

    def test_valid_producer_artifact_accepted_without_rewriting(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "seal.json"
            contents = json.dumps(dict(schema="lean-intrinsic-information-escape-seal",
                                       catalog_mode="single-compilation-leave-one-out",
                                       arenas=[dict(arena="Arena.example")]))
            path.write_text(contents, encoding="utf-8")
            self.program.check_export("Reg.Catalogs.Example", 0, path)
            self.assertEqual(path.read_text(encoding="utf-8"), contents)


if __name__ == "__main__":
    unittest.main()
