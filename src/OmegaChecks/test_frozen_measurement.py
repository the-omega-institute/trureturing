"""Exercise paired frozen dependencies against compiled portable modules.

Run with the project-scoped reportInspector already built:
    python3 -B src/OmegaChecks/test_frozen_measurement.py
"""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import portable


MIXED = "OmegaChecks.Portable.FrozenDependencies"
MATHLIB_FACTORIAL = "OmegaChecks.Portable.MathlibFactorial"
OFFICIAL = "D5.S0.Computability.KernelComponentPayload"
PRIVATE_INDUCTIVE = "D5.S0.Computability.ConditionalComplexityFloor"
TETRAHEDRON = "D5.S3.Quantum.AURICOmega.RationalBlochTetrahedron"


class FrozenMeasurement(unittest.TestCase):
    def test_mixed_public_consumer(self):
        subprocess.run([sys.executable, "-B", "src/OmegaChecks/portable.py", "--backend", "both", MIXED],
                       cwd=portable.ROOT, check=True)
        report = json.loads((portable.ROOT / ".lake/build/omega-checks/selected-official-axioms.json").read_text())
        self.assertIn(MIXED, report["consumerModules"])
        self.assertEqual([row["axioms"] for row in report["declarations"]
                          if row["module"] == MIXED and row["name"].endswith(".mixedFib")],
                         [["Classical.choice"]])

    def test_mixed_frozen_provenance(self):
        pure = "D5.S3.Arith.EuclidLemma"
        names = [MIXED, pure]
        inspector = portable.ROOT / ".lake/build/lean-inspector/producer/bin/reportInspector"
        subprocess.run(["lake", "build", *("+" + name for name in names)], cwd=portable.ROOT, check=True)
        with tempfile.TemporaryDirectory(prefix="omega-frozen-mixed-") as directory:
            request, official, result = (Path(directory) / name for name in ("request", "official", "result"))
            request.write_text(json.dumps(names))
            subprocess.run(["lake", "env", inspector, "--frozen-dependencies-v1", request, official],
                           cwd=portable.ROOT, check=True)
            portable.frozen_measurement(request, official, inspector, result)
            mixed, isolated = json.loads(result.read_text())
            rows = [row for row in mixed["declarations"] if row["includeInStatement"]]
            self.assertEqual(len(rows), 2)
            private = next(row["strict_omega"] for row in rows if "privateFib" in row["nameKey"])
            public = next(row["strict_omega"] for row in rows if "mixedFib" in row["nameKey"])
            self.assertEqual(private["axioms"], [])
            self.assertEqual(public["axioms"], ["Classical.choice"])
            self.assertIn("Init", public["libraries"])
            self.assertIn("OmegaMathlib", public["libraries"])
            for row in isolated["declarations"]:
                if row["includeInStatement"]:
                    self.assertEqual(row["strict_omega"]["axioms"], [])
                    self.assertNotIn("Init", row["strict_omega"]["libraries"])

    def test_compiled_pair(self):
        inspector = portable.ROOT / ".lake/build/lean-inspector/producer/bin/reportInspector"
        self.assertTrue(inspector.is_file(), "prepare reportInspector before running this test")
        names = [OFFICIAL, MIXED, TETRAHEDRON, PRIVATE_INDUCTIVE, MATHLIB_FACTORIAL]
        subprocess.run(["lake", "build", *("+" + name for name in names)],
                       cwd=portable.ROOT, check=True)
        with tempfile.TemporaryDirectory(prefix="omega-frozen-test-") as temporary:
            tmp = Path(temporary)
            request, official, result = (tmp / name for name in ("request", "official", "result"))
            request.write_text(json.dumps(names))
            subprocess.run(["lake", "env", inspector, "--frozen-dependencies-v1", request, official],
                           cwd=portable.ROOT, check=True)
            portable.frozen_measurement(request, official, inspector, result)
            published = result.read_bytes()
            ordinary, mixed, tetrahedron, private_inductive, factorial = json.loads(published)
            self.assertFalse(factorial["strictEligible"])
            self.assertEqual(factorial["mathlibOnly"], [MATHLIB_FACTORIAL])
            self.assertTrue(any("mathlibFactorial" in row["nameKey"] and "Mathlib" in row["libraries"]
                                for row in factorial["declarations"] if row["includeInStatement"]))
            self.assertTrue(all("strict_omega" not in row for row in factorial["declarations"]))
            self.assertFalse(ordinary["strictEligible"])
            self.assertNotIn("mathlibOnly", ordinary)
            self.assertTrue(mixed["strictEligible"])
            self.assertTrue(tetrahedron["strictEligible"])
            self.assertTrue(all("strict_omega" not in row for row in ordinary["declarations"]))
            rows = [row for row in mixed["declarations"] if row["includeInStatement"]]
            self.assertEqual(len(rows), 2)
            private = next(row["strict_omega"] for row in rows if "privateFib" in row["nameKey"])
            self.assertEqual(private["axioms"], [])
            strict = next(row["strict_omega"] for row in rows if "mixedFib" in row["nameKey"])
            self.assertEqual(strict["axioms"], ["Classical.choice"])
            self.assertIn("OmegaMathlib", strict["libraries"])
            self.assertIn("Init", strict["libraries"])
            row, = tetrahedron["declarations"]
            self.assertEqual(row["axioms"], ["propext"])
            self.assertEqual(row["strict_omega"]["axioms"], [])
            self.assertEqual(row["strict_omega"]["libraries"], ["OmegaInit", "OmegaMath"])
            self.assertNotEqual(row["strict_omega"]["statement_type_address"], row["statementTypeAddress"])
            eliminators = [row for row in private_inductive["declarations"]
                           if row["nameKey"].endswith((",11:noConfusion)", ",15:noConfusionType)"))]
            self.assertEqual(len(eliminators), 2)
            for row in eliminators:
                self.assertEqual(row["strict_omega"]["axioms"], [])
            generated = [row for row in private_inductive["declarations"] if row.get("officialDerivedOnly")]
            self.assertTrue(any("sizeOf_spec" in row["nameKey"] for row in generated))
            self.assertTrue(all(row["includeInStatement"] and "strict_omega" not in row for row in generated))
            self.assertTrue(all("strict_omega" in row for row in private_inductive["declarations"]
                                if row["includeInStatement"] and row not in generated))

            # A stale canonical measurement must never replace an existing response.
            stale = json.loads(official.read_text())
            stale[1]["declarations"][0]["statementTypeAddress"] = "sha256:" + "0" * 64
            stale_file = tmp / "stale"
            stale_file.write_text(json.dumps(stale))
            with self.assertRaisesRegex(RuntimeError, "staged official measurement differs"):
                portable.frozen_measurement(request, stale_file, inspector, result)
            self.assertEqual(result.read_bytes(), published)

            self.check_crossed_artifacts(tmp)
            self.check_source_mutation(request, official, inspector, result, published)
            portable.frozen_measurement(request, official, inspector, result)
            self.assertEqual(result.read_bytes(), published)

    def check_source_mutation(self, request, official, inspector, result, published):
        source = portable.SRC / (MIXED.replace(".", "/") + ".lean")
        original_fingerprint = portable.source_fingerprint
        # Change a private copy between measurements. Concurrent Lake builds can
        # continue to use the actual source and its compiled artifacts.
        with tempfile.TemporaryDirectory() as directory:
            copy_path = Path(directory) / source.name
            copy_path.write_bytes(source.read_bytes())

            def fingerprint(path):
                return original_fingerprint(copy_path if path == source else path)

            real_measure = portable.measure_staged

            def changed_source(*args, **kwargs):
                measured = real_measure(*args, **kwargs)
                with copy_path.open("ab") as stream:
                    stream.write(b"\n")
                return measured

            with patch.object(portable, "source_fingerprint", side_effect=fingerprint), \
                 patch.object(portable, "measure_staged", side_effect=changed_source):
                with self.assertRaisesRegex(RuntimeError, "source changed during the backend check"):
                    portable.frozen_measurement(request, official, inspector, result)
            self.assertEqual(result.read_bytes(), published)

    def check_crossed_artifacts(self, tmp):
        name = TETRAHEDRON
        source = portable.ROOT / (name.replace(".", "/") + ".lean")
        relative = Path(name.replace(".", "/") + ".olean")
        official = portable.ROOT / ".lake/build/lib/lean" / relative
        manifest = json.loads((portable.ROOT / "lake-manifest.json").read_text())
        packages = {(portable.ROOT / manifest["packagesDir"] / p["name"] / ".lake/build/lib/lean").resolve()
                    for p in manifest["packages"]}
        lean = portable.output("lake", "env", "printenv", "LEAN").strip()
        environment = {k: v for k, v in os.environ.items() if k not in {"LEAN_PATH", "LEAN_SRC_PATH"}}
        real_output = portable.output

        def crossed_path(*args, **kwargs):
            result = real_output(*args, **kwargs)
            if "query" in args:
                lines = result.splitlines()
                lines[-1] = str(official)
                return "\n".join(lines)
            return result

        with patch.object(portable, "output", side_effect=crossed_path):
            with self.assertRaisesRegex(RuntimeError, "unexpected source file or artifact"):
                portable.backend_artifacts(True, False, {name: source}, tmp / "wrong-path",
                                           packages, lean, environment)

        real_copy = portable.shutil.copyfile

        def crossed_bytes(source_path, destination):
            if source_path.name == relative.name:
                source_path = official
            return real_copy(source_path, destination)

        with patch.object(portable.shutil, "copyfile", side_effect=crossed_bytes):
            with self.assertRaisesRegex(RuntimeError, "artifact differs from its Lake trace"):
                portable.backend_artifacts(True, False, {name: source}, tmp / "wrong-bytes",
                                           packages, lean, environment)

    def test_inventory_mismatch(self):
        row = {"nameKey": "name", "kind": "theorem", "statementTypeAddress": "sha256:" + "a" * 64,
               "includeInStatement": True, "axioms": [], "libraries": []}
        official = [{"module": "D5.Fixture", "declarations": [row]}]
        def inventory(*declarations):
            return portable.paired_inventory(official, copy.deepcopy(official),
                [{"module": "D5.Fixture", "declarations": declarations}], {"D5.Fixture"})

        with self.assertRaisesRegex(RuntimeError, "kind differs"):
            inventory({**row, "kind": "def"})
        with self.assertRaisesRegex(RuntimeError, "did not certify"):
            portable.attach_strict_measurement(copy.deepcopy(official), [], inventory(), [])
        for axiom in ("sorryAx", "Fixture.unauthorized"):
            for included in (True, False):
                with self.subTest(axiom=axiom, included=included):
                    with self.assertRaisesRegex(RuntimeError, "inadmissible strict axioms"):
                        inventory({**row, "nameKey": "strictOnly", "includeInStatement": included, "axioms": [axiom]})

    def test_rejects_unmatched_private_source_declaration(self):
        inspector = portable.ROOT / ".lake/build/lean-inspector/producer/bin/reportInspector"
        subprocess.run(["lake", "build", "omegaAudit"], cwd=portable.ROOT, check=True)
        lean = portable.output("lake", "env", "printenv", "LEAN").strip()
        official_path = portable.output("lake", "env", "printenv", "LEAN_PATH").strip()
        name = "FrozenProvenanceProbe"
        with tempfile.TemporaryDirectory(prefix="omega-frozen-private-") as directory:
            tmp = Path(directory)
            request, inventory = (tmp / path for path in ("request.json", "inventory.json"))
            request.write_text(json.dumps([name]))
            artifacts, measurements = [], []
            for private in (False, True):
                stage = tmp / str(private)
                stage.mkdir()
                source = stage / (name + ".lean")
                source.write_text("module\npublic theorem common {p : Prop} (h : p) : p := h\n"
                                  + ("private theorem Choice.ctorIdx {p : Prop} (h : p) : p := h\n"
                                     if private else ""))
                search = os.pathsep.join([str(stage), official_path])
                subprocess.run([lean, "-R", stage, "-o", source.with_suffix(".olean"), source],
                               env={**os.environ, "LEAN_PATH": search}, check=True)
                artifacts.append(search)
                measurements.append(portable.measure_staged(inspector, request, [name], search,
                                                            stage / "measurement.json", os.environ))
            for strict, official in ((0, 1), (1, 0)):
                rows = measurements[official]
                inventory.write_text(json.dumps(portable.paired_inventory(rows, rows, measurements[strict], {name})))
                result = subprocess.run([portable.AUDIT, "--consumer", artifacts[strict], artifacts[official], name],
                                        env={**os.environ, "OMEGA_FROZEN_INVENTORY": str(inventory)},
                                        capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("one-sided frozen declaration", result.stderr)
                self.assertIn("Choice.ctorIdx", result.stderr)


if __name__ == "__main__":
    unittest.main()
