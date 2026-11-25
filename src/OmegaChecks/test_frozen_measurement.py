"""Exercise paired frozen dependencies against compiled portable modules.

Run with the project-scoped reportInspector already built:
    python3 -B src/OmegaChecks/test_frozen_measurement.py
"""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import portable


MIXED = "OmegaChecks.Portable.FrozenDependencies"
OFFICIAL = "D5.S0.Computability.KernelComponentPayload"
TETRAHEDRON = "D5.S3.Quantum.AURICOmega.RationalBlochTetrahedron"


class FrozenMeasurement(unittest.TestCase):
    def test_compiled_pair(self):
        inspector = portable.ROOT / ".lake/build/lean-inspector/producer/bin/reportInspector"
        self.assertTrue(inspector.is_file(), "prepare reportInspector before running this test")
        names = [OFFICIAL, MIXED, TETRAHEDRON]
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
            ordinary, mixed, tetrahedron = json.loads(published)
            self.assertFalse(ordinary["strictEligible"])
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
        name = MIXED
        source = portable.SRC / (name.replace(".", "/") + ".lean")
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
        for declarations in ([], [{**row, "nameKey": "extra"}], [{**row, "kind": "def"}]):
            with self.assertRaisesRegex(RuntimeError, "inventory differs|kind differs"):
                portable.attach_strict_measurement(copy.deepcopy(official), copy.deepcopy(official),
                    [{"module": "D5.Fixture", "declarations": declarations}], {"D5.Fixture"})


if __name__ == "__main__":
    unittest.main()
