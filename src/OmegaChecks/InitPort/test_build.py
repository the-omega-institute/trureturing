import json
import tempfile
import unittest
from pathlib import Path

from build import cyclic_declarations, snapshot_seed


class SeedSnapshotTest(unittest.TestCase):
    def test_local_seed_tracks_sources_and_detached_seed_keeps_its_modules(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources, build = root / "strict", root / "build"
            (sources / "OmegaInit").mkdir(parents=True)
            (sources / "OmegaInit.lean").touch()
            (sources / "OmegaInit/Present.lean").touch()
            (build / "OmegaInit").mkdir(parents=True)
            parts = (".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig")
            for module in ("OmegaInit", "OmegaInit/Present", "OmegaInit/Deleted"):
                for part in parts:
                    (build / (module + part)).write_text(module)
            snapshot_seed(build, root / "local", sources)
            snapshot_seed(build, root / "detached")
            for part in parts:
                for module in ("OmegaInit", "OmegaInit/Present"):
                    self.assertEqual((root / "local" / (module + part)).read_text(), module)
                deleted = "OmegaInit/Deleted" + part
                self.assertFalse((root / "local" / deleted).exists())
                self.assertEqual((root / "detached" / deleted).read_text(), "OmegaInit/Deleted")


class ModuleDependenciesTest(unittest.TestCase):
    def test_upstream_dependency_survives_multiple_reverse_proofs(self):
        rows = [
            ["Early", "", "[]", "[]"],
            ["Middle", "", "[]", '["Early"]'],
            ["Late", "", "[]", '["Middle"]'],
            ["Early", "convenience1", '["Late"]'],
            ["Early", "convenience2", '["Late"]'],
            ["Late", "matcher", '["Early"]'],
        ]
        with tempfile.TemporaryDirectory() as directory:
            edges = Path(directory) / "candidate-edges.jsonl"
            edges.write_text("".join(json.dumps(row) + "\n" for row in rows))
            rejected, order = cyclic_declarations(edges)
        self.assertEqual(set(rejected), {"convenience1", "convenience2"})
        self.assertLess(order.index("Early"), order.index("Late"))


if __name__ == "__main__":
    unittest.main()
