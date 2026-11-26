import json
import tempfile
import unittest
from pathlib import Path

from build import cyclic_declarations


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
