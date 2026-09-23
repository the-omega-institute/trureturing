"""Behavioral contracts for bounded, complete cache material validation."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "tools/scripts/worktree"))
import cache_material as material


class CacheMaterialContracts(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="cache-material-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.data = self.root / "data"
        self.data.mkdir()
        for name, value in [("a", b"alpha"), ("b", b"beta"),
                            ("nested/c", b"gamma"), ("nested/d", b"delta")]:
            path = self.data / name
            path.parent.mkdir(exist_ok=True)
            path.write_bytes(value)
        self.expected = material.files(self.data)

    def test_declared_material_copy_is_complete_and_independently_owned(self):
        destination = self.root / "private"
        self.assertEqual(self.expected, material.files(self.data, expected=self.expected, copy_to=destination))
        for row in self.expected:
            source, copied = self.data / row["path"], destination / row["path"]
            self.assertNotEqual(source.stat().st_ino, copied.stat().st_ino)
            self.assertEqual(source.read_bytes(), copied.read_bytes())
        (self.data / "a").write_bytes(b"later producer change")
        self.assertEqual(b"alpha", (destination / "a").read_bytes())

    def test_bad_declared_material_is_rejected_before_hashing(self):
        for defect in ("duplicate", "escape", "mode", "digest"):
            rows = json.loads(json.dumps(self.expected))
            if defect == "duplicate": rows.append(rows[0])
            elif defect == "escape": rows[0]["path"] = "../outside"
            elif defect == "mode": rows[0]["mode"] = True
            else: rows[0]["sha256"] = "invalid"
            with self.subTest(defect=defect), mock.patch.object(material, "sha",
                    side_effect=AssertionError("read before validation")):
                with self.assertRaises(ValueError): material.files(self.data, expected=rows)
        with self.assertRaises(ValueError): material.files(self.data, copy_to=self.root / "unchecked")

    def test_missing_corrupt_or_changed_mode_material_cannot_be_accepted(self):
        file = self.data / "a"
        original, mode = file.read_bytes(), file.stat().st_mode & 0o777
        for defect in ("missing", "bytes", "mode"):
            with self.subTest(defect=defect):
                if defect == "missing": file.unlink()
                elif defect == "bytes": file.write_bytes(b"corruption")
                else: file.chmod(mode ^ 0o100)
                with self.assertRaises((ValueError, OSError)): material.files(self.data, expected=self.expected)
                file.write_bytes(original)
                file.chmod(mode)

    def test_declared_material_cannot_follow_a_leaf_or_parent_link(self):
        outside = self.root / "outside"
        outside.write_bytes(b"alpha")
        file = self.data / "a"
        file.unlink()
        file.symlink_to(outside)
        with self.assertRaisesRegex(ValueError, "symlink"): material.files(self.data, expected=self.expected)
        file.unlink()
        file.write_bytes(b"alpha")
        nested = self.data / "nested"
        nested.rename(self.root / "elsewhere")
        nested.symlink_to(self.root / "elsewhere", target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlink"): material.files(self.data, expected=self.expected)


if __name__ == "__main__":
    unittest.main(verbosity=2)
