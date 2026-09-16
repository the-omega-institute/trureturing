"""Release transport behavior contracts using private local fixtures."""
import os
import shutil
import unittest

from lean_seed_support import INPUT, OTHER, PUBLISH, REV, ROOT, PartitionFixture, digest, write
from lean_seed_transport import FAKE_GH, ReleaseTransportCases
from cache_deadline_cases import CacheDeadlineCases
from lean_release_verification import ReleaseVerificationCases
from lean_release_legacy import ReleaseLegacyCases


class TransportTests(ReleaseLegacyCases, ReleaseVerificationCases, CacheDeadlineCases, ReleaseTransportCases, unittest.TestCase):
    """Release transport cases exposed under their existing test identity."""

    def test_transition_fetch_flag_cannot_widen_partition_compatibility(self):
        self.assertEqual(0, self.transport("publish").returncode)
        shutil.rmtree(self.root / ".lake/build")
        self.manifest["packages"][0]["rev"] = OTHER
        self.save_manifest()
        missed = self.transport("fetch", arguments=("--allow-seed",))
        self.assertEqual(1, missed.returncode, missed.stdout + missed.stderr)
        self.assertIn('"status":"miss"', missed.stdout)
        self.assertFalse((self.root / ".lake/build").exists())
        self.manifest["packages"][0]["rev"] = REV
        self.save_manifest()
        restored = self.transport("fetch", arguments=("--allow-seed",))
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        self.assertEqual("locally-produced-olean", (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())


    def test_malformed_cleanup_metadata_cannot_fail_or_repeat_the_build(self):
        calls = self.root / "build-calls"
        write(self.bin / "make", '#!/bin/sh\necho build >> "$FAKE_BUILD_CALLS"\nexit 0\n')
        malformed = [("FAKE_LIST_JSON", '["invalid"]'),
                     ("FAKE_LIST_JSON", '[{"tagName":12,"createdAt":"today","isDraft":false}]'),
                     ("FAKE_FAIL", "list")]
        for index, (field, value) in enumerate(malformed):
            result = self.transport("publish", str(601 + index), FAKE_BUILD_CALLS=str(calls), **{field: value})
            self.assertEqual(0, result.returncode, result.stdout + result.stderr)
            self.assertIn('"status":"published"', result.stdout)
            self.assertIn('"prune_error":', result.stdout)
        self.assertEqual(["build"] * len(malformed), calls.read_text().splitlines())

    def test_publication_requires_a_current_inspector_report(self):
        write(self.bin / "make", '#!/bin/sh\nexit 0\n')
        report = self.root / ".lake/build/stratalint/raw-lean-report.json"
        report.unlink()
        missing = self.transport("publish")
        self.assertEqual(0, missing.returncode, missing.stdout + missing.stderr)
        self.assertIn('"status":"failed"', missing.stdout.replace(" ", ""))
        self.assertIn("current Inspector report is missing", missing.stdout)
        self.assertEqual([], list(self.remote.iterdir()))

        write(self.bin / "make", '#!/bin/sh\nmkdir -p .lake/build/stratalint\nprintf \'%s\\n\' \'{"modules":[],"schema":"wrong"}\' > .lake/build/stratalint/raw-lean-report.json\nexit 0\n')
        malformed = self.transport("publish")
        self.assertEqual(0, malformed.returncode, malformed.stdout + malformed.stderr)
        self.assertIn('"status":"failed"', malformed.stdout.replace(" ", ""))
        self.assertIn("current Inspector report is malformed", malformed.stdout)
        self.assertEqual([], list(self.remote.iterdir()))


if __name__ == "__main__":
    unittest.main()
