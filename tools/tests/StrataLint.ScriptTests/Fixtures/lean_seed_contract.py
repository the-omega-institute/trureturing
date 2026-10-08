"""Release transport behavior contracts using private local fixtures."""
import json
import hashlib
import os
import platform
import shutil
import unittest

from lean_seed_support import INPUT, OTHER, PUBLISH, REV, ROOT, PartitionFixture, digest, write
from lean_seed_transport import FAKE_GH, ReleaseTransportCases
from lean_release_verification import ReleaseVerificationCases
from lean_release_legacy import ReleaseLegacyCases


class TransportTests(ReleaseLegacyCases, ReleaseVerificationCases, ReleaseTransportCases, unittest.TestCase):
    """Release transport cases exposed under their existing test identity."""

    def test_release_key_derives_format_and_explicit_execution_only(self):
        # REL1-1: partition-only names do not distinguish report format/environment.
        address = json.loads(self.transport("address").stdout)
        system, machine = platform.system().lower(), platform.machine().lower()
        machine = {"aarch64": "arm64", "x86_64": "x64", "amd64": "x64"}.get(machine, machine)
        host = system + "-" + machine
        family = "darwin-arm64+linux-arm64" if host in ("darwin-arm64", "linux-arm64") else host
        execution = dict(toolchain=digest((self.root / "lean-toolchain").read_bytes()),
            tools=["lake", "lean"], platform=family,
            environment={name: "" for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "ELAN_TOOLCHAIN", "LEAN_OPTS")})
        expected = hashlib.sha256(json.dumps(execution, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        self.assertEqual(dict(report_format="stratalint-raw-lean-report-v3", execution_sha256=expected), address["cache_key"])
        self.assertEqual(f"lean-cache-v2-{REV}-{host}-report-stratalint-raw-lean-report-v3-env-{expected[:12]}-",
                         address["release_prefix"])
        write(self.root / "D5/A.lean", "def a := 333\n")
        self.assertEqual(address, json.loads(self.transport("address").stdout))
        owner = self.publisher.with_name("lean_cache_release.py")
        write(owner, owner.read_text() + "\n# implementation-only variation\n")
        self.assertEqual(address, json.loads(self.transport("address").stdout))
        write(self.root / "lean-toolchain", "leanprover/lean4:v4.34.0\n")
        self.assertNotEqual(address["cache_key"], json.loads(self.transport("address").stdout)["cache_key"])
        changed = self.transport("address", ELAN_TOOLCHAIN="other-toolchain")
        self.assertNotEqual(expected, json.loads(changed.stdout)["cache_key"]["execution_sha256"])
        selection = self.root / "tools/scripts/report/lean-report-selection.py"
        write(selection, selection.read_text().replace("stratalint-raw-lean-report-v3", "stratalint-raw-lean-report-test"))
        changed = json.loads(self.transport("address").stdout)
        self.assertEqual("stratalint-raw-lean-report-test", changed["cache_key"]["report_format"])
        self.assertIn("-report-stratalint-raw-lean-report-test-env-", changed["release_prefix"])

    def test_mismatched_key_is_never_selected_or_downloaded(self):
        # REL1-2: newest-first partition selection previously downloaded mismatched reports.
        published = self.transport("publish")
        self.assertIn('"status":"published"', published.stdout)
        original = next(self.remote.iterdir()).name
        shutil.rmtree(self.root / ".lake/build")
        address = json.loads(self.transport("address").stdout)
        wrong = [original.replace(address["cache_key"]["report_format"], "wrong-format"),
                 original.replace(address["cache_key"]["execution_sha256"][:12], "0" * 12),
                 f"lean-cache-v2-{REV}-linux-arm64-123-1"]
        releases = [dict(tagName=tag, createdAt=f"9{index}", isDraft=False) for index, tag in enumerate(wrong)]
        log = self.root / "key-gh-calls"
        missed = self.transport("fetch", FAKE_LIST_JSON=json.dumps(releases), FAKE_GH_LOG=str(log))
        self.assertEqual(1, missed.returncode, missed.stdout + missed.stderr)
        self.assertEqual(["list"], [json.loads(line)[1] for line in log.read_text().splitlines()])
        releases.append(dict(tagName=original, createdAt="1", isDraft=False))
        log.unlink()
        restored = self.transport("fetch", FAKE_LIST_JSON=json.dumps(releases), FAKE_GH_LOG=str(log))
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        calls = [json.loads(line) for line in log.read_text().splitlines()]
        self.assertTrue(all(tag not in call for tag in wrong for call in calls[1:]))
        self.assertIn(original, restored.stdout)

    def test_publication_requires_current_report_before_transport(self):
        result = self.transport("publish")
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertEqual(["lean-report LEAN_REPORT=.lake/build/stratalint/raw-lean-report.json"], (self.root / "build-runs").read_text().splitlines())

    def test_fetch_cannot_widen_partition_compatibility(self):
        self.assertEqual(0, self.transport("publish").returncode)
        shutil.rmtree(self.root / ".lake/build")
        self.manifest["packages"][0]["rev"] = OTHER
        self.save_manifest()
        missed = self.transport("fetch")
        self.assertEqual(1, missed.returncode, missed.stdout + missed.stderr)
        self.assertIn('"status":"miss"', missed.stdout)
        self.assertFalse((self.root / ".lake/build").exists())
        self.manifest["packages"][0]["rev"] = REV
        self.save_manifest()
        restored = self.transport("fetch")
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

    def host_platform(self, system, machine):
        # Seed compatibility follows the host that runs the transport.
        write(self.bin / "sitecustomize.py", "import os, platform\n"
              "platform.system = lambda: os.environ['FAKE_PLATFORM_SYSTEM']\n"
              "platform.machine = lambda: os.environ['FAKE_PLATFORM_MACHINE']\n")
        return {"PYTHONPATH": str(self.bin), "FAKE_PLATFORM_SYSTEM": system, "FAKE_PLATFORM_MACHINE": machine}

    def test_arm64_seeds_are_shared_between_linux_and_macos_only(self):
        seed = "locally-produced-olean"
        for publisher, fetcher, run in [(("Linux", "aarch64"), ("Darwin", "arm64"), "123"),
                                        (("Darwin", "arm64"), ("Linux", "aarch64"), "124")]:
            with self.subTest(publisher=publisher, fetcher=fetcher):
                shutil.rmtree(self.remote)
                self.remote.mkdir()
                write(self.root / ".lake/build/lib/lean/D5/A.olean", seed)
                published = self.transport("publish", run, **self.host_platform(*publisher))
                self.assertEqual(0, published.returncode, published.stdout + published.stderr)
                self.assertIn('"status":"published"', published.stdout)
                tag = next(self.remote.iterdir()).name
                # Publication keeps its own platform partition and retention.
                own = "linux-arm64" if publisher[0] == "Linux" else "darwin-arm64"
                self.assertEqual(json.loads(self.transport("address", **self.host_platform(*publisher)).stdout)["release_prefix"] + f"ci-{run}-1", tag)
                shutil.rmtree(self.root / ".lake/build")
                for other in [("Darwin", "x86_64"), ("Linux", "x86_64")]:
                    missed = self.transport("fetch", **self.host_platform(*other))
                    self.assertEqual(1, missed.returncode, missed.stdout + missed.stderr)
                    self.assertIn('"status":"miss"', missed.stdout)
                    self.assertFalse((self.root / ".lake/build").exists())
                restored = self.transport("fetch", **self.host_platform(*fetcher))
                self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
                self.assertIn(f'"resolved":"{tag}"', restored.stdout)
                self.assertIn(f'"partition":"{REV}/{own}"', restored.stdout)
                self.assertEqual(seed, (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())


if __name__ == "__main__":
    unittest.main()
