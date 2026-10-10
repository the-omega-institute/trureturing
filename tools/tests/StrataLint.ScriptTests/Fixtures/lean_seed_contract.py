"""Release transport behavior contracts using private local fixtures."""
import json
import hashlib
import os
import platform
import subprocess
import datetime
import shutil
import unittest

from lean_seed_support import INPUT, OTHER, PUBLISH, REV, ROOT, PartitionFixture, digest, write
from lean_seed_transport import FAKE_GH, ReleaseTransportCases
from lean_release_verification import ReleaseVerificationCases
from lean_release_legacy import ReleaseLegacyCases


class TransportTests(ReleaseLegacyCases, ReleaseVerificationCases, ReleaseTransportCases, unittest.TestCase):
    """Release transport cases exposed under their existing test identity."""

    def local_environment(self, **changes):
        return dict(GITHUB_ACTIONS="false", GITHUB_EVENT_NAME="", GITHUB_REF="", GITHUB_REPOSITORY="",
                    GITHUB_SHA="not-an-input", GITHUB_RUN_ID="", GITHUB_RUN_ATTEMPT="", **changes)

    def test_local_make_publication_and_restore_use_current_protected_head(self):
        # Local make callers publish clean protected-dev snapshots with UTC suffixes.
        before = datetime.datetime.now(datetime.timezone.utc)
        result = subprocess.run([shutil.which("make"), "-C", str(self.root), "lean-cache-to-github-without-mathlib"],
            text=True, capture_output=True, env=self.transport_environment(**self.local_environment(),
                FAKE_GH_LOG=str(self.root / "local-gh-calls")))
        after = datetime.datetime.now(datetime.timezone.utc)
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"published"', result.stdout)
        snapshot = next(self.remote.iterdir())
        prefix = json.loads(self.transport("address").stdout)["release_prefix"]
        suffix = snapshot.name.removeprefix(prefix)
        self.assertRegex(suffix, r"^local-" + self.producer_commit[:12] + r"-[0-9]{8}T[0-9]{12}Z$")
        stamp = suffix.split("-")[-1]
        published_at = datetime.datetime.strptime(stamp, "%Y%m%dT%H%M%S%fZ").replace(tzinfo=datetime.timezone.utc)
        self.assertLessEqual(before, published_at)
        self.assertLessEqual(published_at, after)
        manifest = json.loads((snapshot / "manifest.json").read_text())
        self.assertEqual(self.producer_commit, manifest["producer_commit_sha"])
        self.assertEqual(suffix, manifest["publication_id"])
        self.assertNotIn("workflow_run_id", manifest)
        calls = [json.loads(line) for line in (self.root / "local-gh-calls").read_text().splitlines()]
        self.assertFalse(any(call[0] == "api" and "/actions/" in call[1] for call in calls))
        second = self.transport("publish", **self.local_environment())
        self.assertIn('"status":"published"', second.stdout)
        self.assertEqual(2, len(list(self.remote.iterdir())))
        shutil.rmtree(self.root / ".lake/build")
        restored = self.transport("fetch", **self.local_environment())
        self.assertEqual(0, restored.returncode, restored.stdout + restored.stderr)
        self.assertEqual("locally-produced-olean", (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())

    def test_local_publication_rejects_dirty_unprotected_and_non_dev_content(self):
        # Publication requires clean content from the protected dev history.
        for change in ("tracked", "untracked", "unprotected", "off-dev"):
            with self.subTest(change=change):
                environment = self.local_environment()
                if change == "tracked":
                    write(self.root / "D5/A.lean", "def a := 2\n")
                elif change == "untracked":
                    write(self.root / "untracked-input.lean", "def missing := 1\n")
                elif change == "unprotected":
                    environment["FAKE_DEV_BRANCH"] = json.dumps(dict(name="dev", protected=False, commit=dict(sha=self.producer_commit)))
                else:
                    environment["FAKE_DEV_COMPARE"] = json.dumps(dict(status="diverged", merge_base_commit=dict(sha="f" * 40)))
                result = self.transport("publish", **environment)
                self.assertNotEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertIn('"status":"failed"', result.stdout)
                self.assertEqual([], list(self.remote.iterdir()))
                write(self.root / "D5/A.lean", "def a := 1\n")
                (self.root / "untracked-input.lean").unlink(missing_ok=True)

    def test_local_publication_requires_complete_strict_current_report(self):
        # Publication requires a complete canonical bundle and current sealed inputs.
        report = self.root / ".lake/build/stratalint/raw-lean-report.json"
        originals = {path: path.read_bytes() for path in report.parent.iterdir()}
        for damage in ("missing", "empty-modules", "unknown-field", "noncanonical", "materials", "receipt", "stale"):
            with self.subTest(damage=damage):
                for path, content in originals.items(): path.write_bytes(content)
                environment = self.local_environment(FAKE_REPORT_PRESERVE="1")
                if damage == "missing": report.unlink()
                elif damage in ("empty-modules", "unknown-field", "noncanonical"):
                    data = json.loads(report.read_text())
                    if damage == "empty-modules": data["modules"] = []
                    if damage == "unknown-field": data["unknown"] = True
                    report.write_text((" " if damage == "noncanonical" else "") + json.dumps(data) + "\n")
                    # Keep the integrity seal consistent so the strict row reader, not only the hash guard, rejects it.
                    current_sha = digest(report.read_bytes())
                    report.with_name(report.name + ".sha256").write_text(current_sha + "  " + report.name + "\n")
                    provenance_path = report.with_name(report.name + ".provenance.json")
                    provenance = json.loads(provenance_path.read_text())
                    old_sha = provenance["report_sha256"]
                    provenance["report_sha256"] = current_sha
                    provenance_path.write_text(json.dumps(provenance) + "\n")
                    attestation = report.with_name(report.name + ".input.attestation")
                    attestation.write_text(attestation.read_text().replace(old_sha, current_sha))
                    receipt_path = report.with_name(report.name + ".reuse.json")
                    seal = json.loads(receipt_path.read_text())
                    seal["bundle"] = {suffix: digest(report.with_name(report.name + suffix).read_bytes()) for suffix in seal["bundle"]}
                    receipt_path.write_text(json.dumps(seal) + "\n")
                elif damage == "materials":
                    report.with_name(report.name + ".materials.zip").write_bytes(b"not-a-zip")
                elif damage == "receipt":
                    report.with_name(report.name + ".reuse.json").unlink()
                else:
                    write(self.root / "D5/A.lean", "def a := 2\n")
                    self.commit_fixture()
                result = self.transport("publish", **environment)
                self.assertNotEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertIn('"status":"failed"', result.stdout)
                self.assertEqual([], list(self.remote.iterdir()))

    def test_ci_fetch_never_reads_release_even_when_actions_seed_is_absent(self):
        # CI's ensure fallback must skip Release independently of workflow steps.
        self.assertIn('"status":"published"', self.transport("publish").stdout)
        shutil.rmtree(self.root / ".lake/build")
        log = self.root / "ci-gh-calls"
        result = self.transport("fetch", GITHUB_ACTIONS="true", FAKE_GH_LOG=str(log))
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"status":"skipped"', result.stdout)
        self.assertFalse(log.exists())
        self.assertFalse((self.root / ".lake/build").exists())

    def test_manifest_full_key_mismatch_stops_before_archive_download(self):
        # Full digest validation guards the shortened name before archive transfer.
        self.assertIn('"status":"published"', self.transport("publish").stdout)
        snapshot = next(self.remote.iterdir())
        manifest = json.loads((snapshot / "manifest.json").read_text())
        manifest["cache_key"]["execution_sha256"] = manifest["cache_key"]["execution_sha256"][:12] + "0" * 52
        write(snapshot / "manifest.json", json.dumps(manifest))
        shutil.rmtree(self.root / ".lake/build")
        log = self.root / "manifest-key-calls"
        result = self.transport("fetch", FAKE_GH_LOG=str(log))
        self.assertEqual(1, result.returncode, result.stdout + result.stderr)
        downloads = [json.loads(line) for line in log.read_text().splitlines() if json.loads(line)[:2] == ["release", "download"]]
        self.assertEqual(1, len(downloads))
        self.assertEqual("manifest.json", downloads[0][-1])
        self.assertFalse((self.root / ".lake/build").exists())

    def test_release_key_derives_format_and_explicit_execution_only(self):
        # Names project only the declared format and explicit execution inputs.
        address = json.loads(self.transport("address").stdout)
        system, machine = platform.system().lower(), platform.machine().lower()
        machine = {"aarch64": "arm64", "x86_64": "x64", "amd64": "x64"}.get(machine, machine)
        host = system + "-" + machine
        family = "darwin-arm64+linux-arm64" if host in ("darwin-arm64", "linux-arm64") else host
        execution = dict(toolchain=(self.root / "lean-toolchain").read_text().strip(),
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
        write(self.root / "lean-toolchain", "leanprover/lean4:v4.33.0\n\n")
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
        # Selection filters incompatible names before any snapshot request.
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
        self.assertEqual(["lean-report LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build LEAN_REPORT=.lake/build/stratalint/raw-lean-report.json"], (self.root / "build-runs").read_text().splitlines())

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
        self.assertEqual(2, missing.returncode, missing.stdout + missing.stderr)
        self.assertIn('"status":"failed"', missing.stdout.replace(" ", ""))
        self.assertIn("missing bundle member: raw-lean-report.json", missing.stdout)
        self.assertEqual([], list(self.remote.iterdir()))

        write(self.bin / "make", '#!/bin/sh\nmkdir -p .lake/build/stratalint\nprintf \'%s\\n\' \'{"modules":[],"schema":"wrong"}\' > .lake/build/stratalint/raw-lean-report.json\nexit 0\n')
        malformed = self.transport("publish")
        self.assertEqual(2, malformed.returncode, malformed.stdout + malformed.stderr)
        self.assertIn('"status":"failed"', malformed.stdout.replace(" ", ""))
        self.assertIn("reuse receipt bundle mismatch", malformed.stdout)
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
