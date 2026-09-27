"""Legacy cache data consumed through the normal Release CLI."""
import base64
import hashlib
import io
import json
import shutil
import tarfile

from lean_seed_support import OTHER, REV, digest, write


class ReleaseLegacyCases:
    def legacy_fixture(self, parts=2, members=None, report_snapshot=False):
        tag = "lean-cache-v1-unrelated-toolchain-v0-" + "a" * 16 + "-" + "b" * 16
        if report_snapshot:
            tag += "-" + "e" * 16
        snapshot = self.remote / tag
        snapshot.mkdir()
        partition = json.loads(self.transport("address").stdout)["partition"]
        system, machine = partition.split("/")[1].split("-", 1)
        stream = io.BytesIO()
        with tarfile.open(fileobj=stream, mode="w:gz") as archive:
            if members is None:
                archive.add(self.root / ".lake/build", arcname=".")
            else:
                for name, kind in members:
                    member = tarfile.TarInfo(name)
                    member.type, member.linkname = kind, "outside" if kind in (tarfile.SYMTYPE, tarfile.LNKTYPE) else ""
                    archive.addfile(member)
        packed = stream.getvalue()
        self.legacy_manifest = {"tag": tag, "toolchain": "unrelated/toolchain:v0", "os": system,
            "arch": {"arm64": "aarch64", "x64": "x86_64"}.get(machine, machine),
            "config_sha256": "a" * 64, "sources_sha256": "b" * 64, "asset": "lean-build.tgz",
            "archive_sha256": digest(packed), "archive_bytes": str(len(packed)), "parts": str(parts),
            "producer_commit_sha": "c" * 40, "workflow_run_id": "321"}
        if report_snapshot:
            self.legacy_manifest["build_snapshot_sha256"] = "e" * 64
        for index in range(parts):
            payload = packed[index * len(packed) // parts:(index + 1) * len(packed) // parts]
            name = "lean-build.tgz" if parts == 1 else f"lean-build.tgz.part-{index:02d}"
            (snapshot / name).write_bytes(payload)
            if parts > 1:
                self.legacy_manifest[f"part_sha256_{index}"] = digest(payload)
        self.legacy_snapshot = snapshot
        self.save_legacy_manifest()
        write(snapshot / "release.json", json.dumps({"tag_name": tag, "draft": False,
            "target_commitish": "c" * 40, "published_at": "2026-09-14T12:00:00Z"}))
        repo = "the-omega-institute/trureturing"
        self.legacy_run_api = f"repos/{repo}/actions/runs/321"
        self.legacy_source_api = f"repos/{repo}/contents/lake-manifest.json?ref=" + "c" * 40
        content = json.dumps(self.manifest).encode()
        self.legacy_api = {
            self.legacy_run_api: {"id": 321, "run_attempt": 2, "event": "schedule", "head_branch": "dev",
                "head_sha": "c" * 40, "path": ".github/workflows/lean-cache-publish.yml", "status": "completed",
                "conclusion": "success", "repository": {"full_name": repo}},
            self.legacy_source_api: {"type": "file", "path": "lake-manifest.json", "encoding": "base64",
                "content": base64.b64encode(content).decode(), "size": len(content),
                "sha": hashlib.sha1(b"blob " + str(len(content)).encode() + b"\0" + content).hexdigest()}}
        shutil.rmtree(self.root / ".lake/build")
        return tag

    def save_legacy_manifest(self):
        write(self.legacy_snapshot / "manifest.txt", "".join(f"{key}={value}\n" for key, value in self.legacy_manifest.items()))

    def legacy_fetch(self, **environment):
        write(self.root / "legacy-api.json", json.dumps(self.legacy_api))
        return self.transport("fetch", FAKE_VERIFICATION_API=str(self.root / "legacy-api.json"),
            FAKE_GH_LOG=str(self.root / "legacy-gh-calls"), **environment)

    def test_legacy_report_snapshot_restores_as_same_partition_seed(self):
        tag = self.legacy_fixture(report_snapshot=True)
        result = self.legacy_fetch()
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn('"mode":"partition"', result.stdout)
        self.assertIn('"resolved":"' + tag + '"', result.stdout)
        self.assertEqual("locally-produced-olean", (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())
        self.assertFalse((self.root / "build-runs").exists())

    def test_legacy_report_snapshot_requires_its_declared_address(self):
        self.legacy_fixture(report_snapshot=True)
        for value in (None, "invalid", "f" * 64):
            with self.subTest(snapshot=value):
                if value is None:
                    self.legacy_manifest.pop("build_snapshot_sha256", None)
                else:
                    self.legacy_manifest["build_snapshot_sha256"] = value
                self.save_legacy_manifest()
                result = self.legacy_fetch()
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                self.assertFalse((self.root / ".lake/build").exists())

    def test_legacy_seed_uses_resolved_mathlib_and_platform_only_without_repack(self):
        tag = self.legacy_fixture()
        result = self.legacy_fetch(**self.installation_probe())
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertIn(tag, result.stdout)
        self.assertEqual("locally-produced-olean", (self.root / ".lake/build/lib/lean/D5/A.olean").read_text())
        self.assertFalse((self.root / "build-runs").exists())
        self.assertFalse((self.root / ".lake/report-cache").exists())
        self.assertNotIn("workflow_run_attempt", result.stdout, "legacy archive does not identify its producing attempt")
        events = self.installation_events()
        self.assertFalse(any(event["operation"] == "copytree" for event in events))
        material = next(event for event in events if event["operation"] == "material")
        status = (self.root / ".lake/build/lib/lean/D5/A.olean").stat()
        self.assertEqual((material["device"], material["inode"]), (status.st_dev, status.st_ino))

    def test_legacy_and_current_seeds_share_one_newest_first_selection(self):
        self.assertEqual(0, self.transport("publish").returncode)
        current = next(self.remote.iterdir()).name
        legacy = self.legacy_fixture(parts=1)
        for newest, older in ((legacy, current), (current, legacy)):
            with self.subTest(newest=newest):
                order = [{"tagName": tag, "createdAt": stamp, "isDraft": False}
                         for tag, stamp in ((newest, "2026-09-14T12:00:00Z"), (older, "2026-09-13T12:00:00Z"))]
                (self.root / "legacy-gh-calls").unlink(missing_ok=True)
                result = self.legacy_fetch(FAKE_LIST_JSON=json.dumps(order))
                self.assertEqual(0, result.returncode, result.stdout + result.stderr)
                self.assertIn('"resolved":"' + newest + '"', result.stdout)
                calls = [json.loads(line) for line in (self.root / "legacy-gh-calls").read_text().splitlines()]
                if newest == current:
                    self.assertFalse(any(call[:2] == ["api", self.legacy_run_api] for call in calls))
                    self.assertFalse(any(call[:2] == ["api", self.legacy_source_api] for call in calls))
                shutil.rmtree(self.root / ".lake/build")

    def test_legacy_requires_matching_partition_and_attributable_successful_producer(self):
        self.legacy_fixture()
        metadata = json.loads((self.legacy_snapshot / "release.json").read_text())
        for record, field, value in [
            (self.legacy_manifest, "os", "other"), (self.legacy_manifest, "arch", "other"),
            (self.legacy_manifest, "producer_commit_sha", "latest"), (self.legacy_manifest, "workflow_run_id", "0"),
            (metadata, "draft", True), (metadata, "target_commitish", "e" * 40), (metadata, "published_at", None),
            (self.legacy_api[self.legacy_run_api], "id", 999),
            (self.legacy_api[self.legacy_run_api], "event", "push"),
            (self.legacy_api[self.legacy_run_api], "head_branch", "integration-fixture"),
            (self.legacy_api[self.legacy_run_api], "head_sha", "e" * 40),
            (self.legacy_api[self.legacy_run_api], "path", ".github/workflows/other.yml"),
            (self.legacy_api[self.legacy_run_api], "repository", {"full_name": "other/repo"}),
            (self.legacy_api[self.legacy_run_api], "status", "in_progress"),
            (self.legacy_api[self.legacy_run_api], "conclusion", "failure"),
            (self.legacy_api[self.legacy_source_api], "type", "symlink"),
            (self.legacy_api[self.legacy_source_api], "sha", "0" * 40),
            (self.legacy_api[self.legacy_source_api], "content", "missing")]:
            with self.subTest(field=field, value=value):
                before = record[field]
                record[field] = value
                self.save_legacy_manifest()
                write(self.legacy_snapshot / "release.json", json.dumps(metadata))
                result = self.legacy_fetch()
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                self.assertFalse((self.root / ".lake/build").exists())
                record[field] = before
        self.save_legacy_manifest()
        write(self.legacy_snapshot / "release.json", json.dumps(metadata))
        self.manifest["packages"][0]["rev"] = OTHER
        self.save_manifest()
        self.assertEqual(1, self.legacy_fetch().returncode)
        self.assertFalse((self.root / ".lake/build").exists())

    def test_legacy_rejects_damaged_assets_before_installation(self):
        self.legacy_fixture()
        for field, value in (("archive_sha256", "0" * 64), ("archive_bytes", "1"),
                             ("part_sha256_0", "0" * 64), ("parts", "101")):
            with self.subTest(field=field):
                before = self.legacy_manifest[field]
                self.legacy_manifest[field] = value
                self.save_legacy_manifest()
                result = self.legacy_fetch()
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                self.assertFalse((self.root / ".lake/build").exists())
                self.legacy_manifest[field] = before
        self.save_legacy_manifest()
        (self.legacy_snapshot / "lean-build.tgz.part-01").unlink()
        self.assertEqual(1, self.legacy_fetch().returncode)
        self.assertFalse((self.root / ".lake/build").exists())

    def test_legacy_rejects_unsafe_or_duplicate_members_without_staging(self):
        for members in [ [(name, kind)] for name, kind in (("../outside", tarfile.DIRTYPE),
                ("/outside", tarfile.DIRTYPE), ("link", tarfile.SYMTYPE), ("link", tarfile.LNKTYPE)) ] + [
                [("same", tarfile.REGTYPE), ("./same", tarfile.REGTYPE)],
                [("parent", tarfile.REGTYPE), ("parent/child", tarfile.REGTYPE)]]:
            with self.subTest(members=members):
                if hasattr(self, "legacy_snapshot") and self.legacy_snapshot.exists():
                    shutil.rmtree(self.legacy_snapshot)
                if not (self.root / ".lake/build").exists():
                    write(self.root / ".lake/build/lib/lean/D5/A.olean", "locally-produced-olean")
                self.legacy_fixture(members=members)
                result = self.legacy_fetch()
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                self.assertIn("invalid cache member", result.stdout)
                self.assertEqual([], list((self.root / ".lake").iterdir()))
                shutil.rmtree(self.legacy_snapshot)

    def test_legacy_manifest_parser_rejects_ambiguous_missing_and_malformed_fields(self):
        self.legacy_fixture()
        path = self.legacy_snapshot / "manifest.txt"
        original = path.read_text()
        for text in (original + "parts=2\n", original + "not-a-field\n",
                     original.replace("parts=2\n", "parts=1.5\n"),
                     original.replace("parts=2\n", "parts=\n"),
                     original.replace("os=" + self.legacy_manifest["os"] + "\n", ""),
                     original.replace("producer_commit_sha=" + "c" * 40 + "\n", "")):
            with self.subTest(text=text):
                write(path, text)
                result = self.legacy_fetch()
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                self.assertFalse((self.root / ".lake/build").exists())
                self.assertNotIn("Traceback", result.stderr)

    def test_legacy_source_data_uses_the_same_strict_resolved_mathlib_parser(self):
        self.legacy_fixture()
        source = self.legacy_api[self.legacy_source_api]
        for manifest in ({}, {"packages": []}, {"packages": [{"name": "mathlib", "rev": "dev"}]},
                         {"packages": [{"name": "mathlib", "rev": REV}] * 2},
                         {"packages": [{"name": "mathlib", "rev": OTHER}]}):
            with self.subTest(manifest=manifest):
                content = json.dumps(manifest).encode()
                source.update(content=base64.b64encode(content).decode(), size=len(content),
                    sha=hashlib.sha1(b"blob " + str(len(content)).encode() + b"\0" + content).hexdigest())
                result = self.legacy_fetch()
                self.assertEqual(1, result.returncode, result.stdout + result.stderr)
                self.assertFalse((self.root / ".lake/build").exists())

    def test_legacy_truncated_gzip_cannot_install_even_with_matching_transfer_digests(self):
        self.legacy_fixture(parts=1)
        path = self.legacy_snapshot / "lean-build.tgz"
        packed = path.read_bytes()[:-8]
        path.write_bytes(packed)
        self.legacy_manifest.update(archive_bytes=str(len(packed)), archive_sha256=digest(packed))
        self.save_legacy_manifest()
        result = self.legacy_fetch()
        self.assertEqual(1, result.returncode, result.stdout + result.stderr)
        self.assertFalse((self.root / ".lake/build").exists())
        self.assertEqual([], list((self.root / ".lake").iterdir()))
        self.assertNotIn("Traceback", result.stderr)
