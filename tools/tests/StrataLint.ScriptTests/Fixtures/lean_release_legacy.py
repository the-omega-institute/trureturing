"""Obsolete Release names never enter the current cache download path."""
import json
import shutil


class ReleaseLegacyCases:
    def test_old_release_names_are_not_selected_or_downloaded(self):
        # REL1-4: old names omit the report key; there is no compatibility read.
        shutil.rmtree(self.root / ".lake/build")
        old = ["lean-cache-v1-toolchain-" + "a" * 16 + "-" + "b" * 16,
               "lean-cache-v2-" + "f" * 40 + "-linux-arm64-123-1"]
        releases = [dict(tagName=tag, createdAt="9", isDraft=False) for tag in old]
        log = self.root / "old-name-gh-calls"
        result = self.transport("fetch", FAKE_LIST_JSON=json.dumps(releases), FAKE_GH_LOG=str(log))
        self.assertEqual(1, result.returncode, result.stdout + result.stderr)
        self.assertFalse((self.root / ".lake/build").exists())
        self.assertEqual([["release", "list", "--repo", "the-omega-institute/trureturing", "--limit", "100",
                           "--json", "tagName,createdAt,isDraft"]],
                         [json.loads(line) for line in log.read_text().splitlines()])
