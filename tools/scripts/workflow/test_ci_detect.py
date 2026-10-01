"""Change detection against synthetic unit specifications and changed-path lists."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("ci_detect.py")


class CiDetectTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="ci detect ")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.changed = self.root / "changed paths"
        self.output = self.root / "github output"

    def detect(self, spec, paths=None):
        if paths is not None:
            self.changed.write_bytes(b"".join(path.encode() + b"\0" for path in paths))
        self.output.write_text("")
        env = {key: value for key, value in os.environ.items() if key not in ("CI_UNITS", "GITHUB_OUTPUT")}
        env.update(CI_UNITS=spec, GITHUB_OUTPUT=str(self.output))
        return subprocess.run([sys.executable, str(SCRIPT), "--changed", str(self.changed)],
                              cwd=tempfile.gettempdir(), env=env, capture_output=True, text=True)

    def hits(self, result):
        self.assertEqual(result.returncode, 0, result.stderr)
        lines = self.output.read_text().splitlines()
        self.assertEqual(len(lines), 1, lines)
        key, _, value = lines[0].partition("=")
        self.assertEqual(key, "hits")
        return json.loads(value)

    def assert_error(self, result, message):
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn("CI_DETECT_ERROR", result.stderr)
        self.assertIn(message, result.stderr)
        self.assertEqual(self.output.read_text(), "")

    def test_each_unit_hits_only_on_its_own_patterns(self):
        spec = "[alpha]\nsrc/a/*\n[beta]\nsrc/b/*.cs\n[gamma]\ndocs/*\n"
        hits = self.hits(self.detect(spec, ["src/a/x/y.txt", "src/b/z.cs"]))
        self.assertEqual(hits, {"alpha": True, "beta": True, "gamma": False})
        self.assertEqual(list(hits), ["alpha", "beta", "gamma"])

    def test_star_crosses_directories_and_question_mark_is_one_character(self):
        spec = "[deep]\ntools/*.py\n[one]\na?c\n"
        self.assertEqual(self.hits(self.detect(spec, ["tools/x/y/z.py"])), {"deep": True, "one": False})
        self.assertEqual(self.hits(self.detect(spec, ["abc"])), {"deep": False, "one": True})
        self.assertEqual(self.hits(self.detect(spec, ["abbc"])), {"deep": False, "one": False})

    def test_patterns_match_the_whole_path(self):
        spec = "[exact]\nMakefile\n"
        self.assertEqual(self.hits(self.detect(spec, ["tools/Makefile"])), {"exact": False})
        self.assertEqual(self.hits(self.detect(spec, ["Makefile.bak"])), {"exact": False})
        self.assertEqual(self.hits(self.detect(spec, ["Makefile"])), {"exact": True})

    def test_dots_and_plus_are_literal(self):
        spec = "[literal]\na.b+c\n"
        self.assertEqual(self.hits(self.detect(spec, ["aXb+c"])), {"literal": False})
        self.assertEqual(self.hits(self.detect(spec, ["a.bbc"])), {"literal": False})
        self.assertEqual(self.hits(self.detect(spec, ["a.b+c"])), {"literal": True})

    def test_exclusions_remove_paths_from_their_own_unit_only(self):
        spec = "[all]\n*\n!docs/*\n[docs]\ndocs/*\n"
        self.assertEqual(self.hits(self.detect(spec, ["docs/a.md"])), {"all": False, "docs": True})
        self.assertEqual(self.hits(self.detect(spec, ["docs/a.md", "src/x"])), {"all": True, "docs": True})

    def test_shared_section_applies_to_every_unit(self):
        spec = "[*]\nglobal.json\n[alpha]\nsrc/a/*\n[beta]\nsrc/b/*\n"
        self.assertEqual(self.hits(self.detect(spec, ["global.json"])), {"alpha": True, "beta": True})
        self.assertEqual(self.hits(self.detect(spec, ["src/b/x"])), {"alpha": False, "beta": True})

    def test_unit_exclusions_also_filter_shared_patterns(self):
        spec = "[*]\nshared/*\n[alpha]\nsrc/*\n!shared/skip\n[beta]\nsrc/*\n"
        self.assertEqual(self.hits(self.detect(spec, ["shared/skip"])), {"alpha": False, "beta": True})

    def test_comments_and_blank_lines_are_ignored(self):
        spec = "# heading\n\n[alpha]\n  # note\n  src/*  \n\n"
        self.assertEqual(self.hits(self.detect(spec, ["src/x"])), {"alpha": True})

    def test_missing_changed_list_hits_every_unit(self):
        result = self.detect("[alpha]\nsrc/*\n[beta]\ndocs/*\n")
        self.assertEqual(self.hits(result), {"alpha": True, "beta": True})
        self.assertIn("no base commit", result.stdout)

    def test_empty_change_hits_nothing(self):
        self.assertEqual(self.hits(self.detect("[alpha]\n*\n", [])), {"alpha": False})

    def test_three_thousand_changed_paths_are_accepted(self):
        paths = [f"src/{index}" for index in range(3000)]
        self.assertEqual(self.hits(self.detect("[alpha]\nsrc/*\n", paths)), {"alpha": True})

    def test_more_than_three_thousand_changed_paths_fail(self):
        paths = [f"src/{index}" for index in range(3001)]
        self.assert_error(self.detect("[alpha]\nsrc/*\n", paths), "3001 changed paths exceed 3000")

    def test_log_names_the_first_matching_path_and_pattern(self):
        result = self.detect("[alpha]\nsrc/*\n[beta]\ndocs/*\n", ["src/x", "src/y"])
        self.assertIn("CI_DETECT unit=alpha hit=true path=src/x pattern=src/*", result.stdout)
        self.assertIn("CI_DETECT unit=beta hit=false", result.stdout)

    def test_malformed_specifications_fail(self):
        cases = {
            "": "no unit",
            "[*]\nshared\n": "no unit",
            "src/*\n[alpha]\nx\n": "before the first section",
            "[alpha]\nx\n[alpha]\ny\n": "duplicate section [alpha]",
            "[*]\nx\n[*]\ny\n[alpha]\nz\n": "duplicate section [*]",
            "[Alpha]\nx\n": "invalid section",
            "[al_pha]\nx\n": "invalid section",
            "[alpha]\n": "no including pattern",
            "[alpha]\n!x\n": "no including pattern",
            "[*]\n!x\n[alpha]\ny\n": "shared section cannot exclude",
            "[alpha]\nx\nx\n": "duplicate pattern",
            "[alpha]\n!\n": "invalid pattern",
            "[alpha]\nsrc/[ab]\n": "unsupported pattern syntax",
            "[alpha]\nsrc/{a,b}\n": "unsupported pattern syntax",
            "[alpha]\nsrc\\a\n": "unsupported pattern syntax",
            "[alpha]\nsrc/@(a)\n": "unsupported pattern syntax",
            "[alpha]\nsrc/a|b\n": "unsupported pattern syntax",
        }
        for spec, message in cases.items():
            with self.subTest(spec=spec):
                self.assert_error(self.detect(spec, ["src/x"]), message)

    def test_missing_environment_fails(self):
        env = {key: value for key, value in os.environ.items() if key not in ("CI_UNITS", "GITHUB_OUTPUT")}
        self.changed.write_bytes(b"")
        for missing in ("CI_UNITS", "GITHUB_OUTPUT"):
            with self.subTest(missing=missing):
                present = dict(env, CI_UNITS="[alpha]\nx\n", GITHUB_OUTPUT=str(self.output))
                del present[missing]
                result = subprocess.run([sys.executable, str(SCRIPT), "--changed", str(self.changed)],
                                        env=present, capture_output=True, text=True)
                self.assertEqual(result.returncode, 2)
                self.assertIn(missing, result.stderr)

    def test_unreadable_changed_list_fails(self):
        self.changed.mkdir()
        self.assert_error(self.detect("[alpha]\nx\n"), "cannot read")

    def test_changed_list_must_be_nul_terminated(self):
        self.changed.write_bytes(b"src/x")
        self.assert_error(self.detect("[alpha]\nsrc/*\n"), "NUL-terminated")


if __name__ == "__main__":
    unittest.main()
