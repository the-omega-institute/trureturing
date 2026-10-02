"""Reuse a runnable judge-owned Lean producer or retain the standalone build."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

REPO = Path(__file__).resolve().parents[4]
ENTRY = REPO / 'tools/scripts/workflow/judge-lean-producer.sh'
MESSAGE = 'LEAN_PRODUCER_FAILED expected lean-utility-input, ensure-cache, with-cache-reader or with-cache-writer'


class JudgeProducerContracts(unittest.TestCase):
    def invoke(self, missing=None, runnable=True):
        temp = tempfile.TemporaryDirectory(prefix='judge-producer-contract-')
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        bundle = root / 'judge output'
        bundle.mkdir()
        for suffix in ('dll', 'deps.json', 'runtimeconfig.json'):
            if suffix != missing:
                (bundle / ('StrataLint.Lean.' + suffix)).write_text('fixture')
        dotnet = root / 'dotnet'
        dotnet.write_text("#!/bin/bash\nprintf '%s\\n' '" + (MESSAGE if runnable else 'host failure') + "' >&2\nexit " + ('2' if runnable else '1') + "\n")
        dotnet.chmod(0o755)
        result = subprocess.run(['bash', str(ENTRY), str(bundle)],
                                env=dict(os.environ, PATH=str(root) + os.pathsep + os.environ['PATH']),
                                capture_output=True, text=True)
        return result, bundle

    def test_runnable_cached_or_newly_built_bundle_supplies_absolute_producer(self):
        result, bundle = self.invoke()
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertEqual(str(bundle.resolve() / 'StrataLint.Lean.dll') + '\n', result.stdout)

    def test_missing_or_nonrunnable_bundle_keeps_the_standalone_fallback(self):
        for missing, runnable in (('dll', True), ('deps.json', True), ('runtimeconfig.json', True), (None, False)):
            with self.subTest(missing=missing, runnable=runnable):
                result, _ = self.invoke(missing, runnable)
                self.assertEqual(0, result.returncode, result.stderr)
                self.assertEqual('', result.stdout)
                self.assertIn('JUDGE_LEAN_PRODUCER fallback', result.stderr)

    def test_invalid_selector_invocation_has_distinct_input_failure(self):
        result = subprocess.run(['bash', str(ENTRY)], capture_output=True, text=True)
        self.assertEqual(2, result.returncode, result.stderr)


if __name__ == '__main__':
    unittest.main()
