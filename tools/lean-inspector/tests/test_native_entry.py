"""Whole production-entry regressions: Lake witnesses before report reuse."""
from test_native_support import *
from test_native_invalidation import NativeSemanticConsumerTests


class NativeEntryConsumerTests:
    def whole_entry(self, *, success=True):
        output = self.root / 'public.json'
        result = self.guarded_command(['bash', str(self.root / 'tools/lean-inspector/inspect.sh'),
            '--repository', str(self.root), '--output', str(output)], env=self.env)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        return result

    def test_whole_entry_driver_data_requires_current_verdict(self):
        original = self.build
        calls = 0
        def build(success=True, **kwargs):
            nonlocal calls
            calls += 1
            if calls == 3:
                old = (self.root / 'public.json').read_bytes()
                rejected = self.whole_entry(success=False)
                self.assertIn('driver-data-rejected', rejected.stdout + rejected.stderr)
                self.assertEqual(old, (self.root / 'public.json').read_bytes())
                self.assertFalse(publication.member(self.root / 'public.json', '.reuse.json').exists())
                self.record_result('whole-entry-driver-rejected', dict(exit=rejected.returncode,
                    driver_data_rejected=True, accepted_report_unchanged=True, receipt_removed=True))
            result = original(success=success, **kwargs)
            if calls == 1:
                self.copy('tools/scripts/workflow/ci_plan.py')
                self.env['STRATALINT_LEAN_BUILD_TARGETS'] = '["trureturing/LeanInformationAudit.Registry"]'
                self.whole_entry()
                self.assertTrue(publication.member(self.root / 'public.json', '.reuse.json').is_file())
            return result
        self.build = build
        NativeSemanticConsumerTests.test_driver_only_data_requires_current_production_verdict(self)

    def test_whole_entry_dirty_external_source_is_current_at_unchanged_pin(self):
        original = self.build
        calls = 0
        def build(success=True, **kwargs):
            nonlocal calls
            calls += 1
            if calls == 3:
                self.whole_entry()
                rows = json.loads((self.root / 'public.json').read_text())['modules']
                row = next(row for row in rows if row['module'] == 'D5.A')
                self.assertEqual(row['declarations'][0]['axioms'], ['Classical.choice'])
                self.record_result('whole-entry-dirty-external', dict(axioms=['Classical.choice'],
                    pin_changed=False, actual_entry='inspect.sh'))
            result = original(success=success, **kwargs)
            if calls == 1:
                self.whole_entry()
                self.assertTrue(publication.member(self.root / 'public.json', '.reuse.json').is_file())
            return result
        self.build = build
        NativeSemanticConsumerTests.test_external_package_semantic_source_binding(self)
        output = self.root / 'public.json'
        accepted = output.read_bytes()
        # Ask this Reg workspace for its actual search order. Dependencies
        # can precede the root; placing a file after its owner is not shadowing.
        search = self.run_lake('-d', str(self.root / 'Reg'), 'env', sys.executable, '-c',
            'import json,os;print(json.dumps([os.getcwd(),os.environ["LEAN_PATH"].split(os.pathsep)]))')
        cwd, directories = json.loads(next(line for line in search.stdout.splitlines() if line.startswith('[')))
        first = Path(directories[0])
        if not first.is_absolute(): first = Path(cwd) / first
        shadow = first.resolve() / 'D5/A.olean'
        original = self.root / '.lake/build/lib/lean/D5/A.olean'
        self.assertTrue(shadow.is_relative_to(self.root.resolve()))
        self.assertNotEqual(shadow, original.resolve())
        shadow.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(original, shadow)
        failed = self.whole_entry(success=False)
        self.assertIn('shadowed export D5.A', failed.stdout + failed.stderr)
        self.assertEqual(accepted, output.read_bytes())
        self.assertFalse(publication.member(output, '.reuse.json').exists())
        self.record_result('whole-entry-shadowed-export', dict(exit=failed.returncode,
            shadowed_export_rejected=True, accepted_output_unchanged=True))

    def test_whole_entry_private_claim_support_and_program_only_changes(self):
        support = 'module\npublic section\nprivate def body : Prop := False\ndef claimSupport : Prop := body\n'
        self.write('ClaimSupport.lean', support)
        self.whole_entry()
        output = self.root / 'public.json'
        def evidence():
            return next(row['utility_refutation']['is_closed_negation']
                for row in json.loads(output.read_text())['modules'] if row['module'] == 'Fixture')
        self.assertTrue(evidence())
        before = output.read_bytes()
        witness = json.loads(publication.member(output, '.reuse.json').read_text())['semantic_witness']
        stamps = self.stamps()
        self.write('LeanInformationAudit/Registry.lean', 'def fixtureDriver : Nat := 2\n')
        reused = self.whole_entry()
        self.assertIn('complete-entry-reused', reused.stdout)
        self.assertIn('extracted_modules=0 aggregates=0', reused.stdout)
        self.assertEqual(before, output.read_bytes())
        self.assertEqual(stamps, self.stamps())
        self.assertEqual(witness, json.loads(publication.member(output, '.reuse.json').read_text())['semantic_witness'])
        self.record_result('whole-entry-program-only', dict(same_semantic_witness=True,
            extracted_modules=0, aggregates=0, report_and_native_rows_unchanged=True))
        self.write('LeanInformationAudit/Registry.lean', 'def fixtureDriver : False := True.intro\n')
        self.whole_entry(success=False)
        self.assertEqual(before, output.read_bytes())
        self.assertFalse(publication.member(output, '.reuse.json').exists())
        self.write('LeanInformationAudit/Registry.lean', 'def fixtureDriver : Nat := 2\n')
        self.whole_entry()
        self.write('ClaimSupport.lean', support.replace(':= False', ':= True'))
        self.whole_entry()
        self.assertFalse(evidence())
        self.record_result('whole-entry-private-claim-support', dict(before=True, after=False,
            claim_root_unchanged=True, private_transitive_data_changed=True))

    def test_whole_entry_publisher_failure_keeps_donor_and_accepted_output(self):
        self.whole_entry()
        output = self.root / 'public.json'
        donor = self.root / 'donor/report.json'
        donor.parent.mkdir()
        suffixes = (*publication.SUFFIXES, '.reuse.json')
        for suffix in suffixes:
            os.link(publication.member(output, suffix), publication.member(donor, suffix))
        before = {suffix: publication.member(donor, suffix).read_bytes() for suffix in suffixes}
        stamps = self.stamps()
        self.env['STRATALINT_LEAN_REPORT_REUSE'] = str(donor)
        publisher = self.root / 'tools/lean-inspector/publication.py'
        source = publisher.read_text()
        entry = '    report, destination = Path(report), Path(destination)'
        self.assertEqual(source.count(entry), 1)
        publisher.write_text(source.replace(entry, entry +
            '\n    if mode == "cached": raise PublicationFailure("injected publisher failure")'))
        failed = self.whole_entry(success=False)
        self.assertIn('injected publisher failure', failed.stdout + failed.stderr)
        self.assertEqual(stamps, self.stamps())
        self.assertEqual(before, {suffix: publication.member(donor, suffix).read_bytes() for suffix in suffixes})
        self.assertEqual({suffix: before[suffix] for suffix in publication.SUFFIXES},
                         {suffix: publication.member(output, suffix).read_bytes() for suffix in publication.SUFFIXES})
        self.assertFalse(publication.member(output, '.reuse.json').exists())
        self.record_result('whole-entry-publisher-failure', dict(exit=failed.returncode,
            donor_unchanged=True, accepted_output_unchanged=True, native_rows_unchanged=True,
            output_receipt_removed=True))

