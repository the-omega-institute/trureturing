from test_native_support import ROOT

class NativeInterfaceConsumerTests:
    def test_shared_inspector_and_audit_build_reuses_native_programs(self):
        self.reg_package()
        self.build()
        state = self.root / '.lake/build/lean-inspector'
        before = {path: (path.stat().st_mtime_ns, path.read_bytes())
                  for path in (state / 'producer').rglob('*')
                  if path.is_file() and (path.suffix == '.olean' or
                      path.name in ('reportInspector', 'inputDiscovery'))}
        self.assertTrue(before)
        self.write('tools/lean-inspector/LeanInformationAuditRegTests/CompiledDiscovery.lean',
                   'def main : IO Unit := IO.println "selected audit executed"\n')
        self.make_lean('leanInspector/reportInspector', 'regInspector/compiledJudgeTests')
        self.assertEqual(before, {path: (path.stat().st_mtime_ns, path.read_bytes()) for path in before})
        result = self.run_lake('-d', str(self.root / 'tools/lean-inspector-reg'),
                               'env', str(state / 'reg/bin/compiledJudgeTests'))
        self.assertIn('selected audit executed', result.stdout)
        compiled = state / 'reg/lib/lean/LeanInformationAuditRegTests/CompiledDiscovery.olean'
        stamp = compiled.stat().st_mtime_ns
        self.make_lean('leanInspector/reportInspector', 'regInspector/compiledJudgeTests')
        self.assertEqual(stamp, compiled.stat().st_mtime_ns)
        self.assertEqual(before, {path: (path.stat().st_mtime_ns, path.read_bytes()) for path in before})

    def test_raw_interface_edit_breaks_reg_consumer(self):
        self.reg_package()
        self.run_lake('build', 'Fixture')
        # A raw registration field type change forces its actual Reg consumer
        # to re-elaborate; the imported D5 content remains unchanged.
        self.write('Reg/Support/Entry.lean', 'import D5.A\nimport LeanInformationAuditInterface.Contract.Core\n'
                   'def entryTheorem (d : LeanInformationAudit.Contract.OptionSetting) : Lean.Name :=\n'
                   '  d.name\n')
        self.make_lean('Reg.Support.Entry')
        content = self.root / '.lake/build/lib/lean/D5/A.olean'
        before = (content.stat().st_mtime_ns, content.read_bytes())
        interface = self.root / 'tools/lean-inspector-interface/LeanInformationAuditInterface/Contract/Core.lean'
        original = interface.read_text()
        prefix, entry = original.split('structure OptionSetting where\n', 1)
        self.assertIn('  name : Name\n', entry)
        interface.write_text(prefix + 'structure OptionSetting where\n' +
                             entry.replace('  name : Name\n',
                                           '  name : String\n', 1))
        failed = self.make_lean('Reg.Support.Entry', success=False)
        self.assertIn('Reg/Support/Entry.lean', failed.stdout + failed.stderr)
        self.assertIn('name', failed.stdout + failed.stderr)
        self.assertEqual((content.stat().st_mtime_ns, content.read_bytes()), before)
        interface.write_text(original)
        self.make_lean('Reg.Support.Entry')
        self.assertEqual((content.stat().st_mtime_ns, content.read_bytes()), before)
