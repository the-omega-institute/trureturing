"""The declaration package must build with only the installed core toolchain."""
import json
import os
import re
import shutil
import tomllib

from test_native_support import ROOT, publication


class NativeInterfaceTests:
    def test_interface_registered_build_inputs(self):
        selection = publication.selection.Selection(ROOT)
        package = ROOT / 'tools/lean-inspector-interface'
        sources = {str(path.relative_to(ROOT)) for path in package.rglob('*.lean')
                   if '.lake' not in path.parts}
        self.assertTrue(sources)
        self.assertTrue(sources <= set(selection.expand('inspector_sources')))
        self.assertTrue(sources <= set(selection.dependency_sources()))
        self.assertFalse(sources & set(selection.modules().values()))
        for name in ('lakefile.toml', 'lake-manifest.json'):
            path = 'tools/lean-inspector-interface/' + name
            self.assertIn(path, selection.expand('config_inputs'))
            self.assertIn(dict(pattern=path, optional=False),
                          selection.data['config_inputs']['include'])

    def interface_package(self):
        source = ROOT / 'tools/lean-inspector-interface'
        self.assertTrue(source.is_dir(), 'missing standalone declaration Interface package')
        package = self.root / 'interface package'
        shutil.copytree(source, package, ignore=shutil.ignore_patterns('.lake'))
        shutil.copyfile(ROOT / 'lean-toolchain', package / 'lean-toolchain')
        config = package / 'lakefile.toml'
        policy = tomllib.loads(config.read_text())
        self.assertEqual(policy.get('require', []), [], 'Interface must have zero requires')
        self.assertEqual(json.loads((package / 'lake-manifest.json').read_text())['packages'], [])
        self.assertEqual(len(policy['lean_lib']), 1)
        # The production output is transported under the repository buildDir.
        # An isolated copy must keep both artifacts and Lake metadata in its temp root.
        self.assertTrue((source / policy['buildDir']).resolve().is_relative_to(ROOT / '.lake/build'))
        config.write_text(re.sub(r'(?m)^buildDir\s*=.*$', 'buildDir = ".lake/build"',
            re.sub(r'(?m)^packagesDir\s*=.*$', 'packagesDir = ".lake/packages"', config.read_text())))
        manifest = package / 'lake-manifest.json'
        resolved = json.loads(manifest.read_text())
        resolved['packagesDir'] = '.lake/packages'
        manifest.write_text(json.dumps(resolved))
        env = {key: value for key, value in os.environ.items()
               if not key.startswith(('LEAN_', 'LAKE_', 'ELAN_'))}
        return package, env

    def test_interface_standalone_core_only(self):
        package, env = self.interface_package()
        result = self.guarded_command([self.lake, 'build'], cwd=package, env=env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_interface_only_reports_missing_handler(self):
        package, env = self.interface_package()
        built = self.guarded_command([self.lake, 'build'], cwd=package, env=env)
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        (package / 'MissingHandler.lean').write_text(
            'import LeanInformationAuditInterface.Syntax\n'
            'register_information_template Nat\n')
        result = self.guarded_command([self.lake, 'env', 'lean', 'MissingHandler.lean'],
                                      cwd=package, env=env)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('elaboration function', result.stdout + result.stderr)
        self.assertNotIn('unexpected token', result.stdout + result.stderr)

    def test_interface_grammar_has_single_owner(self):
        implementation = ROOT / 'tools/lean-inspector/LeanInformationAudit/Syntax.lean'
        source = implementation.read_text()
        grammar = r'(?m)^\s*(syntax\b|declare_syntax_cat\b|elab\s)'
        self.assertFalse(re.search(grammar, source), 'implementation still declares registration grammar')
        self.assertNotRegex(source, r'(?m)^\s*def\s+(registrationTerm|\w+Keyword)\b')
        self.assertIn('run_cmd TemplateAudit.initializeGrammarPins', source)
        output_audit = implementation.parent / 'Projection/OutputOnlyAudit.lean'
        self.assertFalse(re.search(grammar, output_audit.read_text()),
                         'output-only audit still declares command grammar')
