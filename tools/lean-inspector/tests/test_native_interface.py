"""Contract inputs and package admission compile without the judge implementation."""
import json
import os
import re
import shutil
import tomllib

from test_native_support import ROOT, publication, copy_contract_interface


class NativeInterfaceTests:
    def test_interface_registered_build_inputs(self):
        selection = publication.selection.Selection(ROOT)
        package = ROOT / 'tools/lean-inspector-interface'
        sources = {str(path.relative_to(ROOT)) for path in package.rglob('*.lean')
                   if '.lake' not in path.parts}
        contract = package / 'LeanInformationAuditInterface/Contract'
        sources.update(str(path.relative_to(ROOT)) for path in contract.glob('*.lean'))
        self.assertTrue(any(path.startswith(str(contract.relative_to(ROOT))) for path in sources))
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
        policy = tomllib.loads((source / 'lakefile.toml').read_text())
        self.assertEqual(policy.get('require', []), [{'name': 'trureturing', 'path': '../..'}])
        copy_contract_interface(source, package)
        shutil.copyfile(ROOT / 'lean-toolchain', package / 'lean-toolchain')
        config = package / 'lakefile.toml'
        policy = tomllib.loads(config.read_text())
        self.assertEqual(policy.get('require', []), [], 'Recorder fixture must have zero requires')
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

    def test_interface_typed_inputs_compile_without_judge(self):
        package, env = self.interface_package()
        built = self.guarded_command([self.lake, 'build'], cwd=package, env=env)
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        (package / 'TypedInputs.lean').write_text('''import LeanInformationAuditInterface.Contract.Catalog
open LeanInformationAudit
def rootInput : Contract.RootCatalog := { data := {
  rootId := `TypedInputs, expected := #[], source := #[], baseline := #[], companionPrefix := none } }
def templateInput : Contract.TemplateEnrollment Nat := {
  name := `Nat, version := 1, constructors := #[], options := #[] }
''')
        result = self.guarded_command([self.lake, 'env', 'lean', 'TypedInputs.lean'], cwd=package, env=env)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertNotIn('IE-C050', result.stdout + result.stderr)
