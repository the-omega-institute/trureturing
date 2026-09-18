"""Normal inspect entry remains authoritative when a lightweight seed is available."""
from test_native_support import *
from test_reuse import EXECUTION
import reuse


class NativeReuseTests:
    def fetched_entry(self, *, packages_dir='.lake/packages'):
        self._configure_fetched_git_package(packages_dir=packages_dir)
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = EXECUTION
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.build()
        self.inspect()
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        self.assertTrue(publication.member(output, '.reuse.json').is_file())
        return output

    def test_fetched_workspace_override_reaches_native_error_and_restores(self):
        output = self.fetched_entry()
        package = self.root / '.lake/packages/fetched'
        override = self.root / 'override-package'
        shutil.copytree(package, override)
        source = override / 'Foreign/Thing.lean'
        source.write_text('def value : Nat := "wrong"\n')
        path = self.root / '.lake/package-overrides.json'
        path.write_text(json.dumps(dict(schemaVersion='1.2.0', packages=[dict(
            name='fetched', type='path', scope='fixture', dir='override-package',
            configFile='lakefile.toml', manifestFile='lake-manifest.json', inherited=False)])))
        failed = self.inspect(success=False)
        self.assertIn('phase=ensure status=started', failed.stderr)
        self.assertIn('Foreign/Thing.lean', failed.stderr)
        self.assertFalse(publication.member(output, '.reuse.json').exists())
        path.unlink()
        self.inspect()
        publication.verify_inputs(output, self.root)
        self.assertTrue(publication.member(output, '.reuse.json').is_file())
        # Even an empty override population has presence, bytes and mode.
        path.write_text('{"schemaVersion":"1.2.0","packages":[]}')
        self.assertIn('phase=ensure status=started', self.inspect().stderr)
        path.chmod(0o755)
        self.assertIn('phase=ensure status=started', self.inspect().stderr)
        path.unlink()
        self.assertIn('phase=ensure status=started', self.inspect().stderr)

    def test_fetched_package_alias_retarget_is_rejected_on_fresh_and_reused_entry(self):
        output = self.fetched_entry()
        package = self.root / '.lake/packages/fetched'
        saved = package.with_name('fetched-saved')
        changed = package.with_name('fetched-next')
        package.rename(saved)
        shutil.copytree(saved, changed)
        (changed / 'Foreign/Thing.lean').write_text('def value : Nat := "wrong"\n')
        for target in (saved, changed):
            package.symlink_to(target.name, target_is_directory=True)
            try:
                failed = self.inspect(success=False)
                self.assertIn('phase=ensure status=started', failed.stderr)
                self.assertFalse(publication.member(output, '.reuse.json').exists())
                with self.assertRaises(ValueError):
                    publication.verify_inputs(output, self.root)
            finally:
                package.unlink()
        saved.rename(package)
        self.inspect()
        publication.verify_inputs(output, self.root)
        self.assertTrue(publication.member(output, '.reuse.json').is_file())

    def test_fetched_optional_json_shapes_reconstruct_through_entry(self):
        output = self.fetched_entry()
        provenance = publication.member(output, '.provenance.json')
        for value in ([], None, {'native_inputs': []}, {'native_inputs': None},
                      {'native_inputs': {'packages': [None]}}):
            with self.subTest(provenance=value):
                provenance.write_text(json.dumps(value))
                recovered = self.inspect()
                self.assertIn('phase=ensure status=started', recovered.stderr)
                publication.validate_bundle(output, publication.coordinates(self.root), self.root)
                self.assertTrue(publication.member(output, '.reuse.json').is_file())
        policy = self.root / 'lean-report-inputs.json'
        original = policy.read_bytes()
        broken = json.loads(original)
        broken['native_inputs'] = []
        policy.write_text(json.dumps(broken))
        rejected = self.inspect(success=False)
        self.assertIn('LEAN_INSPECTOR_FAILED phase=inputs', rejected.stderr)
        self.assertNotIn('phase=ensure status=started', rejected.stderr)
        policy.write_bytes(original)
        self.inspect()
        publication.verify_inputs(output, self.root)

    def test_fetched_missing_descriptor_with_materialization_requires_lake(self):
        output = self.fetched_entry()
        before = self.stamps()
        (self.root / '.lake/build/lean-inspector/lake-inputs.json').unlink()
        recovered = self.inspect()
        self.assertIn('phase=ensure status=started', recovered.stderr)
        self.assertIn('phase=report status=completed', recovered.stderr)
        self.assertEqual(before, self.stamps())
        publication.verify_inputs(output, self.root)
        self.assertTrue(publication.member(output, '.reuse.json').is_file())

    def test_fetched_missing_descriptor_with_unlisted_checkout_requires_lake(self):
        self.check_unlisted_fetched_checkout('.lake/packages')

    def test_fetched_missing_descriptor_uses_configured_store(self):
        self.check_unlisted_fetched_checkout('vendor/fetched')

    def check_unlisted_fetched_checkout(self, packages_dir):
        output = self.fetched_entry(packages_dir=packages_dir)
        descriptor = self.root / '.lake/build/lean-inspector/lake-inputs.json'
        captured = json.loads(descriptor.read_bytes())['descriptor']
        package = self.root / packages_dir / 'fetched'
        sibling = package.with_name('unlisted')
        self.assertNotIn(sibling.relative_to(self.root).as_posix(),
                         [p['dir'] for p in captured['packages']])
        shutil.copytree(package, sibling)
        shutil.rmtree(package)
        descriptor.unlink()
        expected, origins = output.read_bytes(), self.origins()
        recovered = self.inspect()
        self.record_result('unlisted-checkout', dict(exit_code=recovered.returncode,
            ensure_entered='phase=ensure status=started' in recovered.stderr,
            report_completed='phase=report status=completed' in recovered.stderr,
            descriptor_restored=descriptor.is_file(), package_restored=package.is_dir(),
            stdout=recovered.stdout, stderr=recovered.stderr))
        self.assertIn('phase=ensure status=started', recovered.stderr,
                      '[FAIL] unlisted_fetched_checkout_requires_native_resolution')
        self.assertIn('phase=report status=completed', recovered.stderr)
        self.assertTrue(descriptor.is_file())
        self.assertTrue(package.is_dir())
        self.assertEqual(captured['packages_dir'], packages_dir)
        self.assertEqual(expected, output.read_bytes())
        self.assertEqual(origins, self.origins())
        publication.verify_inputs(output, self.root)
        self.assertTrue(publication.member(output, '.reuse.json').is_file())

    def test_fetched_store_absence_and_unlisted_partial_materializations(self):
        output = self.fetched_entry(packages_dir='vendor/fetched')
        descriptor = self.root / '.lake/build/lean-inspector/lake-inputs.json'
        store = self.root / 'vendor/fetched'
        expected, origins = output.read_bytes(), self.origins()
        for materialization in ('absent', 'empty', 'partial', 'file', 'dangling-alias'):
            with self.subTest(materialization=materialization):
                shutil.rmtree(store, ignore_errors=False)
                if descriptor.exists():
                    descriptor.unlink()
                if materialization != 'absent':
                    store.mkdir()
                if materialization == 'partial':
                    partial = store / 'unlisted/Foreign'
                    partial.mkdir(parents=True)
                    (partial / 'Thing.lean').write_text('def value : Nat := 9\n')
                elif materialization == 'file':
                    (store / 'unlisted').write_text('incomplete checkout')
                elif materialization == 'dangling-alias':
                    (store / 'unlisted').symlink_to('missing', target_is_directory=True)
                needs_lake = materialization not in ('absent', 'empty')
                self.assertEqual(reuse.probe(self.root, output, self.lake)['needs_lake'], needs_lake)
                recovered = self.inspect()
                self.assertEqual('phase=ensure status=started' in recovered.stderr, needs_lake)
                self.assertEqual(descriptor.is_file(), needs_lake)
                self.assertEqual((store / 'fetched').is_dir(), needs_lake)
                self.assertEqual(expected, output.read_bytes())
                self.assertEqual(origins, self.origins())
                publication.verify_inputs(output, self.root)
                self.assertTrue(publication.member(output, '.reuse.json').is_file())

                self.assertFalse((self.root / '.lake/packages').exists())
                if materialization == 'absent':
                    store.mkdir()

    def test_fetched_store_aliases_and_obstructions_reject_through_entry(self):
        output = self.fetched_entry(packages_dir='vendor/fetched')
        descriptor = self.root / '.lake/build/lean-inspector/lake-inputs.json'
        store = self.root / 'vendor/fetched'
        for shape in ('store-alias', 'parent-alias', 'store-file', 'parent-file'):
            with self.subTest(shape=shape):
                shutil.rmtree(store)
                descriptor.unlink()
                path = store.parent if shape.startswith('parent') else store
                if path.is_dir():
                    path.rmdir()
                saved = self.root / 'empty-store'
                saved.mkdir()
                if shape.endswith('alias'):
                    path.symlink_to(saved, target_is_directory=True)
                else:
                    path.write_text('not a checkout directory')
                try:
                    self.assertTrue(reuse.probe(self.root, output, self.lake)['needs_lake'])
                    failed = self.inspect(success=False)
                    self.assertIn('phase=ensure status=started', failed.stderr)
                    self.assertFalse(publication.member(output, '.reuse.json').exists())
                    with self.assertRaises(ValueError):
                        publication.verify_inputs(output, self.root)
                finally:
                    path.unlink()
                    shutil.rmtree(saved)
                self.inspect()
                publication.verify_inputs(output, self.root)
                self.assertTrue(publication.member(output, '.reuse.json').is_file())
        # Lake normalizes this configuration before locating fetched packages.
        # Its descriptor must retain the unsafe lexical spelling for validation.
        alias = self.root / 'store-alias'
        alias.symlink_to('vendor', target_is_directory=True)
        config = self.root / 'lakefile.toml'
        lexical = 'store-alias/../vendor/fetched'
        config.write_text(config.read_text().replace('packagesDir = "vendor/fetched"',
                                                    f'packagesDir = "{lexical}"'))
        rejected = self.inspect(success=False)
        self.assertIn('phase=ensure status=started', rejected.stderr)
        self.assertIn('unsafe native input path', rejected.stderr)
        self.assertEqual(json.loads(descriptor.read_bytes())['packages_dir'], lexical)
        self.assertFalse(publication.member(output, '.reuse.json').exists())

    def test_fetched_store_descriptor_damage_reconstructs(self):
        output = self.fetched_entry()
        descriptor = self.root / '.lake/build/lean-inspector/lake-inputs.json'
        expected = descriptor.read_bytes()
        stamps, origins = self.stamps(), self.origins()
        for damage in ('missing', None, [], '', '../outside', '/outside'):
            with self.subTest(packages_dir=damage):
                value = json.loads(expected)
                if damage == 'missing':
                    del value['descriptor']['packages_dir']
                else:
                    value['descriptor']['packages_dir'] = damage
                descriptor.write_text(json.dumps(value))
                recovered = self.inspect()
                self.assertIn('phase=ensure status=started', recovered.stderr)
                self.assertIn('phase=report status=completed', recovered.stderr)
                self.assertEqual(expected, descriptor.read_bytes())
                self.assertEqual(stamps, self.stamps())
                self.assertEqual(origins, self.origins())
                publication.verify_inputs(output, self.root)
                self.assertTrue(publication.member(output, '.reuse.json').is_file())

        provenance = publication.member(output, '.provenance.json')
        old = json.loads(provenance.read_bytes())
        del old['native_inputs']['descriptor']['packages_dir']
        provenance.write_text(json.dumps(old))
        descriptor.unlink()
        recovered = self.inspect()
        self.assertIn('phase=ensure status=started', recovered.stderr)
        self.assertIn('phase=report status=completed', recovered.stderr)
        self.assertEqual(stamps, self.stamps())
        self.assertEqual(origins, self.origins())
        publication.verify_inputs(output, self.root)
        self.assertTrue(publication.member(output, '.reuse.json').is_file())

    def test_fetched_modes_aliases_and_owner_evidence_through_entry(self):
        output = self.fetched_entry()
        package = self.root / '.lake/packages/fetched'
        for relative in ('Foreign/Hidden.lean', 'lakefile.toml'):
            with self.subTest(mode=relative):
                path = package / relative
                mode = path.stat().st_mode & 0o777
                path.chmod(mode | 0o111)
                entered = self.inspect()
                self.assertIn('phase=ensure status=started', entered.stderr)
                publication.verify_inputs(output, self.root)
                self.assertFalse(publication.member(output, '.reuse.json').exists())
                path.chmod(mode)
                self.inspect()
                self.assertTrue(publication.member(output, '.reuse.json').is_file())
        for relative in ('Foreign/Thing.lean', 'Foreign'):
            with self.subTest(alias=relative):
                path = package / relative
                saved = path.with_name(path.name + '-saved')
                path.rename(saved)
                path.symlink_to(saved.name, target_is_directory=saved.is_dir())
                try:
                    rejected = self.inspect(success=False)
                    self.assertIn('phase=ensure status=started', rejected.stderr)
                    self.assertFalse(publication.member(output, '.reuse.json').exists())
                finally:
                    path.unlink()
                    saved.rename(path)
                self.inspect()
                publication.verify_inputs(output, self.root)
                self.assertTrue(publication.member(output, '.reuse.json').is_file())
        descriptor = self.root / '.lake/build/lean-inspector/lake-inputs.json'
        for mutation in ('duplicate-owner', 'outside-owner', 'config'):
            with self.subTest(owner=mutation):
                data = json.loads(descriptor.read_bytes())
                fetched = next(p for p in data['descriptor']['packages'] if p['owner'] == 'fetched')
                if mutation == 'duplicate-owner':
                    data['descriptor']['packages'].append(dict(fetched))
                elif mutation == 'outside-owner':
                    fetched['source_roots'] = ['../outside']
                else:
                    fetched['config_paths'].append('../outside')
                descriptor.write_text(json.dumps(data))
                repaired = self.inspect()
                self.assertIn('phase=ensure status=started', repaired.stderr)
                publication.verify_inputs(output, self.root)
                self.assertTrue(publication.member(output, '.reuse.json').is_file())
        # Actual ambiguous library ownership must also fail Lake's fresh
        # descriptor, rather than only rejecting tampered optional evidence.
        config = self.root / 'lakefile.toml'
        original = config.read_bytes()
        config.write_bytes(original + b'\n[[lean_lib]]\nname = "Conflicting"\nroots = ["Foreign"]\n')
        self.write('Foreign/Thing.lean', 'def conflict : Nat := 1\n')
        rejected = self.inspect(success=False)
        self.assertIn('ambiguous native module owner', rejected.stderr)
        self.assertFalse(publication.member(output, '.reuse.json').exists())
        config.write_bytes(original)
        shutil.rmtree(self.root / 'Foreign')
        self.inspect()
        publication.verify_inputs(output, self.root)

    def inspect(self, *, success=True):
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        result = self.guarded_command(['bash', str(self.root / 'tools/lean-inspector/inspect.sh'),
            '--repository', str(self.root), '--output', str(output)], env=self.env)
        if success:
            self.assertEqual(result.returncode, 0, '[FAIL] report_entry_success\n' + result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0, '[FAIL] default_failure_blocks_reuse\n' + result.stdout + result.stderr)
        return result

    def test_report_entry_reuses_complete_receipt_and_rechecks_current_inputs(self):
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = EXECUTION
        policy['dependency_sources']['include'].append(dict(pattern='Audit.lean', optional=False))
        for path in ['tools/lean-inspector/reuse.py', 'tools/lean-inspector/inspect.sh', 'utility.json']:
            policy['producer_scopes']['lean-report']['include'].append(dict(pattern=path, optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.build()  # installs the collection's private compiler stage
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        first = self.inspect()
        self.assertIn('phase=report status=completed', first.stderr)
        self.assertTrue(publication.member(output, '.reuse.json').is_file(), '[FAIL] defaults_report_success_sealed')
        expected = output.read_bytes()
        seed = self.root / 'lightweight-seed' / output.name
        seed.parent.mkdir()
        for suffix in (*publication.SUFFIXES, '.reuse.json'):
            shutil.copyfile(publication.member(output, suffix), publication.member(seed, suffix))
        sealed = {suffix: publication.member(seed, suffix).read_bytes()
                  for suffix in (*publication.SUFFIXES, '.reuse.json')}
        def probe():
            result = self.guarded_command([sys.executable, '-B', str(self.root / 'tools/lean-inspector/reuse.py'),
                'probe', '--repository', str(self.root), '--report', str(seed), '--lake', self.lake], env=self.env)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertFalse(json.loads(result.stdout)['needs_lake'], '[FAIL] probe_only_selects_resources')
        probe()
        shutil.rmtree(self.root / '.lake')
        self.env['STRATALINT_LEAN_REPORT_REUSE'] = str(seed)
        reused = self.inspect()
        self.assertNotIn('phase=ensure status=started', reused.stderr, '[FAIL] heavy_cache_not_required')
        self.assertNotIn('phase=report status=started', reused.stderr)
        self.assertIn('LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0', reused.stdout)
        self.assertEqual(expected, output.read_bytes())
        self.assertFalse((self.root / '.lake/packages').exists())
        # Resource planning neither parses material semantics nor vouches for
        # bytes that may change before the normal entry consumes its seed.
        for damage in ('sealed-invalid-material', 'changed-after-probe'):
            with self.subTest(damage=damage):
                for suffix, data in sealed.items():
                    publication.member(seed, suffix).write_bytes(data)
                if damage == 'changed-after-probe':
                    probe()
                archive = publication.member(seed, '.materials.zip')
                with zipfile.ZipFile(archive, 'a') as target:
                    target.writestr('unreferenced', b'not an admitted report material')
                if damage == 'sealed-invalid-material':
                    receipt = json.loads(sealed['.reuse.json'])
                    receipt['bundle']['.materials.zip'] = publication.digest(archive)
                    publication.member(seed, '.reuse.json').write_text(json.dumps(receipt))
                    probe()
                shutil.rmtree(self.root / '.lake')
                recovered = self.inspect()
                self.assertIn('phase=ensure status=started', recovered.stderr)
                self.assertIn('phase=report status=completed', recovered.stderr,
                              '[FAIL] invalid_seed_must_reenter_native_producer')
                self.assertEqual(expected, output.read_bytes())
                publication.validate_bundle(output, publication.coordinates(self.root), self.root)
        for suffix, data in sealed.items():
            publication.member(seed, suffix).write_bytes(data)
        probe()
        # A successful planning probe never exempts the normal entry from the
        # default-only input obligation. A changed audit must reach Lake/fail.
        self.write('Audit.lean', 'def audit : False := True.intro\n')
        failed = self.inspect(success=False)
        self.assertIn('LEAN_INSPECTOR_FAILED phase=report', failed.stderr)
        self.assertFalse(publication.member(output, '.reuse.json').exists())
        self.write('Audit.lean', 'def audit : Nat := 1\n')
        publication.member(seed, '.reuse.json').unlink()
        recovered = self.inspect()
        self.assertIn('phase=report status=completed', recovered.stderr)
        self.assertTrue(publication.member(output, '.reuse.json').is_file())
        policy['report_execution'] = dict(EXECUTION, tools=['arbitrary-command'])
        self.write('lean-report-inputs.json', json.dumps(policy))
        invalid = self.inspect(success=False)
        self.assertIn('LEAN_INSPECTOR_FAILED phase=inputs', invalid.stderr)
        self.assertNotIn('phase=report status=started', invalid.stderr)

    def test_fetched_package_absence_reuses_only_wholly_unmaterialized_snapshot(self):
        self._configure_fetched_git_package()
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = EXECUTION
        policy['dependency_sources']['include'].append(dict(pattern='Audit.lean', optional=False))
        for path in ['tools/lean-inspector/reuse.py', 'tools/lean-inspector/inspect.sh', 'utility.json']:
            policy['producer_scopes']['lean-report']['include'].append(dict(pattern=path, optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.build()
        self.inspect()
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        seed = self.root / 'lightweight-seed' / 'raw-lean-report.json'
        seed.parent.mkdir()
        for suffix in (*publication.SUFFIXES, '.reuse.json'):
            shutil.copyfile(publication.member(output, suffix),
                            publication.member(seed, suffix))
        shutil.rmtree(self.root / '.lake')
        self.env['STRATALINT_LEAN_REPORT_REUSE'] = str(seed)
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        with patch.object(publication, 'coordinates', side_effect=AssertionError('probe prepares publication')), \
                patch.object(publication, 'validate_bundle', side_effect=AssertionError('probe accepts publication')):
            self.assertEqual(reuse.probe(self.root, seed, self.lake),
                             dict(needs_lake=False, reason='receipt-matched'))
        reused = self.inspect()
        self.assertEqual(reused.returncode, 0, reused.stdout + reused.stderr)
        self.assertNotIn('phase=ensure status=started', reused.stderr)
        self.assertEqual(output.read_bytes(), seed.read_bytes())
        # A present but incomplete checkout is a miss even though the
        # producer-bound Git snapshot itself remains unchanged.
        partial = self.root / '.lake/packages/fetched/Foreign'
        partial.mkdir(parents=True)
        (partial / 'Thing.lean').write_text('def value : Nat := 9\n')
        captured = reuse.probe(self.root, seed, self.lake)
        self.assertTrue(captured['needs_lake'], captured)
        repaired = self.inspect()
        self.assertIn('phase=ensure status=started', repaired.stderr)
        publication.verify_inputs(output, self.root)
        self.assertTrue(publication.member(output, '.reuse.json').is_file())
        self.assertEqual(output.read_bytes(), seed.read_bytes())

    def test_fetched_default_only_failure_and_metadata_reuse(self):
        self._configure_fetched_git_package()
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = EXECUTION
        for path in ['tools/lean-inspector/reuse.py', 'tools/lean-inspector/inspect.sh', 'utility.json']:
            policy['producer_scopes']['lean-report']['include'].append(dict(pattern=path, optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))
        # Audit.lean is intentionally not manually registered: native defaults
        # must account for it and the fetched module used only by that default.
        self.build()
        self.inspect()
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        self.assertTrue(publication.member(output, '.reuse.json').is_file())
        origins = self.origins()
        self.assertTrue(all(not any(item['module'] == 'Foreign.AuditOnly'
                                   for item in origin['external_inputs']) for origin in origins.values()))
        before = self.stamps()
        source = self.root / '.lake/packages/fetched/Foreign/AuditOnly.lean'
        original = source.read_bytes()
        source.write_text('def auditOnly : False := True.intro\n')
        self.assertTrue(reuse.probe(self.root, output, self.lake)['needs_lake'])
        failed = self.inspect(success=False)
        self.assertIn('LEAN_INSPECTOR_FAILED phase=report', failed.stderr)
        self.assertFalse(publication.member(output, '.reuse.json').exists())
        source.write_bytes(original)
        self.inspect()
        self.assertEqual(before, self.stamps())
        self.assertTrue(publication.member(output, '.reuse.json').is_file())
        oleans = {str(path): (path.stat().st_mtime_ns, publication.digest(path))
                  for path in (self.root / '.lake/build/lib/lean').rglob('*.olean*')}
        config = self.root / 'lakefile.toml'
        config.write_text(config.read_text() + '\n# compatible metadata\n')
        self.assertTrue(reuse.probe(self.root, output, self.lake)['needs_lake'])
        result = self.inspect()
        self.assertIn('extracted_modules=0', result.stdout)
        self.assertEqual(before, self.stamps())
        self.assertEqual(origins, self.origins())
        self.assertEqual(oleans, {str(path): (path.stat().st_mtime_ns, publication.digest(path))
                                 for path in (self.root / '.lake/build/lib/lean').rglob('*.olean*')})
        # A malformed descriptor cannot be replaced with yesterday's inputs.json.
        descriptor = self.root / '.lake/build/lean-inspector/lake-inputs.json'
        descriptor.write_text('{broken')
        self.assertTrue(reuse.probe(self.root, output, self.lake)['needs_lake'])
        repaired = self.inspect()
        self.assertIn('phase=report status=completed', repaired.stderr)
        self.assertIn('extracted_modules=0', repaired.stdout)
        # A custom default is outside the native source population: execute it.
        config.write_text(config.read_text().replace('["Fixture", "Audit"]', '["Fixture", "Audit", "cache"]'))
        self.inspect()
        self.assertFalse(publication.member(output, '.reuse.json').exists())

    def test_fetched_entry_retains_preensure_root_capture(self):
        self._configure_fetched_git_package()
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = EXECUTION
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.build()
        entry = self.root / 'tools/lean-inspector/inspect.sh'
        source = entry.read_text()
        marker = 'run_phase ensure /bin/bash'
        self.assertEqual(source.count(marker), 1)
        source = source.replace(marker,
            'printf "\\n-- changed after root capture\\n" >> "$REPOSITORY/D5/Alone.lean"\n' + marker)
        entry.write_text(source)
        result = self.inspect(success=False)
        self.assertIn('root inputs changed during report entry', result.stderr)
        self.assertIn('LEAN_INSPECTOR_FAILED phase=capture-final', result.stderr)
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        self.assertFalse(publication.member(output, '.reuse.json').exists())
