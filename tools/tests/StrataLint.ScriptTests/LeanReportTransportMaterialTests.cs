using FixtureFile = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

public sealed class LeanReportTransportMaterialTests
{
    [Theory]
    [InlineData("invalid-archive")]
    [InlineData("missing-member")]
    [InlineData("missing-archive")]
    public void LocalExactMaterialDamageRegeneratesAfterAValidHit(string damage)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new LeanReportTransportFixture();
        fixture.Success(fixture.MakeReport("STRATALINT_REPORT_CACHE_REMOTE=0"));
        Assert.Single(fixture.ProducerCalls);
        var original = fixture.CacheSnapshot();
        var materials = FixtureFile.ReadAllBytes(fixture.Output + ".materials.zip");
        fixture.Success(fixture.Stage(fixture.Output));

        var hit = fixture.MakeReport("STRATALINT_REPORT_CACHE_REMOTE=0");
        fixture.Success(hit);
        Assert.Contains("status=hit mode=local-exact", hit.Text, StringComparison.Ordinal);
        Assert.Single(fixture.ProducerCalls);
        Assert.Single(fixture.SlotCalls);
        Assert.Equal(original, fixture.CacheSnapshot());

        fixture.DamageCachedMaterials(damage);
        foreach (var suffix in LeanReportTransportFixture.Suffixes.Where(suffix => suffix != ".materials.zip"))
            Assert.Equal(original[Array.IndexOf(LeanReportTransportFixture.Suffixes, suffix)],
                LeanReportTransportFixture.Digest(FixtureFile.ReadAllBytes(fixture.CachedReport + suffix)));
        var recovered = fixture.MakeReport("STRATALINT_REPORT_CACHE_REMOTE=0");
        fixture.Success(recovered);
        Assert.Contains("status=miss reason=local-entry-unavailable", recovered.Text, StringComparison.Ordinal);
        Assert.Contains("mode=produced", recovered.Text, StringComparison.Ordinal);
        Assert.Equal(2, fixture.ProducerCalls.Length);
        Assert.Equal(2, fixture.SlotCalls.Length);
        Assert.Equal(["absent", "present", "present"], fixture.EnsureCalls);
        Assert.Empty(fixture.ReleaseCalls);
        Assert.Equal(materials, FixtureFile.ReadAllBytes(fixture.Output + ".materials.zip"));
        fixture.Success(fixture.Stage(fixture.Output));
        fixture.Success(fixture.Stage(fixture.CachedReport));
    }

    [Theory]
    [InlineData("occupied", "valid")]
    [InlineData("occupied", "missing-member")]
    [InlineData("race", "valid")]
    [InlineData("race", "missing-member")]
    public void TransportStageValidatesTheSelectedEntry(string selection, string scenario) => RunMaterialCase(scenario, selection);

    [Theory]
    [InlineData("valid")]
    [InlineData("empty")]
    [InlineData("missing-member")]
    [InlineData("extra-member")]
    [InlineData("duplicate-member")]
    [InlineData("invalid-archive")]
    [InlineData("crc")]
    public void TransportStageRequiresCompleteReadableMaterials(string scenario) => RunMaterialCase(scenario, "fresh");

    private static void RunMaterialCase(string scenario, string selection)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var result = TestProcessRunner.Run("python3", ["-I", "-B", "-c", MaterialCase,
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/report/lean-report-cache.py"),
            temporary.Path, scenario, selection], temporary.Path, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            System.Text.Encoding.UTF8.GetString(result.StandardOutput) + System.Text.Encoding.UTF8.GetString(result.StandardError));
    }

    private const string MaterialCase = """
        import contextlib, hashlib, io, json, pathlib, runpy, struct, subprocess, sys, warnings, zipfile
        from unittest.mock import patch
        script, scratch, selected_scenario, selection = sys.argv[1:]
        scenario = selected_scenario if selection == 'fresh' else 'valid'
        scratch = pathlib.Path(scratch)
        report = scratch / 'candidate-lean-report.json'
        def sidecar(suffix): return pathlib.Path(str(report) + suffix)
        producer, resident, sources, config = [c * 64 for c in 'abcd']
        common = f'repository_inspector_sha256={resident}\nlean_sources_sha256={sources}\nlean_config_sha256={config}\n'
        pair = hashlib.sha256(('schema=stratalint-lean-report-input-v1\n' + f'producer_sha256={producer}\n' + common).encode()).hexdigest()
        repository = hashlib.sha256(('schema=stratalint-lean-report-repository-input-v1\n' + common).encode()).hexdigest()
        material = b'canonical material fixture\n'
        address = hashlib.sha256(b'trureturing:statement:v1\0' + material).hexdigest()
        name = 'sha256/' + address
        declaration = dict(type_sha256='sha256:' + address, statement_id='sha256:' + 'e' * 64)
        # Shared material is stored once even when multiple declarations reference it.
        modules = [] if scenario == 'empty' else [dict(module='D5.Probe', source_path='D5/Probe.lean',
            source_sha256='sha256:' + 'f' * 64, imports=[], declarations=[declaration, declaration])]
        report.write_text(json.dumps(dict(schema='stratalint-raw-lean-report-v2', modules=modules)) + '\n')
        digest = hashlib.sha256(report.read_bytes()).hexdigest()
        sidecar('.sha256').write_text(digest + '  ' + report.name + '\n')
        sidecar('.input.attestation').write_text('schema=stratalint-lean-report-input-attestation-v1\n'
            + f'repository_input_sha256={repository}\nproducer_sha256={producer}\nreport_sha256={digest}\n')
        sidecar('.provenance.json').write_text(json.dumps(dict(schema='stratalint-lean-report-provenance-v1',
            side='candidate', mode='cached', source_side='candidate', input_address='sha256:' + pair,
            producer_sha256=producer, repository_inspector_sha256=resident, lean_sources_sha256=sources,
            lean_config_sha256=config, report_sha256=digest)) + '\n')
        archive = sidecar('.materials.zip')
        with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_STORED) as z:
            if scenario not in ('empty', 'missing-member'): z.writestr(name, material)
            if scenario == 'extra-member': z.writestr('sha256/' + '0' * 64, b'unreferenced')
            if scenario == 'duplicate-member':
                with warnings.catch_warnings():
                    warnings.simplefilter('ignore', UserWarning)
                    z.writestr(name, material)
        if scenario == 'invalid-archive': archive.write_bytes(b'not a material ZIP')
        if scenario == 'crc':
            with zipfile.ZipFile(archive) as z: info = z.getinfo(name)
            data = bytearray(archive.read_bytes())
            namesize, extrasize = struct.unpack_from('<HH', data, info.header_offset + 26)
            data[info.header_offset + 30 + namesize + extrasize] ^= 1
            archive.write_bytes(data)
        original = {p: p.read_bytes() for p in scratch.iterdir() if p.is_file()}
        if selection != 'fresh':
            api = runpy.run_path(script)
            destination = scratch / 'selected-cache'
            destination.mkdir(mode=0o700)
            entry = destination / pair
            def install_selected():
                entry.mkdir()
                selected = api['copy_bundle'](report, entry, True)
                if selected_scenario == 'missing-member':
                    with zipfile.ZipFile(str(selected) + '.materials.zip', 'w'): pass
                return selected
            if selection == 'occupied': install_selected()
            original_rename = pathlib.Path.rename
            raced = []
            def rename(staged, target):
                assert target == entry
                assert not raced, 'unexpected repeated installation'
                raced.append(install_selected())
                # A real occupied-directory rename failure, injected at the IO seam.
                return original_rename(staged, target)
            sys.argv = [script, 'stage', '--transport', '--bundle', str(report), '--cache-root', str(destination)]
            stdout, stderr = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                with patch.object(pathlib.Path, 'rename', rename) if selection == 'race' else contextlib.nullcontext():
                    rc = api['main']()
            valid = selected_scenario == 'valid'
            assert rc == (0 if valid else 1), (rc, stdout.getvalue(), stderr.getvalue())
            assert bool(stdout.getvalue().strip()) == valid, 'invalid selection reported ready'
            assert ('status=ready' in stderr.getvalue()) == valid
            selected = entry / 'raw-lean-report.json'
            with zipfile.ZipFile(str(selected) + '.materials.zip') as z:
                assert z.testzip() is None
                assert z.namelist() == ([name] if valid else [])
            if valid:
                assert stdout.getvalue().strip() == str(destination)
                assert selected.read_bytes() == report.read_bytes()
                assert pathlib.Path(str(selected) + '.materials.zip').read_bytes() == archive.read_bytes()
            else: assert 'material-members-mismatch' in stderr.getvalue()
            assert bool(raced) == (selection == 'race')
            assert not list(destination.glob('.staging.*')), 'staging directory leaked'
            assert all(p.read_bytes() == data for p, data in original.items()), 'incoming bundle changed'
            raise SystemExit(0)
        valid = scenario in ('valid', 'empty')
        for option in ('--staging-directory', '--cache-root'):
            destination = scratch / option[2:]
            result = subprocess.run([sys.executable, '-I', '-B', script, 'stage', '--transport',
                '--bundle', str(report), option, str(destination)], capture_output=True, text=True)
            assert result.returncode == (0 if valid else 1), (scenario, option, result.returncode, result.stdout, result.stderr)
            if valid:
                staged = destination / (pair if option == '--cache-root' else '') / 'raw-lean-report.json'
                assert staged.read_bytes() == report.read_bytes()
                assert pathlib.Path(str(staged) + '.materials.zip').read_bytes() == archive.read_bytes()
                assert pathlib.Path(str(staged) + '.sha256').read_text() == digest + '  raw-lean-report.json\n'
            else:
                assert not result.stdout.strip(), 'rejected bundle reported ready'
                if option == '--cache-root': assert not (destination / pair).exists(), 'invalid private seed installed'
                diagnostic = {'invalid-archive': 'File is not a zip file', 'crc': 'corrupt-materials-zip'}.get(scenario, 'material-members-mismatch')
                assert diagnostic in result.stderr, result.stderr
        # The optional adapter returns zero on failure, but must not return a ready root.
        adapter = str(pathlib.Path(script).with_name('lean-report-ci-baseline.sh'))
        destination = scratch / 'adapter-cache'
        adapted = subprocess.run(['bash', adapter, '--bundle', str(report), '--cache-root', str(destination),
            '--transport'], capture_output=True, text=True)
        assert adapted.returncode == 0, adapted.stderr
        assert bool(adapted.stdout.strip()) == valid, adapted.stdout
        assert (destination / pair).exists() == valid
        if not valid: assert 'status=fallback' in adapted.stderr, adapted.stderr
        assert all(p.read_bytes() == data for p, data in original.items()), 'source bundle changed'
        """;
}
