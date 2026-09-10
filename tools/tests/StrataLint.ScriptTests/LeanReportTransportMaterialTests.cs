namespace StrataLint.Tests;

public sealed class LeanReportTransportMaterialTests
{
    [Theory]
    [InlineData("valid")]
    [InlineData("empty")]
    [InlineData("missing-member")]
    [InlineData("extra-member")]
    [InlineData("duplicate-member")]
    [InlineData("invalid-archive")]
    [InlineData("crc")]
    public void TransportStageRequiresCompleteReadableMaterials(string scenario)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var result = TestProcessRunner.Run("python3", ["-I", "-B", "-c", MaterialCase,
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/report/lean-report-cache.py"),
            temporary.Path, scenario], temporary.Path, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            System.Text.Encoding.UTF8.GetString(result.StandardOutput) + System.Text.Encoding.UTF8.GetString(result.StandardError));
    }

    private const string MaterialCase = """
        import hashlib, json, pathlib, struct, subprocess, sys, warnings, zipfile
        script, scratch, scenario = sys.argv[1:]
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
