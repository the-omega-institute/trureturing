namespace StrataLint.Tests;

internal sealed partial class LeanReportTransportFixture
{
    private string CacheScript => Path.Combine(Repository, "tools/scripts/report/lean-report-cache.py");
    private string MaterialScript => Path.Combine(Repository, "tools/lean-inspector/materials.py");

    internal void TamperMaterial(string report) => Success(Run(["python3", "-I", "-B", "-c",
        MaterialTamper + "\ntamper(pathlib.Path(sys.argv[3]))\n", CacheScript, MaterialScript, report]));

    internal Attempt ExerciseMaterialTransport(bool tampered) => Run(["python3", "-I", "-B", "-c",
        MaterialTamper + MaterialTransport, CacheScript, MaterialScript, Output, temporary.Path, tampered ? "1" : "0"]);

    private const string MaterialTamper = """
        import hashlib, json, pathlib, runpy, subprocess, sys, zipfile
        statement_address = runpy.run_path(sys.argv[2])['statement_address']
        def tamper(report):
            archive = pathlib.Path(str(report) + '.materials.zip')
            records = json.loads(report.read_bytes())['modules']
            stable = next(record for record in records if record['module'] == 'D5.Probe')
            name = stable['declarations'][0]['type_sha256'].replace(':', '/', 1)
            with zipfile.ZipFile(archive) as z:
                assert z.testzip() is None
                infos = z.infolist()
                contents = {info.filename: z.read(info) for info in infos}
                assert all(statement_address(data).replace(':', '/', 1) == key for key, data in contents.items())
            damaged = b'CRC-valid material content mismatch\n'
            assert statement_address(damaged).replace(':', '/', 1) != name
            with zipfile.ZipFile(archive, 'w') as z:
                for info in infos: z.writestr(info, damaged if info.filename == name else contents[info.filename])
            with zipfile.ZipFile(archive) as z:
                assert z.testzip() is None, 'tamper is not CRC-valid'
                assert z.namelist() == list(contents), 'tamper changed member names'
                assert all(z.read(key) == (damaged if key == name else data) for key, data in contents.items())
            print('P1 tamper: canonical valid input; same member set; one mismatched payload; CRC valid')

        """;

    private const string MaterialTransport = """
        script, _, live, scratch, damaged = sys.argv[1:]
        api = runpy.run_path(script)
        scratch = pathlib.Path(scratch) / 'material-transport'
        incoming = scratch / 'incoming'
        incoming.mkdir(parents=True)
        report = api['copy_bundle'](pathlib.Path(live), incoming, True)
        provenance, repository = api['bundle_metadata'](report, True)
        name = api['asset_name'](repository, provenance['producer_sha256'],
            provenance['repository_inspector_sha256'], provenance['lean_config_sha256'])
        archive = scratch / name
        def invoke(*args):
            return subprocess.run([sys.executable, '-I', '-B', script, *map(str, args)], capture_output=True, text=True)
        control = invoke('pack', report, archive)
        assert control.returncode == 0, control.stderr
        original = {p: p.read_bytes() for p in incoming.iterdir()}
        if damaged == '1':
            tamper(report)
            assert all(p.read_bytes() == data for p, data in original.items() if p.suffix != '.zip')
            with zipfile.ZipFile(archive) as z:
                infos = z.infolist()
                outer = {info.filename: z.read(info) for info in infos}
            outer[report.name + '.materials.zip'] = pathlib.Path(str(report) + '.materials.zip').read_bytes()
            with zipfile.ZipFile(archive, 'w') as z:
                for info in infos: z.writestr(info, outer[info.filename])
            pathlib.Path(str(archive) + '.sha256').write_text(hashlib.sha256(archive.read_bytes()).hexdigest() + '  ' + name + '\n')
        with zipfile.ZipFile(archive) as z: assert z.testzip() is None
        packed = scratch / 'repacked'
        packed.mkdir()
        results = {
            'validate': invoke('validate', report),
            'pack': invoke('pack', report, packed / name),
            'unpack': invoke('unpack', archive, scratch / 'unpacked'),
            'stage': invoke('stage', '--transport', '--bundle', report, '--cache-root', scratch / 'cache'),
        }
        print('P1 transport exits: ' + json.dumps({key: result.returncode for key, result in results.items()}))
        for operation, result in results.items():
            assert result.returncode == (1 if damaged == '1' else 0), (operation, result.returncode, result.stderr)
            if damaged == '1': assert 'statement material address mismatch' in result.stderr, result.stderr
        if damaged == '1':
            assert not (packed / name).exists(), 'bad material was packed'
            assert not (scratch / 'cache' / provenance['input_address'][7:]).exists(), 'bad seed was installed'
        else:
            for suffix in api['SUFFIXES']:
                assert (scratch / 'unpacked' / (report.name + suffix)).read_bytes() == pathlib.Path(str(report) + suffix).read_bytes()
        """;
}
