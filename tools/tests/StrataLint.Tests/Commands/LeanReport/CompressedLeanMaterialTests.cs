using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CompressedLeanMaterialTests
{
    [Fact]
    public void compressed_spool_roundtrip_accepted() => Run("equivalence");

    [Fact]
    public void input_spool_at_legacy_output_path_accepted() => Run("overlap");

    [Fact]
    public void changed_spool_never_published() => Run("changed");

    [Theory]
    [InlineData("truncated")]
    [InlineData("corruption")]
    public void CompressedSpoolsRejectInvalidInput(string mode) => Run(mode);

    private static void Run(string mode)
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-c", Probe, Path.Combine(root, "tools/lean-inspector/materials.py"), mode],
            root, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    private const string Probe = """
        import copy, gzip, hashlib, importlib.util, json, pathlib, subprocess, sys, tempfile
        script, mode = pathlib.Path(sys.argv[1]), sys.argv[2]
        spec = importlib.util.spec_from_file_location('materials', script)
        materials = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(materials)
        values = ['statement-v1(α,😀)'.encode(), b'statement-v1(' + b'payload,' * 20000 + b')']
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            manifest = root / "lean-report-inputs.json"
            manifest.write_text(json.dumps({"report_semantic_version": 1}))
            compressed = root / ('compressed.json.materials' if mode == 'overlap' else 'compressed')
            framed = b''.join(str(len(v)).encode() + b'\n' + v for v in values) + b'done\n'
            if mode == 'truncated':
                result = subprocess.run([sys.executable, str(script), 'stream', str(compressed)],
                    input=b'10\nabc', capture_output=True)
                assert result.returncode != 0 and not list(compressed.iterdir())
                assert b'truncated material frame' in result.stderr
                sys.exit(0)
            result = subprocess.run([sys.executable, str(script), 'stream', str(compressed)],
                input=framed, capture_output=True)
            assert result.returncode == 0, result.stderr
            assert result.stdout == b'ok\nok\ndone\n'
            assert [gzip.decompress((compressed / f'{i}.statement.gz').read_bytes())
                for i in range(len(values))] == values
            base = {'schema': materials.SPOOL_SCHEMA, 'modules': [{
                'module': 'D5.Fixture', 'source_path': 'D5/Fixture.lean',
                'source_sha256': 'sha256:' + 'a' * 64, 'imports': [],
                'declarations': [{'axioms': [], 'generated_companion': False, 'include_in_statement': True, 'kind': 'def',
                    'material_file': f'{i}.statement.gz', 'name': f'Fixture.value{i}',
                    'name_key': f'key{i}'} for i in range(len(values))]}]}
            source = root / 'spool.json'
            source.write_text(json.dumps(base))
            if mode == 'corruption':
                (compressed / '0.statement.gz').write_bytes(b'invalid gzip')
                result = subprocess.run([sys.executable, str(script), 'compact', str(source),
                    str(compressed), str(root / 'rejected.json'), str(manifest)], capture_output=True)
                assert result.returncode != 0
                assert not (root / 'rejected.json').exists()
                sys.exit(0)
            if mode == 'changed':
                original = materials.open_material
                calls = {}
                def change_on_archive(path):
                    calls[path] = calls.get(path, 0) + 1
                    if calls[path] == 2:
                        path.write_bytes(gzip.compress(b'changed material', mtime=0))
                    return original(path)
                materials.open_material = change_on_archive
                try:
                    materials.compact(source, compressed, root / 'rejected.json', manifest)
                except ValueError as error:
                    assert str(error) == 'statement material changed during compaction'
                else:
                    raise AssertionError('[FAIL] changed_spool_never_published')
                assert not (root / 'rejected.json').exists()
                assert not (root / 'rejected.json.materials.zip').exists()
                sys.exit(0)
            plain = root / 'plain'
            plain.mkdir()
            legacy = copy.deepcopy(base)
            for i, value in enumerate(values):
                (plain / f'{i}.statement').write_bytes(value)
                legacy['modules'][0]['declarations'][i]['material_file'] = f'{i}.statement'
            legacy_source = root / 'legacy.json'
            legacy_source.write_text(json.dumps(legacy))
            materials.compact(legacy_source, plain, root / 'plain.json', manifest)
            materials.compact(source, compressed, root / 'compressed.json', manifest)
            for suffix in ('', '.materials.zip'):
                assert (root / ('plain.json' + suffix)).read_bytes() == (root / ('compressed.json' + suffix)).read_bytes()
            # Byte identities measured with the pre-compression compactor at 1630e64b0b.
            assert hashlib.sha256((root / 'plain.json').read_bytes()).hexdigest() == 'fbde2eefbe685a3f4492fc85d1e2257456e3461fa9dac918c7a013a96356cb33'
            assert hashlib.sha256((root / 'plain.json.materials.zip').read_bytes()).hexdigest() == '3645dbf13d606a04f63ffb5704fab99ffcab588dd458f8e30540bee548f2416d'
            assert not list(plain.iterdir())
            assert not compressed.exists() if mode == 'overlap' else not list(compressed.iterdir())
        """;
}
