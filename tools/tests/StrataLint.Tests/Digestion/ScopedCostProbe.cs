using System.Text;
using Xunit.Abstractions;

namespace StrataLint.Tests;

public sealed class ScopedCostProbe(ITestOutputHelper output)
{
    [Fact]
    public void InstalledSourceSelectionHasMatchingProjectionAndMeasuredReadCost()
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-c", Probe, root, "--source", "mub-six-fourth-basis-theory",
                "--atom", "0439f0bb1ea28d31c1e85be80a1c5148c13e9e11fd9d369d6ff987f9a00a2055"],
            root, TestBudgets.LeanProcessHangGuard, 1024 * 1024);
        var stdout = Encoding.UTF8.GetString(result.StandardOutput);
        var stderr = Encoding.UTF8.GetString(result.StandardError);
        output.WriteLine(stdout);
        Assert.True(result.ExitCode == 0, stdout + stderr);
        Assert.Contains("SCOPED_COST_PROJECTION_MATCH target=true search=true ledger_reads_in_search=0 text_limit_cas_reads=1", stdout, StringComparison.Ordinal);
    }

    private const string Probe = """"
        import argparse
        import hashlib
        import json
        import os
        import pathlib
        import shutil
        import subprocess
        import tempfile
        import xml.sax.saxutils
        
        parser = argparse.ArgumentParser()
        parser.add_argument('root', type=pathlib.Path)
        parser.add_argument('--source', required=True)
        parser.add_argument('--atom', required=True)
        options = parser.parse_args()
        root = options.root.resolve(strict=True)
        cli = root / 'tools/StrataLint.Cli/bin/Release/net10.0'
        scratch = pathlib.Path(tempfile.mkdtemp(prefix='digestion-scoped-cost-', dir=os.environ.get('RUNNER_TEMP')))
        code = r'''
        using System.Diagnostics;
        using System.Security.Cryptography;
        using System.Text.Json;
        using StrataLint.Cli;
        using StrataLint.Engine;
        
        var root = args[0]; var source = args[1]; var atom = args[2]; var mode = args[3]; var text = args[4];
        var gateway = new MeasuredGateway(new GitRepositoryGateway(root));
        var before = GC.GetTotalAllocatedBytes(true);
        var started = Stopwatch.GetTimestamp();
        string projection;
        if (mode is "full-reference" or "scoped")
        {
            var loaded = mode == "scoped"
                ? DigestionQuerySelection.ReadAtom(gateway, atom, [source])
                : DigestionQuerySelection.Load(gateway.ReadCurrent([BackfillInventoryLoader.RootPath.TrimEnd('/')]));
            var target = loaded.Document.RequireDigestionEntries().Single(entry => entry.SourceId == source && entry.AtomId == atom);
            projection = JsonSerializer.Serialize(target);
        }
        else
        {
            var arguments = mode == "search-text"
                ? new[] { "--source", source, "--text", text, "--limit", "1" }
                : new[] { "--source", source, "--limit", "1" };
            var result = SearchAtomsCommand.Run(gateway, arguments);
            if (!result.Success || string.IsNullOrEmpty(result.Output)) throw new Exception(result.Error);
            projection = result.Output;
        }
        var seconds = Stopwatch.GetElapsedTime(started).TotalSeconds;
        var allocated = GC.GetTotalAllocatedBytes(true) - before;
        Console.WriteLine("SCOPED_COST " + JsonSerializer.Serialize(new {
            mode, seconds, allocated, gateway.BodyFiles, gateway.BodyBytes,
            gateway.LedgerRecords, gateway.CasFiles, gateway.CasBytes, gateway.SearchPaths,
            digest = Convert.ToHexStringLower(SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(projection))),
            peak_rss_bytes = Process.GetCurrentProcess().PeakWorkingSet64 is > 0 and var rss ? (long?)rss : null
        }));
        
        sealed class MeasuredGateway(IRepositoryGateway inner) : IRepositoryGateway
        {
            public long BodyFiles; public long BodyBytes; public long LedgerRecords;
            public long CasFiles; public long CasBytes; public long SearchPaths;
            public RawRepositorySnapshot ReadCurrent(IReadOnlyList<string> paths)
            {
                var raw = inner.ReadCurrent(paths);
                foreach (var entry in raw.Entries)
                {
                    BodyFiles++; BodyBytes += entry.Bytes.Length;
                    if (entry.Path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)
                        && entry.Path.EndsWith(".yaml", StringComparison.Ordinal)) LedgerRecords++;
                    if (entry.Path.StartsWith(DigestionCasStore.RootPath, StringComparison.Ordinal))
                    { CasFiles++; CasBytes += entry.Bytes.Length; }
                }
                return raw;
            }
            public IReadOnlyList<string> SearchCurrentPaths(IReadOnlyList<string> paths)
            { var result = inner.SearchCurrentPaths(paths); SearchPaths += result.Count; return result; }
            public RawRepositorySnapshot ReadCurrent() => throw new Exception("whole tree not requested by this probe");
            public AdmissionTopologyOutcome InspectAdmissionTopology() => throw new NotSupportedException();
            public PreparedRepository Prepare(string? baseline) => throw new NotSupportedException();
            public FrozenRevisionIdentity ResolveCurrentRevision() => inner.ResolveCurrentRevision();
            public RawRepositorySnapshot ReadRevision(string revision) => throw new NotSupportedException();
            public RawChangeSet ReadCurrentChanges() => throw new NotSupportedException();
            public RawChangeSet ReadChanges(string revision) => throw new NotSupportedException();
        }
        '''
        try:
            (scratch / 'Program.cs').write_text(code)
            references = ''.join('<Reference Include="' + p.stem + '"><HintPath>'
                                 + xml.sax.saxutils.escape(str(p)) + '</HintPath></Reference>' for p in cli.glob('*.dll'))
            (scratch / 'Probe.csproj').write_text('<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup>'
                '<TargetFramework>net10.0</TargetFramework><OutputType>Exe</OutputType>'
                '<AssemblyName>StrataLint.Tests</AssemblyName><ImplicitUsings>enable</ImplicitUsings>'
                '<Nullable>enable</Nullable></PropertyGroup><ItemGroup>' + references + '</ItemGroup></Project>')
            subprocess.run(['dotnet', 'build', str(scratch / 'Probe.csproj'), '-c', 'Release', '-nologo'], check=True)
            program = scratch / 'bin/Release/net10.0/StrataLint.Tests.dll'
            results = []
            stored_text = (root / 'Meta/Digestion/atoms/sha256' / options.atom).read_text()
            text = stored_text.split()[0]
            for mode in ['full-reference', 'scoped', 'scoped', 'full-reference', 'search-paths', 'search-text']:
                output = subprocess.check_output(['dotnet', str(program), str(root), options.source, options.atom, mode, text], text=True)
                print(output, end='', flush=True)
                result = json.loads(output.removeprefix('SCOPED_COST '))
                results.append(result)
            assert len({r['digest'] for r in results if r['mode'] in ['full-reference', 'scoped']}) == 1
            search = {r['mode']: r for r in results if r['mode'].startswith('search-')}
            assert search['search-paths']['LedgerRecords'] == 0 and search['search-paths']['CasFiles'] == 0
            assert search['search-text']['LedgerRecords'] == 0 and search['search-text']['CasFiles'] == 1
            assert search['search-paths']['digest'] == search['search-text']['digest']
            print('SCOPED_COST_PROJECTION_MATCH target=true search=true ledger_reads_in_search=0 text_limit_cas_reads=1', flush=True)
            print('SCOPED_COST_INPUT ' + json.dumps({'source': options.source, 'atom': options.atom,
                'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
                'assembly_sha256': hashlib.sha256((cli / 'StrataLint.dll').read_bytes()).hexdigest(),
                'cas_sha256': hashlib.sha256(stored_text.encode()).hexdigest(), 'text': text}), flush=True)
        finally:
            shutil.rmtree(scratch)
        """";
}
