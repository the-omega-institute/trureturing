using System.Text;
using System.Text.Json;

namespace StrataLint.Tests;

public sealed class ScopedCostProbe
{
    private sealed record Result(JsonElement[] Rows, JsonElement Input);
    private static readonly Lazy<Result> Measurement = new(ReadMeasurements);

    [Theory]
    [MemberData(nameof(CostRows))]
    public void InstalledSourceCost(int row, string mode, long ledgerRecords, long casFiles,
        long bodyBytes, long allocatedBytes, double seconds, long? peakRssBytes,
        long bodyFiles, long casBytes, long searchPaths)
    {
        Assert.InRange(row, 1, 6);
        Assert.Contains(mode, new[] { "full-reference", "scoped", "search-paths", "search-text" });
        Assert.True(double.IsFinite(seconds) && seconds >= 0);
        Assert.True(allocatedBytes >= 0 && bodyBytes >= 0 && bodyFiles >= 0 && casBytes >= 0 && searchPaths >= 0);
        Assert.True(peakRssBytes is null or > 0);
        if (mode == "scoped") Assert.Equal(1, ledgerRecords);
        if (mode.StartsWith("search-", StringComparison.Ordinal)) Assert.Equal(0, ledgerRecords);
        Assert.Equal(mode == "search-text" ? 1 : 0, casFiles);
    }

    [Theory]
    [MemberData(nameof(InputRows))]
    public void InstalledSourceInput(string field, int part, string value)
    {
        Assert.True(part >= 0);
        Assert.False(string.IsNullOrWhiteSpace(field));
        Assert.False(string.IsNullOrWhiteSpace(value));
    }

    public static IEnumerable<object?[]> CostRows()
    {
        var index = 0;
        foreach (var row in Measurement.Value.Rows)
            yield return [++index, row.GetProperty("mode").GetString(), row.GetProperty("LedgerRecords").GetInt64(),
                row.GetProperty("CasFiles").GetInt64(), row.GetProperty("BodyBytes").GetInt64(),
                row.GetProperty("allocated").GetInt64(), row.GetProperty("seconds").GetDouble(),
                row.GetProperty("peak_rss_bytes").ValueKind == JsonValueKind.Null ? null : row.GetProperty("peak_rss_bytes").GetInt64(),
                row.GetProperty("BodyFiles").GetInt64(), row.GetProperty("CasBytes").GetInt64(), row.GetProperty("SearchPaths").GetInt64()];
    }

    public static IEnumerable<object?[]> InputRows()
    {
        foreach (var property in Measurement.Value.Input.EnumerateObject())
        {
            var value = property.Value.GetString()!;
            for (var offset = 0; offset < value.Length; offset += 32)
                yield return [property.Name, offset / 32, value.Substring(offset, Math.Min(32, value.Length - offset))];
        }
        foreach (var group in Measurement.Value.Rows.GroupBy(row => row.GetProperty("mode").GetString()))
        {
            var digest = group.First().GetProperty("digest").GetString()!;
            yield return [group.Key + "_digest", 0, digest[..32]];
            yield return [group.Key + "_digest", 1, digest[32..]];
        }
    }

    private static Result ReadMeasurements()
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-c", Probe, root, "--source", "mub-six-fourth-basis-theory",
                "--atom", "0439f0bb1ea28d31c1e85be80a1c5148c13e9e11fd9d369d6ff987f9a00a2055"],
            root, TestBudgets.LeanProcessHangGuard, 1024 * 1024);
        var stdout = Encoding.UTF8.GetString(result.StandardOutput);
        var stderr = Encoding.UTF8.GetString(result.StandardError);
        Assert.True(result.ExitCode == 0, stdout + stderr);
        Assert.Contains("SCOPED_COST_PROJECTION_MATCH target=true search=true ledger_reads_in_search=0 text_limit_cas_reads=1", stdout, StringComparison.Ordinal);
        var lines = stdout.Split('\n');
        var rows = lines.Where(line => line.StartsWith("SCOPED_COST ", StringComparison.Ordinal))
            .Select(line => JsonDocument.Parse(line[12..]).RootElement.Clone()).ToArray();
        Assert.Equal(6, rows.Length);
        var inputLine = Assert.Single(lines, line => line.StartsWith("SCOPED_COST_INPUT ", StringComparison.Ordinal));
        var input = JsonDocument.Parse(inputLine[18..]).RootElement.Clone();
        Assert.Equal("mub-six-fourth-basis-theory", input.GetProperty("source").GetString());
        Assert.Equal(input.GetProperty("atom").GetString(), input.GetProperty("cas_sha256").GetString());
        Assert.Equal("###", input.GetProperty("text").GetString());
        return new Result(rows, input);
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
