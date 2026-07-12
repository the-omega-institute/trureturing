using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void LedgerGenesisCommandWritesOnceAndRepeatsByteIdentically()
    {
        const string path = "D5/S0/Carrier/A.lean";
        const string source = "theorem a : True := by trivial\n";
        const string toolchain = "leanprover/lean4:v4.24.0\n";
        const string manifest = "{}\n";
        var revision = new string('a', 40);
        var raw = Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [path] = source,
            ["lean-toolchain"] = toolchain,
            ["lake-manifest.json"] = manifest,
        });
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [path] = new LeanFileReport(
                ImmutableArray<string>.Empty,
                ImmutableArray.Create(new LeanDeclaration(
                    "a",
                    "theorem",
                    "True",
                    ImmutableArray<string>.Empty))),
        });
        using var temporary = new TemporaryDirectory();
        var canonicalWriterPath = Path.Combine(
            temporary.Path,
            "Meta",
            "StrataLint",
            "StrataLint.Engine",
            "Ledger",
            "FrozenLedgerCanonicalWriter.cs");
        var generatorPath = Path.Combine(
            temporary.Path,
            "Meta",
            "StrataLint",
            "StrataLint.Cli",
            "Commands",
            "DagLedgerGenesisWriter.cs");
        Directory.CreateDirectory(Path.GetDirectoryName(canonicalWriterPath)!);
        Directory.CreateDirectory(Path.GetDirectoryName(generatorPath)!);
        File.WriteAllText(canonicalWriterPath, "// canonical writer fixture\n", new UTF8Encoding(false));
        File.WriteAllText(generatorPath, "// generator entrypoint fixture\n", new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), raw, raw),
            new FakeLeanReportSource(report));

        var first = environment.GenerateLedger(new[] { "--revision", revision });
        var ledgerPath = Path.Combine(
            temporary.Path,
            FrozenLedgerChangeClassifier.LedgerPath.Replace('/', Path.DirectorySeparatorChar));
        var firstBytes = File.ReadAllBytes(ledgerPath);
        var second = environment.GenerateLedger(new[] { "--revision", revision });

        Assert.True(first.Success, first.Error);
        Assert.True(second.Success, second.Error);
        Assert.Equal(firstBytes, File.ReadAllBytes(ledgerPath));
        Assert.Contains("events=2", first.Output, StringComparison.Ordinal);
        Assert.Contains("closed_modules=1", first.Output, StringComparison.Ordinal);
        var genesis = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(firstBytes)).Syntax.Lines[0].Value.GetProperty("payload");
        Assert.Equal(
            FrozenLedgerTestData.GitBlobOid("// generator entrypoint fixture\n"),
            genesis.GetProperty("generator_blob_oid").GetString());
    }
}
