using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LedgerSyncCommandTests
{
    [Fact]
    public void ProductionCommandReattestsThenFreezesInOneTransaction()
    {
        using var fixture = new LedgerSyncFixture(blobChanged: true, addClosedModule: true);
        var baselineLines = FrozenLedgerTestData.Lines(fixture.BaselineBytes);

        var (exitCode, console) = Run(fixture, "ledger-sync");

        Assert.Equal(0, exitCode);
        Assert.Equal(string.Empty, console.Error);
        Assert.Contains("appended_reattests=1", console.Output, StringComparison.Ordinal);
        Assert.Contains("appended_freezes=1", console.Output, StringComparison.Ordinal);
        var appendedBytes = ImmutableArray.CreateRange(
            FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
        var appendedLines = FrozenLedgerTestData.Lines(appendedBytes);
        Assert.Equal(baselineLines.Length + 2, appendedLines.Length);
        for (var index = 0; index < baselineLines.Length; index++)
        {
            Assert.Equal(baselineLines[index], appendedLines[index]);
        }

        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(appendedBytes.AsSpan())).Syntax;
        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedgerTestData.ValidateHistory(syntax, fixture.CandidateCatalog)).Capability;
        Assert.IsType<FrozenLedgerEvent.Reattest>(accepted.Events[^2]);
        Assert.IsType<FrozenLedgerEvent.Freeze>(accepted.Events[^1]);
    }

    [Fact]
    public void ProductionCommandRejectsStatementChangesWithoutWriting()
    {
        using var fixture = new LedgerSyncFixture(
            blobChanged: true,
            addClosedModule: true,
            candidateStatement: "False");

        var (exitCode, console) = Run(fixture, "ledger-sync");

        Assert.Equal(2, exitCode);
        Assert.Contains("statement identity changed", console.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(
            fixture.BaselineBytes.AsSpan().ToArray(),
            FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }

    [Fact]
    public void ProductionCommandIsIdempotentWhenLedgerAlreadyMatchesCatalog()
    {
        using var fixture = new LedgerSyncFixture(blobChanged: false, addClosedModule: false);

        var (exitCode, console) = Run(fixture, "ledger-sync");

        Assert.Equal(0, exitCode);
        Assert.Contains("no ledger changes", console.Output, StringComparison.Ordinal);
        Assert.Equal(
            fixture.BaselineBytes.AsSpan().ToArray(),
            FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }

    [Fact]
    public void ProductionCommandMatchesLedgerAppendWhenOnlyFreezesAreMissing()
    {
        using var syncFixture = new LedgerSyncFixture(blobChanged: false, addClosedModule: true);
        using var appendFixture = new LedgerSyncFixture(blobChanged: false, addClosedModule: true);

        var (exitCode, console) = Run(syncFixture, "ledger-sync");
        var append = appendFixture.Environment.AppendLedger(
            new[] { "--candidate-lean-report", appendFixture.ReportPath });

        Assert.Equal(0, exitCode);
        Assert.Equal(string.Empty, console.Error);
        Assert.True(append.Success, append.Error);
        Assert.Equal(
            FrozenLedgerTestData.ReadLedgerDirectory(appendFixture.LedgerPath),
            FrozenLedgerTestData.ReadLedgerDirectory(syncFixture.LedgerPath));
    }

    [Fact]
    public void ProductionCommandMatchesLedgerReattestWhenOnlyBlobsChanged()
    {
        using var syncFixture = new LedgerSyncFixture(blobChanged: true, addClosedModule: false);
        using var reattestFixture = new LedgerSyncFixture(blobChanged: true, addClosedModule: false);

        var (exitCode, console) = Run(syncFixture, "ledger-sync");
        var reattest = reattestFixture.Environment.ReattestLedger(
            new[] { "--candidate-lean-report", reattestFixture.ReportPath });

        Assert.Equal(0, exitCode);
        Assert.Equal(string.Empty, console.Error);
        Assert.True(reattest.Success, reattest.Error);
        Assert.Equal(
            FrozenLedgerTestData.ReadLedgerDirectory(reattestFixture.LedgerPath),
            FrozenLedgerTestData.ReadLedgerDirectory(syncFixture.LedgerPath));
    }

    private static (int ExitCode, BufferedConsole Console) Run(
        LedgerSyncFixture fixture,
        string command)
    {
        var console = new BufferedConsole();
        var exitCode = CliApplication.Run(
            new[] { command, "--candidate-lean-report", fixture.ReportPath },
            fixture.Environment,
            console);
        return (exitCode, console);
    }

    private sealed class LedgerSyncFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();

        internal LedgerSyncFixture(
            bool blobChanged,
            bool addClosedModule,
            string candidateStatement = "True")
        {
            const string originalSource = "theorem a : True := by trivial\n";
            var candidateSource = blobChanged
                ? $"-- canonical header changed\ntheorem a : {candidateStatement} := by trivial\n"
                : originalSource;
            var original = FrozenLedgerTestData.ModuleWithReport(
                "A",
                originalSource,
                "True");
            var added = FrozenLedgerTestData.Module("B", imports: new[] { "A" });
            var baselineCatalog = FrozenLedgerTestData.BuildCatalog(original);
            CandidateCatalog = addClosedModule
                ? FrozenLedgerTestData.BuildCatalog(
                    original with { Source = candidateSource, StatementMaterial = candidateStatement },
                    added)
                : FrozenLedgerTestData.BuildCatalog(
                    original with { Source = candidateSource, StatementMaterial = candidateStatement });
            BaselineBytes = FrozenLedgerGenerator.GenerateGenesis(
                baselineCatalog,
                new FrozenGenesisDescriptor(
                    FrozenLedgerTestData.GitOid('e'),
                    FrozenLedgerTestData.Sha256("historical-rule-catalog")));

            var files = new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["lean-toolchain"] = "leanprover/lean4:v4.24.0\n",
                ["lake-manifest.json"] = "{}\n",
                [FrozenLedgerTestData.PathFor("A")] = candidateSource,
            };
            var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                [FrozenLedgerTestData.PathFor("A")] = Report("A", candidateStatement),
            };
            if (addClosedModule)
            {
                files.Add(FrozenLedgerTestData.PathFor("B"), added.Source);
                reports.Add(FrozenLedgerTestData.PathFor("B"), Report("B", "True", "A"));
            }

            FrozenLedgerTestData.AddLedgerFiles(files, BaselineBytes);
            var raw = RawRepositorySnapshot.Create(
                files.Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(raw)).Snapshot;
            var report = LeanAxiomReport.Create(reports);

            LedgerPath = Path.Combine(
                temporary.Path,
                FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));
            FrozenLedgerTestData.WriteLedgerDirectory(LedgerPath, BaselineBytes);
            ReportPath = Path.Combine(temporary.Path, "candidate-lean-report.json");
            File.WriteAllBytes(ReportPath, RawLeanReportArtifact.Write(snapshot, report).AsSpan());
            Environment = new ProductionCliEnvironment(
                temporary.Path,
                new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null),
                new FakeLeanReportSource(null));
        }

        internal ImmutableArray<byte> BaselineBytes { get; }

        internal FrozenMaterialCatalog CandidateCatalog { get; }

        internal ProductionCliEnvironment Environment { get; }

        internal string LedgerPath { get; }

        internal string ReportPath { get; }

        public void Dispose() => temporary.Dispose();

        private static LeanFileReport Report(
            string name,
            string statement,
            params string[] imports) => new(
            imports.Select(static item => $"D5.S0.Carrier.{item}").ToImmutableArray(),
            ImmutableArray.Create(new LeanDeclaration(
                name.ToLowerInvariant(),
                "theorem",
                statement,
                ImmutableArray<string>.Empty)
            {
                NameKey = $"ns(n0,{name.Length}:{name.ToLowerInvariant()})",
            }));
    }
}
