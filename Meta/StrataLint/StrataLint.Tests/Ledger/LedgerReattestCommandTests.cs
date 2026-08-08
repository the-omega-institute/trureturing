using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LedgerReattestCommandTests
{
    [Fact]
    public void RootUsageListsLedgerReattestCommand()
    {
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            Array.Empty<string>(),
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("ledger-reattest", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void LedgerReattestVerbDispatchesToTheEnvironment()
    {
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            new[] { "ledger-reattest", "--candidate-lean-report", "report.json" },
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("ledger reattest is not configured", console.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("UNKNOWN_COMMAND", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionCommandReattestsCommentOnlyBlobChangesWithoutRewritingHistory()
    {
        using var fixture = new LedgerReattestFixture("True");
        var baselineLines = FrozenLedgerTestData.Lines(fixture.BaselineBytes);

        var result = fixture.Environment.ReattestLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.True(result.Success, result.Error);
        Assert.Contains("appended_reattests=1", result.Output, StringComparison.Ordinal);
        var appendedBytes = ImmutableArray.CreateRange(
            FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
        var appendedLines = FrozenLedgerTestData.Lines(appendedBytes);
        Assert.Equal(baselineLines.Length + 1, appendedLines.Length);
        for (var index = 0; index < baselineLines.Length; index++)
        {
            Assert.Equal(baselineLines[index], appendedLines[index]);
        }

        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(appendedBytes.AsSpan())).Syntax;
        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedgerTestData.ValidateHistory(syntax, fixture.CandidateCatalog)).Capability;
        Assert.IsType<FrozenLedgerEvent.Reattest>(accepted.Events[^1]);
        var baselineStatement = fixture.BaselineCatalog.ClosedNodes.Single().StatementId;
        Assert.Equal(baselineStatement, accepted.ActiveFrozenNodes.Single().StatementId);
    }

    [Fact]
    public void ProductionCommandIsIdempotentAfterReattestation()
    {
        using var fixture = new LedgerReattestFixture("True");
        var arguments = new[] { "--candidate-lean-report", fixture.ReportPath };
        var first = fixture.Environment.ReattestLedger(arguments);
        Assert.True(first.Success, first.Error);
        var firstBytes = FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath);

        var second = fixture.Environment.ReattestLedger(arguments);

        Assert.True(second.Success, second.Error);
        Assert.Contains("no changed frozen modules", second.Output, StringComparison.Ordinal);
        Assert.Equal(firstBytes, FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }

    [Fact]
    public void ProductionCommandRejectsStatementChangesWithoutWriting()
    {
        using var fixture = new LedgerReattestFixture("False");

        var result = fixture.Environment.ReattestLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.False(result.Success);
        Assert.Contains("statement identity changed", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(
            fixture.BaselineBytes.AsSpan().ToArray(),
            FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }

    /// The preparation step marks an unusable raw report with its own exception type. Drop that
    /// type from this command's catch list and the failure escapes with no LEDGER_REATTEST_FAILED
    /// diagnostic at all -- which is exactly how a real contract break went unnoticed here.
    [Fact]
    public void ProductionCommandKeepsItsDiagnosticWhenTheReportCannotBeLoaded()
    {
        using var fixture = new LedgerReattestFixture("True");
        File.WriteAllText(fixture.ReportPath, "this is not a raw Lean report");

        var result = fixture.Environment.ReattestLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.False(result.Success, result.Output);
        Assert.StartsWith("LEDGER_REATTEST_FAILED ", result.Error, StringComparison.Ordinal);
        // The marker's own message says only "raw Lean report is unusable". Reporting that instead
        // of the cause would silently drop the diagnostic this command had before the marker existed.
        Assert.Contains("Raw Lean report is not valid JSON.", result.Error, StringComparison.Ordinal);
    }

    /// The gateway is asked before the report is read, so this reaches the other marker type and
    /// no other. Orthogonal to the report case above: neither mutant kills both tests.
    [Fact]
    public void ProductionCommandKeepsItsDiagnosticWhenTheRepositoryCannotBeRead()
    {
        using var fixture = new LedgerReattestFixture("True");
        var environment = new ProductionCliEnvironment(
            fixture.Root,
            new FakeRepositoryGateway(RawChangeSet.Create([]), null, null),
            new FakeLeanReportSource(null));

        var result = environment.ReattestLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.False(result.Success, result.Output);
        Assert.StartsWith("LEDGER_REATTEST_FAILED ", result.Error, StringComparison.Ordinal);
        Assert.Contains("current snapshot should not be read", result.Error, StringComparison.Ordinal);
    }

    private sealed class LedgerReattestFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();

        internal LedgerReattestFixture(string candidateStatement)
        {
            const string originalSource = "theorem a : True := by trivial\n";
            var candidateSource = "-- canonical header changed\n"
                + $"theorem a : {candidateStatement} := by trivial\n";
            var original = FrozenLedgerTestData.Module("A", source: originalSource);
            BaselineCatalog = FrozenLedgerTestData.BuildCatalog(original);
            BaselineBytes = FrozenLedgerGenerator.GenerateGenesis(
                BaselineCatalog,
                new FrozenGenesisDescriptor(
                    FrozenLedgerTestData.GitOid('e'),
                    FrozenLedgerTestData.Sha256("historical-rule-catalog")));

            var files = new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["lean-toolchain"] = "leanprover/lean4:v4.24.0\n",
                ["lake-manifest.json"] = "{}\n",
                [FrozenLedgerTestData.PathFor("A")] = candidateSource,
            };
            FrozenLedgerTestData.AddLedgerFiles(files, BaselineBytes);
            var raw = RawRepositorySnapshot.Create(
                files.Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(raw)).Snapshot;
            var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                [FrozenLedgerTestData.PathFor("A")] = new(
                    ImmutableArray<string>.Empty,
                    ImmutableArray.Create(new LeanDeclaration(
                        "a",
                        "theorem",
                        candidateStatement,
                        ImmutableArray<string>.Empty)
                    {
                        NameKey = "ns(n0,1:a)",
                    })),
            });

            LedgerPath = Path.Combine(
                temporary.Path,
                FrozenLedgerChangeClassifier.LedgerPath.Replace('/', Path.DirectorySeparatorChar));
            FrozenLedgerTestData.WriteLedgerDirectory(LedgerPath, BaselineBytes);
            ReportPath = Path.Combine(temporary.Path, "candidate-lean-report.json");
            File.WriteAllBytes(ReportPath, RawLeanReportArtifact.Write(snapshot, report).AsSpan());
            Environment = new ProductionCliEnvironment(
                temporary.Path,
                new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null),
                new FakeLeanReportSource(null));
            CandidateCatalog = BuildCandidateCatalog(candidateSource, candidateStatement);
        }

        internal ImmutableArray<byte> BaselineBytes { get; }

        internal FrozenMaterialCatalog BaselineCatalog { get; }

        internal FrozenMaterialCatalog CandidateCatalog { get; }

        internal ProductionCliEnvironment Environment { get; }

        internal string LedgerPath { get; }

        internal string ReportPath { get; }

        internal string Root => temporary.Path;

        public void Dispose() => temporary.Dispose();

        private static FrozenMaterialCatalog BuildCandidateCatalog(
            string candidateSource,
            string candidateStatement)
        {
            var files = new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["lean-toolchain"] = "leanprover/lean4:v4.24.0\n",
                ["lake-manifest.json"] = "{}\n",
                [FrozenLedgerTestData.PathFor("A")] = candidateSource,
            };
            var raw = RawRepositorySnapshot.Create(
                files.Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(raw)).Snapshot;
            var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                [FrozenLedgerTestData.PathFor("A")] = new(
                    ImmutableArray<string>.Empty,
                    ImmutableArray.Create(new LeanDeclaration(
                        "a",
                        "theorem",
                        candidateStatement,
                        ImmutableArray<string>.Empty)
                    {
                        NameKey = "ns(n0,1:a)",
                    })),
            });
            var closure = Assert.IsType<LeanValidationOutcome.Accepted>(
                LeanClosureValidator.Validate(snapshot, report)).Capability;
            var dag = Assert.IsType<DagBuildOutcome.Accepted>(
                AcyclicTruthDag.Build(snapshot, closure)).Capability;
            var environment = new FrozenEnvironmentAttestation(
                FrozenLedgerTestData.GitOid('a'),
                FrozenLedgerTestData.GitOid('b'),
                FrozenLedgerTestData.GitBlobOid(files["lean-toolchain"]),
                FrozenLedgerTestData.GitBlobOid(files["lake-manifest.json"]));
            return Assert.IsType<FrozenMaterialOutcome.Accepted>(
                FrozenContentAddress.Build(
                    snapshot,
                    closure,
                    dag,
                    environment,
                    new[]
                    {
                        new FrozenModuleAttestation(
                            FrozenLedgerTestData.RepoPathFor("A"),
                            FrozenLedgerTestData.GitBlobOid(candidateSource)),
                    })).Capability;
        }
    }
}
