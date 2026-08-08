using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LedgerAppendCommandTests
{
    [Fact]
    public void RootUsageListsLedgerAppendCommand()
    {
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            Array.Empty<string>(),
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("ledger-append", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void LedgerAppendVerbDispatchesToTheEnvironment()
    {
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            new[] { "ledger-append", "--candidate-lean-report", "report.json" },
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("ledger append is not configured", console.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("UNKNOWN_COMMAND", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionCommandAppendsEveryMissingFreezeWithoutRewritingTheBaseline()
    {
        using var fixture = new LedgerAppendFixture();
        var baselineLines = FrozenLedgerTestData.Lines(fixture.BaselineBytes);

        var result = fixture.Environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.True(result.Success, result.Error);
        Assert.Contains("appended_freezes=2", result.Output, StringComparison.Ordinal);
        var appendedBytes = FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath);
        var appendedLines = FrozenLedgerTestData.Lines(ImmutableArray.CreateRange(appendedBytes));
        Assert.Equal(baselineLines.Length + 2, appendedLines.Length);
        for (var index = 0; index < baselineLines.Length; index++)
        {
            Assert.Equal(baselineLines[index], appendedLines[index]);
        }

        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(appendedBytes)).Syntax;
        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedgerTestData.ValidateHistory(syntax, fixture.CandidateCatalog));
        Assert.Equal(3, accepted.Capability.ActiveFrozenNodes.Length);
        Assert.Equal(
            new[]
            {
                FrozenLedgerTestData.PathFor("B"),
                FrozenLedgerTestData.PathFor("C"),
            },
            accepted.Capability.Events
                .OfType<FrozenLedgerEvent.Freeze>()
                .Skip(1)
                .Select(static item => item.Payload.NodePath.Value)
                .Order(StringComparer.Ordinal));
    }

    [Fact]
    public void ProductionCommandReportsNoMissingFreezesWithoutWritingAgain()
    {
        using var fixture = new LedgerAppendFixture();
        var first = fixture.Environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });
        Assert.True(first.Success, first.Error);
        var appendedBytes = FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath);

        var second = fixture.Environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.True(second.Success, second.Error);
        Assert.Contains("no missing freezes", second.Output, StringComparison.Ordinal);
        Assert.Equal(appendedBytes, FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }

    /// The preparation step marks an unusable raw report with its own exception type. Drop that
    /// type from this command's catch list and the failure escapes with no LEDGER_APPEND_FAILED
    /// diagnostic at all -- which is exactly how a real contract break went unnoticed here.
    [Fact]
    public void ProductionCommandKeepsItsDiagnosticWhenTheReportCannotBeLoaded()
    {
        using var fixture = new LedgerAppendFixture();
        File.WriteAllText(fixture.ReportPath, "this is not a raw Lean report");

        var result = fixture.Environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.False(result.Success, result.Output);
        Assert.StartsWith("LEDGER_APPEND_FAILED ", result.Error, StringComparison.Ordinal);
        // The marker's own message says only "raw Lean report is unusable". Reporting that instead
        // of the cause would silently drop the diagnostic this command had before the marker existed.
        Assert.Contains("Raw Lean report is not valid JSON.", result.Error, StringComparison.Ordinal);
    }

    /// The gateway is asked before the report is read, so this reaches the other marker type and
    /// no other. Orthogonal to the report case above: neither mutant kills both tests.
    [Fact]
    public void ProductionCommandKeepsItsDiagnosticWhenTheRepositoryCannotBeRead()
    {
        using var fixture = new LedgerAppendFixture();
        var environment = new ProductionCliEnvironment(
            fixture.Root,
            new FakeRepositoryGateway(RawChangeSet.Create([]), null, null),
            new FakeLeanReportSource(null));

        var result = environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.False(result.Success, result.Output);
        Assert.StartsWith("LEDGER_APPEND_FAILED ", result.Error, StringComparison.Ordinal);
        Assert.Contains("current snapshot should not be read", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void PublicHistoryValidationStillRejectsAnIncompleteClosedCatalog()
    {
        using var fixture = new LedgerAppendFixture();
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(fixture.BaselineBytes.AsSpan())).Syntax;

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            FrozenLedgerTestData.ValidateHistory(syntax, fixture.CandidateCatalog));

        Assert.Contains("missing Freeze", rejected.Message, StringComparison.Ordinal);
    }

    private sealed class LedgerAppendFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();

        internal LedgerAppendFixture()
        {
            var a = FrozenLedgerTestData.Module("A");
            var b = FrozenLedgerTestData.Module("B", imports: new[] { "A" });
            var c = FrozenLedgerTestData.Module("C", imports: new[] { "B" });
            var baselineCatalog = FrozenLedgerTestData.BuildCatalog(a);
            CandidateCatalog = FrozenLedgerTestData.BuildCatalog(a, b, c);
            BaselineBytes = FrozenLedgerGenerator.GenerateGenesis(
                baselineCatalog,
                new FrozenGenesisDescriptor(
                    FrozenLedgerTestData.GitOid('e'),
                    RuleCatalog.Default.RootSha256));

            var files = new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["lean-toolchain"] = "leanprover/lean4:v4.24.0\n",
                ["lake-manifest.json"] = "{}\n",
                [FrozenLedgerTestData.PathFor("A")] = a.Source,
                [FrozenLedgerTestData.PathFor("B")] = b.Source,
                [FrozenLedgerTestData.PathFor("C")] = c.Source,
            };
            FrozenLedgerTestData.AddLedgerFiles(files, BaselineBytes);
            var raw = RawRepositorySnapshot.Create(
                files.Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(raw)).Snapshot;
            var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                [FrozenLedgerTestData.PathFor("A")] = Report("A"),
                [FrozenLedgerTestData.PathFor("B")] = Report("B", "A"),
                [FrozenLedgerTestData.PathFor("C")] = Report("C", "B"),
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
        }

        internal ImmutableArray<byte> BaselineBytes { get; }

        internal FrozenMaterialCatalog CandidateCatalog { get; }

        internal ProductionCliEnvironment Environment { get; }

        internal string LedgerPath { get; }

        internal string ReportPath { get; }

        internal string Root => temporary.Path;

        public void Dispose() => temporary.Dispose();

        private static LeanFileReport Report(string name, params string[] imports) => new(
            imports.Select(static item => $"D5.S0.Carrier.{item}").ToImmutableArray(),
            ImmutableArray.Create(new LeanDeclaration(
                name.ToLowerInvariant(),
                "theorem",
                "True",
                ImmutableArray<string>.Empty)
            {
                NameKey = $"ns(n0,{name.Length}:{name.ToLowerInvariant()})",
            }));
    }
}
