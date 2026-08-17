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
        Assert.Contains("appended_reattests=0", result.Output, StringComparison.Ordinal);
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
    public void ProductionCommandWithOneAppendValidatesOnlyTheSuffixOids()
    {
        using var fixture = new LedgerAppendFixture(
            addSecondClosedModule: false,
            historicalReattest: true);
        var preparation = DagLedgerCommandPreparation.Prepare(
            fixture.Root,
            fixture.Gateway,
            fixture.ReportPath);

        Assert.Equal(3, preparation.BaseView.EventCount);

        var result = fixture.Environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.True(result.Success, result.Error);
        Assert.Contains("appended_freezes=1", result.Output, StringComparison.Ordinal);
        var references = Assert.Single(fixture.Gateway.FrozenReferenceValidations);
        Assert.Single(references.Inputs);
        Assert.Equal(FrozenLedgerTestData.PathFor("B"), references.Inputs[0].DescriptorSelector);
        Assert.DoesNotContain(
            references.Inputs,
            static input => input.DescriptorSelector == FrozenLedgerTestData.PathFor("A"));
        Assert.Single(references.CommitOids);
        Assert.Single(references.TreeOids);
        Assert.Equal(3, references.BlobOids.Length);
    }

    [Fact]
    public void ProductionCommandDirectsExistingIdentityDriftToLedgerSyncWithoutWriting()
    {
        using var fixture = new LedgerAppendFixture(driftARepresentation: true);
        var result = fixture.Environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.False(result.Success, result.Output);
        Assert.Contains(FrozenLedgerTestData.PathFor("A"), result.Error, StringComparison.Ordinal);
        Assert.Contains("changed identity", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("ledger-sync", result.Error, StringComparison.Ordinal);
        Assert.Equal(
            fixture.BaselineBytes.AsSpan().ToArray(),
            FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }

    [Fact]
    public void WriterPreparationBuildsOnlyCandidateDeltaAndTrustsCommittedBaseIdentity()
    {
        using var fixture = new LedgerAppendFixture(currentAStatementMaterial: "False");

        var preparation = DagLedgerCommandPreparation.Prepare(
            fixture.Root,
            fixture.Gateway,
            fixture.ReportPath);

        Assert.Equal(
            new[] { FrozenLedgerTestData.PathFor("B"), FrozenLedgerTestData.PathFor("C") },
            preparation.Catalog.ClosedNodes.Select(static node => node.RepoPath.Value));

        var result = fixture.Environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.True(result.Success, result.Error);
        Assert.Contains("appended_freezes=2", result.Output, StringComparison.Ordinal);
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
        Assert.Contains("no catalog reconciliation required", second.Output, StringComparison.Ordinal);
        Assert.Contains("appended_reattests=0", second.Output, StringComparison.Ordinal);
        Assert.Contains("appended_freezes=0", second.Output, StringComparison.Ordinal);
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

    [Fact]
    public void WriteNewEventsRejectsABaselineChangedAfterTheEarlyRecheckWithoutWriting()
    {
        using var temporary = new TemporaryDirectory();
        var (baselineBytes, baseline, candidateCatalog) = ReconciliationFixture(includeNewModule: true);
        var candidateBytes = FrozenLedgerGenerator.AppendSynchronization(baseline, candidateCatalog);
        var candidateSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax;
        FrozenLedgerTestData.WriteLedgerDirectory(temporary.Path, baselineBytes);
        var expectedBaselineFiles = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(
            temporary.Path);
        Assert.True(DagLedgerCommandPreparation.LoadLedgerDirectory(
                temporary.Path,
                "early baseline recheck").RawBytes.AsSpan().SequenceEqual(baselineBytes.AsSpan()));

        const string competing = "-- competing representation\ntheorem a : True := by trivial\n";
        var competingCatalog = FrozenLedgerTestData.BuildCatalog(
            FrozenLedgerTestData.Module("A", source: competing),
            FrozenLedgerTestData.Module("C", imports: new[] { "A" }));
        var competingBytes = FrozenLedgerGenerator.AppendSynchronization(baseline, competingCatalog);
        var competingSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(competingBytes.AsSpan())).Syntax;
        DagLedgerAppendWriter.WriteNewEvents(
            temporary.Path,
            competingSyntax.Lines,
            baseline.Events.Length);
        var before = DirectorySnapshot(temporary.Path);

        var exception = Assert.Throws<InvalidOperationException>(() =>
            DagLedgerAppendWriter.WriteNewEvents(
                temporary.Path,
                candidateSyntax.Lines,
                baseline.Events.Length,
                expectedBaselineFiles: expectedBaselineFiles));

        Assert.Contains("accepted event files changed", exception.Message, StringComparison.Ordinal);
        var after = DirectorySnapshot(temporary.Path);
        Assert.Equal(before.Keys, after.Keys);
        Assert.All(before, item => Assert.Equal(item.Value, after[item.Key]));
        Assert.Empty(Directory.EnumerateDirectories(temporary.Path, ".ledger-stage-*"));
    }

    [Fact]
    public void PublicationLockBlocksASecondWriterAndProtectsItsStageUntilRelease()
    {
        using var temporary = new TemporaryDirectory();
        var lockPath = Path.Combine(temporary.Path, ".ledger-write.lock");
        var activeStage = Path.Combine(temporary.Path, ".ledger-stage-active");
        Directory.CreateDirectory(activeStage);
        File.WriteAllText(Path.Combine(activeStage, "pending.json"), "pending\n");

        using (DagLedgerAppendWriter.AcquirePublicationLock(lockPath))
        {
            var exception = Assert.Throws<IOException>(() => DagLedgerAppendWriter.WriteNewEvents(
                temporary.Path,
                Array.Empty<FrozenLedgerLineSyntax>()));

            Assert.Contains("owns the writer lock", exception.Message, StringComparison.Ordinal);
            Assert.True(Directory.Exists(activeStage));
        }

        DagLedgerAppendWriter.WriteNewEvents(
            temporary.Path,
            Array.Empty<FrozenLedgerLineSyntax>());

        Assert.False(Directory.Exists(activeStage));
    }

    [Fact]
    public void WriteNewEventsReapsStaleStagingDirectoriesBeforePlanning()
    {
        using var temporary = new TemporaryDirectory();
        var stale = Path.Combine(temporary.Path, ".ledger-stage-stale");
        Directory.CreateDirectory(stale);
        File.WriteAllText(Path.Combine(stale, "orphan.json"), "orphan\n");

        DagLedgerAppendWriter.WriteNewEvents(
            temporary.Path,
            Array.Empty<FrozenLedgerLineSyntax>());

        Assert.False(Directory.Exists(stale));
    }

    [Fact]
    public void RepositoryIgnoresLedgerPublicationScratchArtifacts()
    {
        var ignore = File.ReadAllLines(Path.Combine(TestRepositoryLayout.FindRoot(), ".gitignore"));

        Assert.Contains("/Golden/Frozen/accepted/.ledger-stage-*/", ignore);
        Assert.Contains("/Golden/Frozen/accepted/.ledger-write.lock", ignore);
    }

    private static (
        ImmutableArray<byte> BaselineBytes,
        FrozenLedgerConsistent Baseline,
        FrozenMaterialCatalog CandidateCatalog) ReconciliationFixture(bool includeNewModule)
    {
        const string original = "theorem a : True := by trivial\n";
        const string changed = "-- representation changed\ntheorem a : True := by trivial\n";
        var baselineCatalog = FrozenLedgerTestData.BuildCatalog(
            FrozenLedgerTestData.Module("A", source: original));
        var candidateModules = new List<FrozenLedgerTestData.ModuleSpec>
        {
            FrozenLedgerTestData.Module("A", source: changed),
        };
        if (includeNewModule)
        {
            candidateModules.Add(FrozenLedgerTestData.Module("B", imports: new[] { "A" }));
        }

        var candidateCatalog = FrozenLedgerTestData.BuildCatalog(candidateModules.ToArray());
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            baselineCatalog,
            new FrozenGenesisDescriptor(
                FrozenLedgerTestData.GitOid('e'),
                RuleCatalog.Default.RootSha256));
        var baselineSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(baselineBytes.AsSpan())).Syntax;
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedgerTestData.ValidateGenesis(baselineSyntax, baselineCatalog)).Capability;
        return (baselineBytes, baseline, candidateCatalog);
    }

    private static SortedDictionary<string, byte[]> DirectorySnapshot(string directory)
    {
        var result = new SortedDictionary<string, byte[]>(StringComparer.Ordinal);
        foreach (var path in Directory.EnumerateFiles(directory))
        {
            result.Add(Path.GetFileName(path), File.ReadAllBytes(path));
        }

        return result;
    }

    internal sealed class LedgerAppendFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();

        internal LedgerAppendFixture(
            bool driftARepresentation = false,
            string currentAStatementMaterial = "True",
            bool pinBump = false,
            bool addSecondClosedModule = true,
            bool historicalReattest = false)
        {
            var baselineA = FrozenLedgerTestData.ModuleWithReport(
                "A",
                "theorem a : True := by trivial\n",
                "True");
            var candidateA = FrozenLedgerTestData.ModuleWithReport(
                "A",
                driftARepresentation
                    ? "-- representation changed\ntheorem a : True := by trivial\n"
                    : baselineA.Source,
                currentAStatementMaterial);
            var b = FrozenLedgerTestData.Module("B", imports: new[] { "A" });
            var c = FrozenLedgerTestData.Module("C", imports: new[] { "B" });
            var baselineCatalog = FrozenLedgerTestData.BuildCatalog(baselineA);
            CandidateCatalog = addSecondClosedModule
                ? FrozenLedgerTestData.BuildCatalog(candidateA, b, c)
                : FrozenLedgerTestData.BuildCatalog(candidateA, b);
            BaselineBytes = FrozenLedgerGenerator.GenerateGenesis(
                baselineCatalog,
                new FrozenGenesisDescriptor(
                    FrozenLedgerTestData.GitOid('e'),
                    RuleCatalog.Default.RootSha256));
            if (historicalReattest)
            {
                var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                    DagLedgerLoader.Load(BaselineBytes.AsSpan())).Syntax;
                var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
                    FrozenLedgerTestData.ValidateGenesis(syntax, baselineCatalog)).Capability;
                var entry = Assert.Single(baseline.ActiveEntries).Value;
                BaselineBytes = FrozenLedgerGenerator.AppendReattestation(
                    baseline,
                    entry.Payload.CaseId,
                    entry.Payload.Input);
            }

            var files = new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["lean-toolchain"] = pinBump
                    ? "leanprover/lean4:v4.25.0\n"
                    : "leanprover/lean4:v4.24.0\n",
                ["lakefile.toml"] = "[package]\nname = \"fixture\"\n",
                ["lake-manifest.json"] = "{}\n",
                [FrozenLedgerTestData.PathFor("A")] = candidateA.Source,
                [FrozenLedgerTestData.PathFor("B")] = b.Source,
            };
            if (addSecondClosedModule)
            {
                files.Add(FrozenLedgerTestData.PathFor("C"), c.Source);
            }
            FrozenLedgerTestData.AddLedgerFiles(files, BaselineBytes);
            var raw = RawRepositorySnapshot.Create(
                files.Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(raw)).Snapshot;
            var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                [FrozenLedgerTestData.PathFor("A")] = Report("A", currentAStatementMaterial),
                [FrozenLedgerTestData.PathFor("B")] = Report("B", "True", "A"),
            };
            if (addSecondClosedModule)
            {
                reports.Add(FrozenLedgerTestData.PathFor("C"), Report("C", "True", "B"));
            }
            var report = LeanAxiomReport.Create(reports);

            LedgerPath = Path.Combine(
                temporary.Path,
                FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));
            FrozenLedgerTestData.WriteLedgerDirectory(LedgerPath, BaselineBytes);
            ReportPath = Path.Combine(temporary.Path, "candidate-lean-report.json");
            File.WriteAllBytes(ReportPath, RawLeanReportArtifact.Write(snapshot, report).AsSpan());
            Gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null);
            Environment = new ProductionCliEnvironment(
                temporary.Path,
                Gateway,
                new FakeLeanReportSource(null));
        }

        internal ImmutableArray<byte> BaselineBytes { get; }

        internal FrozenMaterialCatalog CandidateCatalog { get; }

        internal ProductionCliEnvironment Environment { get; }

        internal FakeRepositoryGateway Gateway { get; }

        internal string LedgerPath { get; }

        internal string ReportPath { get; }

        internal string Root => temporary.Path;

        public void Dispose() => temporary.Dispose();

        private static LeanFileReport Report(
            string name,
            string statementMaterial,
            params string[] imports) => new(
            imports.Select(static item => $"D5.S0.Carrier.{item}").ToImmutableArray(),
            ImmutableArray.Create(new LeanDeclaration(
                name.ToLowerInvariant(),
                "theorem",
                statementMaterial,
                ImmutableArray<string>.Empty)
            {
                NameKey = $"ns(n0,{name.Length}:{name.ToLowerInvariant()})",
            }));
    }
}
