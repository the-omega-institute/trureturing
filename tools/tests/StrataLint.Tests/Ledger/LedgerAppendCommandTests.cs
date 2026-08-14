using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
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
    public void ProductionCommandRejectsStatementChangesWithRevokeGuidanceWithoutWriting()
    {
        using var fixture = new LedgerAppendFixture(currentAStatementMaterial: "False");

        var result = fixture.Environment.AppendLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.False(result.Success, result.Output);
        Assert.Contains(FrozenLedgerTestData.PathFor("A"), result.Error, StringComparison.Ordinal);
        Assert.Contains("statement identity", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("Revoke", result.Error, StringComparison.Ordinal);
        Assert.Equal(
            fixture.BaselineBytes.AsSpan().ToArray(),
            FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
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
                expectedBaselineBytes: baselineBytes.ToArray()));

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
    public void WriteNewEventsLeavesTheLedgerUnchangedWhenPreflightFindsAnExistingShard()
    {
        using var temporary = new TemporaryDirectory();
        var (baselineBytes, baseline, candidateCatalog) = ReconciliationFixture(includeNewModule: true);
        var candidateBytes = FrozenLedgerGenerator.AppendSynchronization(baseline, candidateCatalog);
        var candidateSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax;
        FrozenLedgerTestData.WriteLedgerDirectory(temporary.Path, baselineBytes);
        var projected = ProjectLedgerFiles(candidateBytes);
        var collidingFreeze = EventPath(projected, "Freeze", FrozenLedgerTestData.PathFor("B"));
        File.WriteAllText(Path.Combine(temporary.Path, Path.GetFileName(collidingFreeze)), "collision\n");
        var before = DirectorySnapshot(temporary.Path);

        Assert.Throws<IOException>(() => DagLedgerAppendWriter.WriteNewEvents(
            temporary.Path,
            candidateSyntax.Lines,
            baseline.Events.Length));

        var after = DirectorySnapshot(temporary.Path);
        Assert.Equal(before.Keys, after.Keys);
        Assert.All(before, item => Assert.Equal(item.Value, after[item.Key]));
    }

    [Fact]
    public void WriteNewEventsRejectsDuplicateIdentityWithinTheBatchBeforePublishing()
    {
        using var temporary = new TemporaryDirectory();
        var (baselineBytes, baseline, candidateCatalog) = ReconciliationFixture(includeNewModule: true);
        var candidateBytes = FrozenLedgerGenerator.AppendSynchronization(baseline, candidateCatalog);
        var candidateSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax;
        FrozenLedgerTestData.WriteLedgerDirectory(temporary.Path, baselineBytes);
        var freeze = candidateSyntax.Lines.Single(line =>
            line.Value.GetProperty("event_type").GetString() == "Freeze"
            && line.Value.GetProperty("payload").GetProperty("node_path").GetString()
                == FrozenLedgerTestData.PathFor("B"));
        var duplicate = JsonNode.Parse(freeze.Value.GetRawText())!.AsObject();
        duplicate["event_hash"] = new string('9', 64);
        var duplicateLine = new FrozenLedgerLineSyntax(
            ImmutableArray<byte>.Empty,
            JsonSerializer.SerializeToElement(duplicate));
        var before = DirectorySnapshot(temporary.Path);

        var exception = Assert.Throws<IOException>(() => DagLedgerAppendWriter.WriteNewEvents(
            temporary.Path,
            candidateSyntax.Lines.Add(duplicateLine),
            baseline.Events.Length));

        Assert.Contains("planned more than once", exception.Message, StringComparison.Ordinal);
        var after = DirectorySnapshot(temporary.Path);
        Assert.Equal(before.Keys, after.Keys);
        Assert.All(before, item => Assert.Equal(item.Value, after[item.Key]));
    }

    [Fact]
    public void WriteNewEventsRollsBackPublishedShardWhenALaterMoveFails()
    {
        using var temporary = new TemporaryDirectory();
        var (baselineBytes, baseline, candidateCatalog) = ReconciliationFixture(includeNewModule: true);
        var candidateBytes = FrozenLedgerGenerator.AppendSynchronization(baseline, candidateCatalog);
        var candidateSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax;
        FrozenLedgerTestData.WriteLedgerDirectory(temporary.Path, baselineBytes);
        var projected = ProjectLedgerFiles(candidateBytes);
        var firstPublishedPath = EventPath(
            projected,
            "Reattest",
            FrozenLedgerTestData.PathFor("A"));
        var failingPath = EventPath(projected, "Freeze", FrozenLedgerTestData.PathFor("B"));
        Directory.CreateDirectory(Path.Combine(temporary.Path, Path.GetFileName(failingPath)));

        Assert.Throws<IOException>(() => DagLedgerAppendWriter.WriteNewEvents(
            temporary.Path,
            candidateSyntax.Lines,
            baseline.Events.Length));

        Assert.False(File.Exists(Path.Combine(
            temporary.Path,
            Path.GetFileName(firstPublishedPath))));
        Assert.True(Directory.Exists(Path.Combine(
            temporary.Path,
            Path.GetFileName(failingPath))));
        Assert.Empty(Directory.EnumerateDirectories(temporary.Path, ".ledger-stage-*"));
    }

    [Fact]
    public void RollbackPublishedPrefixStopsAtFirstFailureAndPreservesTheLongestPrefix()
    {
        using var temporary = new TemporaryDirectory();
        var first = Path.Combine(temporary.Path, "first.json");
        var second = Path.Combine(temporary.Path, "second.json");
        var blocked = Path.Combine(temporary.Path, "third.json");
        var last = Path.Combine(temporary.Path, "fourth.json");
        File.WriteAllText(first, "first\n");
        File.WriteAllText(second, "second\n");
        Directory.CreateDirectory(blocked);
        File.WriteAllText(last, "fourth\n");

        var rollback = DagLedgerAppendWriter.RollbackPublishedPrefix(
            [first, second, blocked, last]);

        Assert.Collection(rollback.RolledBackPaths, path => Assert.Equal(last, path));
        Assert.Equal(blocked, rollback.StoppedPath);
        Assert.NotNull(rollback.Failure);
        Assert.True(File.Exists(first));
        Assert.True(File.Exists(second));
        Assert.True(Directory.Exists(blocked));
        Assert.False(File.Exists(last));

        var publicationFailure = DagLedgerAppendWriter.PublicationFailure(
            new IOException("synthetic move failure"),
            [first, second, blocked, last],
            rollback,
            scratchFailure: null);
        var rendered = DagLedgerAppendWriter.RenderFailure(
            "LEDGER_APPEND_FAILED",
            publicationFailure);
        Assert.Contains("LEDGER_ROLLBACK_INCOMPLETE", rendered, StringComparison.Ordinal);
        Assert.Contains("published=[first.json,second.json,third.json,fourth.json]", rendered, StringComparison.Ordinal);
        Assert.Contains("rolled_back=[fourth.json]", rendered, StringComparison.Ordinal);
        Assert.Contains("rollback_stopped_at=third.json", rendered, StringComparison.Ordinal);
        Assert.Contains("retained_prefix=[first.json,second.json,third.json]", rendered, StringComparison.Ordinal);
        Assert.DoesNotContain("LEDGER_SCRATCH_CLEANUP_FAILED", rendered, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("LEDGER_APPEND_FAILED")]
    [InlineData("LEDGER_REATTEST_FAILED")]
    [InlineData("LEDGER_RECOORDINATE_FAILED")]
    [InlineData("LEDGER_SYNC_FAILED")]
    public void LedgerCommandFailureRenderingKeepsIncompleteRollbackVisible(string marker)
    {
        var exception = new IOException(
            "LEDGER_ROLLBACK_INCOMPLETE published shards remain as the longest valid prefix.",
            new AggregateException(new IOException("synthetic rollback failure")));

        var rendered = DagLedgerAppendWriter.RenderFailure(marker, exception);

        Assert.StartsWith(marker + " ", rendered, StringComparison.Ordinal);
        Assert.Contains("LEDGER_ROLLBACK_INCOMPLETE", rendered, StringComparison.Ordinal);
        Assert.Contains("synthetic rollback failure", rendered, StringComparison.Ordinal);
    }

    [Fact]
    public void SuccessfulPublicationScratchCleanupFailureHasItsOwnSignal()
    {
        using var temporary = new TemporaryDirectory();
        var staging = Path.Combine(temporary.Path, ".ledger-stage-test");
        Directory.CreateDirectory(staging);
        File.WriteAllText(Path.Combine(staging, ".DS_Store"), "synthetic stray file\n");

        var warning = DagLedgerAppendWriter.CleanupAfterSuccessfulPublication(staging);

        Assert.StartsWith("LEDGER_SCRATCH_CLEANUP_FAILED ", warning, StringComparison.Ordinal);
        Assert.Contains("publication_succeeded=true", warning, StringComparison.Ordinal);
        Assert.DoesNotContain("ROLLBACK_INCOMPLETE", warning, StringComparison.Ordinal);
        Assert.True(Directory.Exists(staging));
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

    [Fact]
    public void WriteNewEventsNamesTheModuleAndPriorIdentityWhenAReattestShardCollides()
    {
        using var temporary = new TemporaryDirectory();
        var (baselineBytes, baseline, candidateCatalog) = ReconciliationFixture(includeNewModule: false);
        var candidateBytes = FrozenLedgerGenerator.AppendSynchronization(baseline, candidateCatalog);
        var candidateSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax;
        FrozenLedgerTestData.WriteLedgerDirectory(temporary.Path, baselineBytes);
        var projected = ProjectLedgerFiles(candidateBytes);
        var collidingReattest = EventPath(projected, "Reattest", FrozenLedgerTestData.PathFor("A"));
        File.WriteAllText(Path.Combine(temporary.Path, Path.GetFileName(collidingReattest)), "collision\n");

        var exception = Assert.Throws<IOException>(() => DagLedgerAppendWriter.WriteNewEvents(
            temporary.Path,
            candidateSyntax.Lines,
            baseline.Events.Length));

        Assert.Contains(FrozenLedgerTestData.PathFor("A"), exception.Message, StringComparison.Ordinal);
        Assert.Contains("previously recorded", exception.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("byte-distinct", exception.Message, StringComparison.OrdinalIgnoreCase);
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

    private static Dictionary<string, string> ProjectLedgerFiles(ImmutableArray<byte> bytes)
    {
        var projected = new Dictionary<string, string>(StringComparer.Ordinal);
        FrozenLedgerTestData.AddLedgerFiles(projected, bytes);
        return projected;
    }

    private static string EventPath(
        IReadOnlyDictionary<string, string> files,
        string eventType,
        string modulePath) => files.Single(item =>
    {
        using var document = JsonDocument.Parse(item.Value);
        var root = document.RootElement;
        if (root.GetProperty("event_type").GetString() != eventType)
        {
            return false;
        }

        var payload = root.GetProperty("payload");
        return eventType == "Freeze"
            ? payload.GetProperty("node_path").GetString() == modulePath
            : payload.GetProperty("input").GetProperty("descriptor_selector").GetString() == modulePath;
    }).Key;

    private static SortedDictionary<string, byte[]> DirectorySnapshot(string directory)
    {
        var result = new SortedDictionary<string, byte[]>(StringComparer.Ordinal);
        foreach (var path in Directory.EnumerateFiles(directory))
        {
            result.Add(Path.GetFileName(path), File.ReadAllBytes(path));
        }

        return result;
    }

    private sealed class LedgerAppendFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();

        internal LedgerAppendFixture(
            bool driftARepresentation = false,
            string currentAStatementMaterial = "True")
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
            CandidateCatalog = FrozenLedgerTestData.BuildCatalog(candidateA, b, c);
            BaselineBytes = FrozenLedgerGenerator.GenerateGenesis(
                baselineCatalog,
                new FrozenGenesisDescriptor(
                    FrozenLedgerTestData.GitOid('e'),
                    RuleCatalog.Default.RootSha256));

            var files = new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["lean-toolchain"] = "leanprover/lean4:v4.24.0\n",
                ["lake-manifest.json"] = "{}\n",
                [FrozenLedgerTestData.PathFor("A")] = candidateA.Source,
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
                [FrozenLedgerTestData.PathFor("A")] = Report("A", currentAStatementMaterial),
                [FrozenLedgerTestData.PathFor("B")] = Report("B", "True", "A"),
                [FrozenLedgerTestData.PathFor("C")] = Report("C", "True", "B"),
            });

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
