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
        Assert.Contains("appended_freezes=0", result.Output, StringComparison.Ordinal);
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

    [Theory]
    [InlineData("B", true)]
    [InlineData("Omega", false)]
    public void ProductionCommandRoundTripsIndependentBacklogForBothLexicalOrders(
        string backlogModule,
        bool backlogReplaysFirst)
    {
        using var fixture = new LedgerReattestFixture(
            "True",
            includeBacklog: true,
            backlogModule: backlogModule);
        var baselineLines = FrozenLedgerTestData.Lines(fixture.BaselineBytes);

        var result = fixture.Environment.ReattestLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.True(result.Success, result.Error);
        Assert.Contains("appended_reattests=1", result.Output, StringComparison.Ordinal);
        Assert.Contains("appended_freezes=1", result.Output, StringComparison.Ordinal);
        Assert.Contains(
            $"REATTESTED {FrozenLedgerTestData.PathFor("A")}",
            result.Output,
            StringComparison.Ordinal);
        Assert.Contains(
            $"FROZEN {FrozenLedgerTestData.PathFor(fixture.BacklogModule)}",
            result.Output,
            StringComparison.Ordinal);

        var candidateSyntax = DagLedgerCommandPreparation.LoadLedgerDirectory(
            fixture.LedgerPath,
            "test frozen ledger");
        Assert.Equal(baselineLines.Length + 2, candidateSyntax.Lines.Length);
        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedgerTestData.ValidateHistory(candidateSyntax, fixture.CandidateCatalog)).Capability;
        var reattestIndex = accepted.Events
            .Select(static (item, index) => (item, index))
            .Single(static pair => pair.item is FrozenLedgerEvent.Reattest)
            .index;
        var backlogIndex = accepted.Events
            .Select(static (item, index) => (item, index))
            .Single(pair => pair.item is FrozenLedgerEvent.Freeze freeze
                && freeze.Payload.Input.DescriptorSelector == FrozenLedgerTestData.PathFor(fixture.BacklogModule))
            .index;
        Assert.Equal(backlogReplaysFirst, backlogIndex < reattestIndex);
        var acceptedFiles = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath);
        var acceptedView = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            acceptedFiles.ToImmutableDictionary(static file => file.Path)));
        Assert.Contains($"head={acceptedView.EventSetRoot()}", result.Output, StringComparison.Ordinal);
        Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedger.ValidateHistoryPrefix(
                candidateSyntax,
                fixture.CandidateCatalog,
                FrozenLedgerTestData.Trust(candidateSyntax)));
    }

    [Fact]
    public void ProductionCommandWithoutDriftIsAByteIdenticalNoOp()
    {
        using var fixture = new LedgerReattestFixture("True", descriptorDrift: false);

        var result = fixture.Environment.ReattestLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.True(result.Success, result.Error);
        Assert.Contains("no changed frozen modules", result.Output, StringComparison.Ordinal);
        Assert.Equal(
            fixture.BaselineBytes.AsSpan().ToArray(),
            FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }

    [Fact]
    public void ProductionCommandWithoutDriftLeavesIndependentBacklogForLedgerAppend()
    {
        using var fixture = new LedgerReattestFixture(
            "True",
            descriptorDrift: false,
            includeBacklog: true);
        var before = SnapshotDirectory(fixture.LedgerPath);
        var arguments = new[] { "--candidate-lean-report", fixture.ReportPath };

        var reattest = fixture.Environment.ReattestLedger(arguments);

        Assert.True(reattest.Success, reattest.Error);
        Assert.Contains("no changed frozen modules", reattest.Output, StringComparison.Ordinal);
        AssertDirectoryEqual(before, SnapshotDirectory(fixture.LedgerPath));

        var append = fixture.Environment.AppendLedger(arguments);
        Assert.True(append.Success, append.Error);
        Assert.Contains("appended_freezes=1", append.Output, StringComparison.Ordinal);
        Assert.Contains(
            $"FROZEN {FrozenLedgerTestData.PathFor(fixture.BacklogModule)}",
            append.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionCommandAcceptsProspectiveReplayThatReordersBaselineWhenDagInvariantsHold()
    {
        using var fixture = new LedgerReattestFixture("True", includeBacklog: true);

        var result = fixture.Environment.ReattestLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.True(result.Success, result.Error);
        Assert.Contains("appended_reattests=1", result.Output, StringComparison.Ordinal);
        Assert.Contains("appended_freezes=1", result.Output, StringComparison.Ordinal);
        var replayed = DagLedgerCommandPreparation.LoadLedgerDirectory(
            fixture.LedgerPath,
            "test frozen ledger");
        Assert.False(replayed.RawBytes.AsSpan().StartsWith(fixture.BaselineBytes.AsSpan()));
        Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedgerTestData.ValidateHistory(replayed, fixture.CandidateCatalog));
    }

    [Fact]
    public void ProspectiveReplayRejectsAnEventSetMissingABaselineEvent()
    {
        using var fixture = new LedgerReattestFixture("True");
        var baselineFiles = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath);
        var baselineEvents = Assert.IsType<DagLedgerFilesLoadOutcome.Loaded>(
            DagLedgerLoader.LoadFiles(baselineFiles)).Events;

        var exception = Assert.Throws<InvalidOperationException>(() =>
            DagLedgerReattestWriter.RequireExpectedEventSet(
                baselineEvents,
                ImmutableArray<DagLedgerFileEvent>.Empty,
                baselineEvents.Skip(1).ToImmutableArray()));

        Assert.Contains("event set", exception.Message, StringComparison.OrdinalIgnoreCase);

        var baseView = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            baselineFiles.ToImmutableDictionary(static file => file.Path)));
        var nonIncremental = Assert.Throws<InvalidOperationException>(() =>
            DagLedgerCommandPreparation.ValidateGeneratedEventFiles(
                baseView,
                ImmutableArray.Create(baselineFiles.Single(file =>
                    file.Path == baselineEvents.Single(static item => item.EventType == "Genesis").SourcePath)),
                "test suffix"));
        Assert.Contains("does not extend", nonIncremental.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ProspectiveReplayRejectsAnEventSetWithAnExtraEvent()
    {
        using var fixture = new LedgerReattestFixture("True");
        var baselineEvents = Assert.IsType<DagLedgerFilesLoadOutcome.Loaded>(
            DagLedgerLoader.LoadFiles(
                DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath))).Events;
        var extraEvent = baselineEvents[0] with
        {
            EventHash = FrozenLedgerTestData.Sha256("unexpected-extra-event"),
        };

        var exception = Assert.Throws<InvalidOperationException>(() =>
            DagLedgerReattestWriter.RequireExpectedEventSet(
                baselineEvents,
                ImmutableArray<DagLedgerFileEvent>.Empty,
                baselineEvents.Add(extraEvent)));

        Assert.Contains("event set", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ProductionCommandRollsBackEarlierShardsWhenLaterPublicationFails()
    {
        using var fixture = new LedgerReattestFixture("True", includeBacklog: true);
        var baselineSyntax = DagLedgerCommandPreparation.LoadLedgerDirectory(
            fixture.LedgerPath,
            "test frozen ledger");
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedger.ValidateHistoryPrefix(
                baselineSyntax,
                fixture.CandidateCatalog,
                FrozenLedgerTestData.Trust(baselineSyntax))).Capability;
        var intermediateBytes = FrozenLedgerGenerator.AppendReattestation(
            baseline,
            fixture.CandidateCatalog);
        var intermediateSyntax = DagLedgerCommandPreparation.LoadLedger(
            intermediateBytes.AsSpan(),
            "test reattested ledger");
        var intermediate = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedger.ValidateHistoryPrefix(
                intermediateSyntax,
                fixture.CandidateCatalog,
                FrozenLedgerTestData.Trust(intermediateSyntax))).Capability;
        var generatedBytes = FrozenLedgerGenerator.AppendMissingFreezes(
            intermediate,
            fixture.CandidateCatalog);
        var generatedSyntax = DagLedgerCommandPreparation.LoadLedger(
            generatedBytes.AsSpan(),
            "test generated ledger");
        var newFiles = DagLedgerAppendWriter.BuildNewEventFiles(
            generatedSyntax.Lines,
            baseline.Events.Length);
        Assert.Equal(2, newFiles.Length);
        var collisionPath = Path.Combine(
            fixture.LedgerPath,
            Path.GetFileName(newFiles[1].Path.Value));
        Directory.CreateDirectory(collisionPath);
        var before = SnapshotDirectory(fixture.LedgerPath);

        var result = fixture.Environment.ReattestLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.False(result.Success, result.Output);
        Assert.StartsWith("LEDGER_REATTEST_FAILED ", result.Error, StringComparison.Ordinal);
        AssertDirectoryEqual(before, SnapshotDirectory(fixture.LedgerPath));
        Assert.True(Directory.Exists(collisionPath));
    }

    [Fact]
    public void RollbackContinuesAfterAnUndeletableShard()
    {
        using var temporary = new TemporaryDirectory();
        var undeletablePath = Path.Combine(temporary.Path, "undeletable.json");
        Directory.CreateDirectory(undeletablePath);
        File.WriteAllText(Path.Combine(undeletablePath, "contents"), "occupied");
        var deletablePath = Path.Combine(temporary.Path, "deletable.json");
        File.WriteAllText(deletablePath, "created shard");

        DagLedgerAppendWriter.RollbackCreatedFiles(new[] { undeletablePath, deletablePath });

        Assert.True(Directory.Exists(undeletablePath));
        Assert.False(File.Exists(deletablePath));
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
        Assert.Contains("Revoke", result.Error, StringComparison.Ordinal);
        Assert.Equal(
            fixture.BaselineBytes.AsSpan().ToArray(),
            FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }

    [Fact]
    public void ProductionCommandDirectsAmbientStatementDriftToLedgerSupersedeWithoutWriting()
    {
        using var fixture = new LedgerReattestFixture(
            "ambiently-different-elaborated-expression",
            descriptorDrift: false,
            pinBump: true);

        var result = fixture.Environment.ReattestLedger(
            new[] { "--candidate-lean-report", fixture.ReportPath });

        Assert.False(result.Success);
        Assert.Contains("statement identity changed", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("source blob is unchanged", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("ledger-supersede", result.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("append Revoke", result.Error, StringComparison.OrdinalIgnoreCase);
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

    private static Dictionary<string, byte[]> SnapshotDirectory(string directory) =>
        Directory.EnumerateFiles(directory, "*.json")
            .ToDictionary(
                static path => Path.GetFileName(path)!,
                File.ReadAllBytes,
                StringComparer.Ordinal);

    private static void AssertDirectoryEqual(
        IReadOnlyDictionary<string, byte[]> expected,
        IReadOnlyDictionary<string, byte[]> actual)
    {
        Assert.Equal(
            expected.Keys.OrderBy(static path => path, StringComparer.Ordinal),
            actual.Keys.OrderBy(static path => path, StringComparer.Ordinal));
        foreach (var path in expected.Keys)
        {
            Assert.Equal(expected[path], actual[path]);
        }
    }

    private sealed class LedgerReattestFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();

        internal LedgerReattestFixture(
            string candidateStatement,
            bool descriptorDrift = true,
            bool includeBacklog = false,
            string backlogModule = "B",
            bool pinBump = false)
        {
            const string originalSource = "theorem a : True := by trivial\n";
            var candidateSource = descriptorDrift
                ? "-- canonical header changed\n"
                    + $"theorem a : {candidateStatement} := by trivial\n"
                : originalSource;
            BacklogModule = backlogModule;
            var backlogDeclaration = BacklogModule.ToLowerInvariant();
            var backlogSource = $"theorem {backlogDeclaration} : True := by trivial\n";
            var original = FrozenLedgerTestData.Module("A", source: originalSource);
            BaselineCatalog = FrozenLedgerTestData.BuildCatalog(original);
            BaselineBytes = FrozenLedgerGenerator.GenerateGenesis(
                BaselineCatalog,
                new FrozenGenesisDescriptor(
                    FrozenLedgerTestData.GitOid('e'),
                    FrozenLedgerTestData.Sha256("historical-rule-catalog")));

            var files = new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["lean-toolchain"] = pinBump
                    ? "leanprover/lean4:v4.25.0\n"
                    : "leanprover/lean4:v4.24.0\n",
                ["lake-manifest.json"] = "{}\n",
                [FrozenLedgerTestData.PathFor("A")] = candidateSource,
            };
            if (includeBacklog)
            {
                files.Add(FrozenLedgerTestData.PathFor(BacklogModule), backlogSource);
            }
            FrozenLedgerTestData.AddLedgerFiles(files, BaselineBytes);
            var raw = RawRepositorySnapshot.Create(
                files.Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(raw)).Snapshot;
            var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
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
            };
            if (includeBacklog)
            {
                reports.Add(
                    FrozenLedgerTestData.PathFor(BacklogModule),
                    new LeanFileReport(
                        ImmutableArray<string>.Empty,
                        ImmutableArray.Create(new LeanDeclaration(
                            backlogDeclaration,
                            "theorem",
                            "True",
                            ImmutableArray<string>.Empty)
                        {
                            NameKey = $"ns(n0,{backlogDeclaration.Length}:{backlogDeclaration})",
                        })));
            }
            var report = LeanAxiomReport.Create(reports);

            LedgerPath = Path.Combine(
                temporary.Path,
                FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));
            FrozenLedgerTestData.WriteLedgerDirectory(LedgerPath, BaselineBytes);
            ReportPath = Path.Combine(temporary.Path, "candidate-lean-report.json");
            RawLeanReportArtifact.WriteFile(ReportPath, snapshot, report);
            var changedPaths = new List<string>();
            if (descriptorDrift)
            {
                changedPaths.Add(FrozenLedgerTestData.PathFor("A"));
            }
            if (pinBump)
            {
                changedPaths.Add("lean-toolchain");
            }

            Environment = new ProductionCliEnvironment(
                temporary.Path,
                new FakeRepositoryGateway(RawChangeSet.Create(changedPaths), raw, null),
                new FakeLeanReportSource(null));
            CandidateCatalog = BuildCandidateCatalog(
                snapshot,
                report,
                files);
        }

        internal ImmutableArray<byte> BaselineBytes { get; }

        internal string BacklogModule { get; }

        internal FrozenMaterialCatalog BaselineCatalog { get; }

        internal FrozenMaterialCatalog CandidateCatalog { get; }

        internal ProductionCliEnvironment Environment { get; }

        internal string LedgerPath { get; }

        internal string ReportPath { get; }

        internal string Root => temporary.Path;

        public void Dispose() => temporary.Dispose();

        private static FrozenMaterialCatalog BuildCandidateCatalog(
            RepositorySnapshot snapshot,
            LeanAxiomReport report,
            IReadOnlyDictionary<string, string> files)
        {
            var closure = Assert.IsType<LeanValidationOutcome.Accepted>(
                LeanClosureValidator.Validate(snapshot, report)).Capability;
            var states = LeanTruthStates.Resolve(snapshot, closure);
            var adjacency = LeanImportAdjacency.Build(snapshot, closure);
            var environment = new FrozenEnvironmentAttestation(
                FrozenLedgerTestData.GitOid('a'),
                FrozenLedgerTestData.GitOid('b'),
                FrozenLedgerTestData.GitBlobOid(files["lean-toolchain"]),
                FrozenLedgerTestData.GitBlobOid(files["lake-manifest.json"]));
            return Assert.IsType<FrozenMaterialOutcome.Accepted>(
                FrozenContentAddress.Build(
                    snapshot,
                    closure,
                    states,
                    adjacency,
                    environment,
                    report.Files.Keys.Select(path => new FrozenModuleAttestation(
                        path,
                        FrozenLedgerTestData.GitBlobOid(files[path.Value]))))).Capability;
        }
    }
}
