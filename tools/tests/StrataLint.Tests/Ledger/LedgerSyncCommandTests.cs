using System.Collections.Immutable;
using System.Text;
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

    [Fact]
    public void ProductionCommandUsesDirectoryReplayOrderForManyExistingEvents()
    {
        using var fixture = new LedgerSyncFixture(
            blobChanged: true,
            addClosedModule: false,
            existingModuleCount: 16);
        var generatedBytes = FrozenLedgerGenerator.AppendSynchronization(
            fixture.Baseline,
            fixture.CandidateCatalog);
        var generatedSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(generatedBytes.AsSpan())).Syntax;
        var pending = DagLedgerAppendWriter.PrepareNewEvents(
            fixture.LedgerPath,
            generatedSyntax.Lines,
            fixture.Baseline.Events.Length).ToImmutableArray();
        var prospectiveFiles = Directory.EnumerateFiles(fixture.LedgerPath, "*.json")
            .Select(ReadEventFile)
            .Concat(pending.Select(static item => EventFile(item.Path, item.Bytes)))
            .ToImmutableArray();
        var replayed = DagLedgerCommandPreparation.LoadLedgerFiles(
            prospectiveFiles,
            "prospective frozen ledger");
        var firstDifference = FirstDifference(generatedBytes, replayed.RawBytes);

        Assert.Equal(2329, firstDifference);
        Assert.Equal(
            "Freeze",
            generatedSyntax.Lines[2].Value.GetProperty("event_type").GetString());
        Assert.Equal(
            "Reattest",
            replayed.Lines[2].Value.GetProperty("event_type").GetString());

        var (exitCode, console) = Run(fixture, "ledger-sync");

        Assert.Equal(0, exitCode);
        Assert.Equal(string.Empty, console.Error);
        Assert.Equal(
            replayed.RawBytes.AsSpan().ToArray(),
            FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }

    [Fact]
    public void ProductionCommandReplaysRealLedgerScaleTopology()
    {
        using var fixture = new LedgerSyncFixture(
            blobChanged: true,
            addClosedModule: false,
            existingModuleCount: 688,
            historicalReattestCount: 83,
            changedModuleCount: 63);
        Assert.Equal(772, fixture.Baseline.Events.Length);
        Assert.Single(fixture.Baseline.Events.OfType<FrozenLedgerEvent.Genesis>());
        Assert.Equal(688, fixture.Baseline.Events.OfType<FrozenLedgerEvent.Freeze>().Count());
        Assert.Equal(83, fixture.Baseline.Events.OfType<FrozenLedgerEvent.Reattest>().Count());

        var generatedBytes = FrozenLedgerGenerator.AppendSynchronization(
            fixture.Baseline,
            fixture.CandidateCatalog);
        var generatedSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(generatedBytes.AsSpan())).Syntax;
        var pending = DagLedgerAppendWriter.PrepareNewEvents(
            fixture.LedgerPath,
            generatedSyntax.Lines,
            fixture.Baseline.Events.Length).ToImmutableArray();
        var prospectiveFiles = Directory.EnumerateFiles(fixture.LedgerPath, "*.json")
            .Select(ReadEventFile)
            .Concat(pending.Select(static item => EventFile(item.Path, item.Bytes)))
            .ToImmutableArray();
        var replayed = DagLedgerCommandPreparation.LoadLedgerFiles(
            prospectiveFiles,
            "prospective frozen ledger");
        var firstDifference = FirstDifference(generatedBytes, replayed.RawBytes);

        Assert.NotEqual(-1, firstDifference);
        Assert.Equal(63, pending.Length);
        Assert.Equal(835, replayed.Lines.Length);

        var (exitCode, console) = Run(fixture, "ledger-sync");

        Assert.Equal(0, exitCode);
        Assert.Equal(string.Empty, console.Error);
        Assert.Contains("appended_reattests=63", console.Output, StringComparison.Ordinal);
        Assert.Contains("appended_freezes=0", console.Output, StringComparison.Ordinal);
        Assert.Equal(
            replayed.RawBytes.AsSpan().ToArray(),
            FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }

    private static RepositoryFile ReadEventFile(string path)
    {
        var bytes = File.ReadAllBytes(path);
        return EventFile(path, ImmutableArray.CreateRange(bytes));
    }

    private static RepositoryFile EventFile(string path, ImmutableArray<byte> bytes)
    {
        return new RepositoryFile(
            RepoPath.CreateKnown(
                $"{FrozenLedgerChangeClassifier.AcceptedRoot}/{Path.GetFileName(path)}"),
            bytes,
            Encoding.UTF8.GetString(bytes.AsSpan()));
    }

    private static int FirstDifference(
        ImmutableArray<byte> left,
        ImmutableArray<byte> right)
    {
        var length = Math.Min(left.Length, right.Length);
        for (var index = 0; index < length; index++)
        {
            if (left[index] != right[index])
            {
                return index;
            }
        }

        return left.Length == right.Length ? -1 : length;
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
            string candidateStatement = "True",
            int existingModuleCount = 1,
            int historicalReattestCount = 0,
            int? changedModuleCount = null)
        {
            if (historicalReattestCount < 0 || historicalReattestCount > existingModuleCount)
            {
                throw new ArgumentOutOfRangeException(nameof(historicalReattestCount));
            }

            var candidateChangeCount = blobChanged
                ? changedModuleCount ?? existingModuleCount
                : 0;
            if (candidateChangeCount < 0 || candidateChangeCount > existingModuleCount)
            {
                throw new ArgumentOutOfRangeException(nameof(changedModuleCount));
            }

            var moduleNames = existingModuleCount == 1
                ? new[] { "A" }
                : Enumerable.Range(0, existingModuleCount)
                    .Select(index => existingModuleCount < 100
                        ? $"M{index:D2}"
                        : $"M{index:D3}")
                    .ToArray();
            var originals = moduleNames.Select(static name =>
                FrozenLedgerTestData.Module(name)).ToArray();
            var historical = originals.Select((module, index) =>
                index < historicalReattestCount
                    ? module with
                    {
                        Source = $"-- historical header changed\ntheorem {module.Name.ToLowerInvariant()} : True := by trivial\n",
                    }
                    : module).ToArray();
            var candidateHeader = historicalReattestCount == 0 && changedModuleCount is null
                ? "canonical"
                : "candidate";
            var candidates = historical.Select((module, index) => index < candidateChangeCount
                ? module with
                {
                    Source = $"-- {candidateHeader} header changed\ntheorem {module.Name.ToLowerInvariant()} : {candidateStatement} := by trivial\n",
                    StatementMaterial = candidateStatement,
                }
                : module).ToArray();
            var added = FrozenLedgerTestData.Module(
                existingModuleCount == 1 ? "B" : "Added",
                imports: new[] { moduleNames[^1] });
            var originalCatalog = FrozenLedgerTestData.BuildCatalog(originals);
            var historicalCatalog = historicalReattestCount == 0
                ? originalCatalog
                : FrozenLedgerTestData.BuildCatalog(historical);
            CandidateCatalog = addClosedModule
                ? FrozenLedgerTestData.BuildCatalog(candidates.Append(added).ToArray())
                : FrozenLedgerTestData.BuildCatalog(candidates);
            var genesisBytes = FrozenLedgerGenerator.GenerateGenesis(
                originalCatalog,
                new FrozenGenesisDescriptor(
                    FrozenLedgerTestData.GitOid('e'),
                    FrozenLedgerTestData.Sha256("historical-rule-catalog")));
            var genesisSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                DagLedgerLoader.Load(genesisBytes.AsSpan())).Syntax;
            var genesis = FrozenLedgerTestData.ValidateHistory(genesisSyntax, originalCatalog) switch
            {
                FrozenLedgerValidationOutcome.Accepted accepted => accepted.Capability,
                FrozenLedgerValidationOutcome.Rejected rejected => throw new InvalidOperationException(
                    "fixture genesis was rejected: " + rejected.Message),
                _ => throw new InvalidOperationException("unknown fixture genesis outcome"),
            };
            BaselineBytes = historicalReattestCount == 0
                ? genesisBytes
                : FrozenLedgerGenerator.AppendReattestation(genesis, historicalCatalog);

            var baselineSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                DagLedgerLoader.Load(BaselineBytes.AsSpan())).Syntax;
            Baseline = FrozenLedgerTestData.ValidateHistory(baselineSyntax, historicalCatalog) switch
            {
                FrozenLedgerValidationOutcome.Accepted accepted => accepted.Capability,
                FrozenLedgerValidationOutcome.Rejected rejected => throw new InvalidOperationException(
                    "fixture history was rejected: " + rejected.Message),
                _ => throw new InvalidOperationException("unknown fixture history outcome"),
            };

            var files = new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["lean-toolchain"] = "leanprover/lean4:v4.24.0\n",
                ["lake-manifest.json"] = "{}\n",
            };
            var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal);
            foreach (var module in candidates)
            {
                files.Add(FrozenLedgerTestData.PathFor(module.Name), module.Source);
                reports.Add(
                    FrozenLedgerTestData.PathFor(module.Name),
                    Report(module.Name, candidateStatement, module.Imports.ToArray()));
            }

            if (addClosedModule)
            {
                files.Add(FrozenLedgerTestData.PathFor(added.Name), added.Source);
                reports.Add(
                    FrozenLedgerTestData.PathFor(added.Name),
                    Report(added.Name, "True", added.Imports.ToArray()));
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

        internal FrozenLedgerConsistent Baseline { get; }

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
