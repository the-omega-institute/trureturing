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
        var persistedFiles = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath);
        var persistedView = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            persistedFiles.ToImmutableDictionary(static file => file.Path)));
        Assert.Contains($"head={persistedView.EventSetRoot()}", console.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionCommandWithoutBaseFlagNeverCallsReadChanges()
    {
        // Requirement 1 (加性、默认行为完全不变): omitting --base must keep using
        // repository.ReadCurrentChanges() exactly as before this flag existed. Asserting
        // ReadChangesCalls is empty proves the new code path is not on the default route, not
        // merely that the output happens to match.
        using var fixture = new LedgerSyncFixture(blobChanged: true, addClosedModule: true);

        var (exitCode, console) = Run(fixture, "ledger-sync");

        Assert.Equal(0, exitCode);
        Assert.Equal(string.Empty, console.Error);
        Assert.Contains("appended_reattests=1", console.Output, StringComparison.Ordinal);
        Assert.Contains("appended_freezes=1", console.Output, StringComparison.Ordinal);
        Assert.Empty(fixture.Gateway.ReadChangesCalls);
    }

    [Fact]
    public void ProductionCommandWithoutBaseFlagReportsNoChangesWhenTheDeltaIsAlreadyCommitted()
    {
        // Reproduces issue #2474: a comment-only edit to an *already-frozen* module is a
        // Reattest, and Reattest selection requires the path to appear in changedPaths (see
        // DagLedgerCommandPreparation.BuildWriterCatalog). A change that is already committed
        // (so ReadCurrentChanges(), the uncommitted-only working-tree diff, is empty) makes that
        // module invisible to ledger-sync without --base, even though the same delta is real
        // against a committed base revision. addClosedModule stays false here: a brand-new
        // module would be selected unconditionally (it is absent from baseView.ActiveByPath
        // regardless of changedPaths) and would not exercise the bug.
        using var fixture = new LedgerSyncFixture(
            blobChanged: true,
            addClosedModule: false,
            currentChangesEmpty: true);

        var (exitCode, console) = Run(fixture, "ledger-sync");

        Assert.Equal(0, exitCode);
        Assert.Equal(string.Empty, console.Error);
        Assert.Contains("no ledger changes", console.Output, StringComparison.Ordinal);
        Assert.Empty(fixture.Gateway.ReadChangesCalls);
    }

    [Fact]
    public void ProductionCommandWithBaseFlagReadsChangesFromThatRevisionAndUnblocksTheSameFixture()
    {
        // Requirement 2, and the fix for #2474 on the exact fixture that reproduces it above:
        // --base REV switches the change set to repository.ReadChanges(REV) -- the committed
        // delta against REV -- instead of the (here, empty) uncommitted delta.
        using var fixture = new LedgerSyncFixture(
            blobChanged: true,
            addClosedModule: false,
            currentChangesEmpty: true);

        var (exitCode, console) = Run(fixture, "ledger-sync", baseRevision: "committed-base-rev");

        Assert.Equal(0, exitCode);
        Assert.Equal(string.Empty, console.Error);
        Assert.Contains("appended_reattests=1", console.Output, StringComparison.Ordinal);
        Assert.Contains("appended_freezes=0", console.Output, StringComparison.Ordinal);
        Assert.Equal(new[] { "committed-base-rev" }, fixture.Gateway.ReadChangesCalls);
    }

    [Fact]
    public void ProductionCommandWithBaseFlagIsIdempotentAcrossAccumulatedRepeatedRuns()
    {
        // Governance finding (nyxid-oracle, 2026-08-20): a fixed --base REV makes
        // GitRepositoryGateway.ReadChanges(REV) an *accumulated* diff -- unlike
        // ReadCurrentChanges(), it never empties out once the edit is committed. So a second
        // `ledger-sync --base REV` run still selects module A via clause (c) (changedPaths still
        // contains its path), even though the on-disk ledger already carries the Reattest the
        // first run wrote. If the writer only asked "was this path selected" and not "does the
        // ledger already match this candidate's material", the second run would append a
        // duplicate Reattest into the append-only ledger -- which cannot be rolled back.
        //
        // This locks down that FrozenLedgerCanonicalWriter's per-path convergence check
        // (materialUnchanged && entry.AxiomClosureKnown -> skip; see
        // FrozenLedgerCanonicalWriter.cs:201-206) is what makes the second run a no-op, not
        // selection. Selection only decides candidacy; convergence decides whether anything is
        // actually appended.
        using var fixture = new LedgerSyncFixture(
            blobChanged: true,
            addClosedModule: false,
            currentChangesEmpty: true);

        var (firstExitCode, firstConsole) = Run(fixture, "ledger-sync", baseRevision: "committed-base-rev");

        Assert.Equal(0, firstExitCode);
        Assert.Equal(string.Empty, firstConsole.Error);
        Assert.Contains("appended_reattests=1", firstConsole.Output, StringComparison.Ordinal);
        var ledgerAfterFirstRun = FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath);

        var (secondExitCode, secondConsole) = Run(fixture, "ledger-sync", baseRevision: "committed-base-rev");

        Assert.Equal(0, secondExitCode);
        Assert.Equal(string.Empty, secondConsole.Error);
        Assert.Contains("no ledger changes", secondConsole.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("REATTESTED", secondConsole.Output, StringComparison.Ordinal);
        Assert.Equal(ledgerAfterFirstRun, FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
        Assert.Equal(
            new[] { "committed-base-rev", "committed-base-rev" },
            fixture.Gateway.ReadChangesCalls);
    }

    [Fact]
    public void ProductionCommandRejectsFlagShapedValueForBaseFlag()
    {
        // Review finding (1): git diff treats "--cached" as a flag (compare against the index),
        // not a revision. Without a guard, `--base --cached` would consume "--cached" as REV,
        // reach GitRepositoryGateway.ReadChanges("--cached"), and exit 0 with an empty change set
        // -- fail-open, silently reproducing the #2474 symptom under a different cause instead of
        // failing loudly. TryParseArguments must reject a flag-shaped value before it ever reaches
        // git, for both flags (this test covers --base; the next covers --candidate-lean-report).
        using var fixture = new LedgerSyncFixture(blobChanged: false, addClosedModule: false);

        var (exitCode, console) = RunArgs(
            fixture, "ledger-sync", "--candidate-lean-report", fixture.ReportPath, "--base", "--cached");

        Assert.Equal(2, exitCode);
        Assert.Contains("USAGE", console.Error, StringComparison.Ordinal);
        Assert.Empty(fixture.Gateway.ReadChangesCalls);
    }

    [Fact]
    public void ProductionCommandRejectsFlagShapedValueForCandidateLeanReportFlag()
    {
        // Review finding (3): without the same guard on --candidate-lean-report, the sequence
        // `--candidate-lean-report --base` would swallow "--base" as the report *path* and fail
        // with a file-read error instead of a usage error. Fixed by the same IsFlagShaped check
        // used for --base, applied symmetrically to both flags.
        using var fixture = new LedgerSyncFixture(blobChanged: false, addClosedModule: false);

        var (exitCode, console) = RunArgs(fixture, "ledger-sync", "--candidate-lean-report", "--base");

        Assert.Equal(2, exitCode);
        Assert.Contains("USAGE", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionCommandRejectsEmptyBaseValueAsUsage()
    {
        using var fixture = new LedgerSyncFixture(blobChanged: false, addClosedModule: false);

        var (exitCode, console) = RunArgs(
            fixture, "ledger-sync", "--candidate-lean-report", fixture.ReportPath, "--base", string.Empty);

        Assert.Equal(2, exitCode);
        Assert.Contains("USAGE", console.Error, StringComparison.Ordinal);
        Assert.Empty(fixture.Gateway.ReadChangesCalls);
    }

    [Fact]
    public void ProductionCommandRejectsDuplicateBaseFlag()
    {
        // Review finding (2): the "@base is null" uniqueness guard already rejected a repeated
        // --base before this PR, but nothing tested it -- a later refactor could silently drop the
        // guard (e.g. "last one wins") and every pre-existing test would stay green. This test
        // exists purely to lock the guard down.
        using var fixture = new LedgerSyncFixture(blobChanged: false, addClosedModule: false);

        var (exitCode, console) = RunArgs(
            fixture,
            "ledger-sync",
            "--candidate-lean-report", fixture.ReportPath,
            "--base", "rev-one",
            "--base", "rev-two");

        Assert.Equal(2, exitCode);
        Assert.Contains("USAGE", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionCommandRejectsDuplicateCandidateLeanReportFlag()
    {
        // Symmetric to the --base duplicate guard: "each flag at most once" applies to both.
        using var fixture = new LedgerSyncFixture(blobChanged: false, addClosedModule: false);

        var (exitCode, console) = RunArgs(
            fixture,
            "ledger-sync",
            "--candidate-lean-report", fixture.ReportPath,
            "--candidate-lean-report", fixture.ReportPath);

        Assert.Equal(2, exitCode);
        Assert.Contains("USAGE", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionCommandRejectsBaseFlagMissingItsValueAtEndOfArguments()
    {
        // Pre-existing behaviour (the index+1 < arguments.Count bound), locked down with a named
        // test as the review requested rather than left to rely on nobody breaking it.
        using var fixture = new LedgerSyncFixture(blobChanged: false, addClosedModule: false);

        var (exitCode, console) = RunArgs(
            fixture, "ledger-sync", "--candidate-lean-report", fixture.ReportPath, "--base");

        Assert.Equal(2, exitCode);
        Assert.Contains("USAGE", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionCommandAcceptsBaseFlagBeforeCandidateLeanReportFlag()
    {
        // Reversed flag order is pre-existing accepted behaviour; locked down with a test so a
        // future parser rewrite that only tries one order doesn't regress it silently.
        using var fixture = new LedgerSyncFixture(
            blobChanged: true,
            addClosedModule: false,
            currentChangesEmpty: true);

        var (exitCode, console) = RunArgs(
            fixture,
            "ledger-sync",
            "--base", "committed-base-rev",
            "--candidate-lean-report", fixture.ReportPath);

        Assert.Equal(0, exitCode);
        Assert.Equal(string.Empty, console.Error);
        Assert.Contains("appended_reattests=1", console.Output, StringComparison.Ordinal);
        Assert.Equal(new[] { "committed-base-rev" }, fixture.Gateway.ReadChangesCalls);
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
        Assert.Equal(0, fixture.Gateway.FrozenReferenceValidationCount);
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
        Assert.Equal(0, fixture.Gateway.FrozenReferenceValidationCount);
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
        var pending = DagLedgerAppendWriter.BuildNewEventFiles(
            generatedSyntax.Lines,
            fixture.Baseline.Events.Length);
        var prospectiveFiles = Directory.EnumerateFiles(fixture.LedgerPath, "*.json")
            .Select(ReadEventFile)
            .Concat(pending)
            .ToImmutableArray();
        var replayed = DagLedgerCommandPreparation.LoadLedgerFiles(
            prospectiveFiles,
            "prospective frozen ledger");
        var firstDifference = FirstDifference(generatedBytes, replayed.RawBytes);

        Assert.True(firstDifference >= 0);
        Assert.NotEqual(
            generatedSyntax.Lines.Select(static line =>
                line.Value.GetProperty("event_hash").GetString()).ToArray(),
            replayed.Lines.Select(static line =>
                line.Value.GetProperty("event_hash").GetString()).ToArray());

        var (exitCode, console) = Run(fixture, "ledger-sync");

        Assert.Equal(0, exitCode);
        Assert.Equal(string.Empty, console.Error);
        Assert.Equal(
            replayed.RawBytes.AsSpan().ToArray(),
            FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
        Assert.Equal(1, fixture.Gateway.FrozenReferenceValidationCount);
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
        var pending = DagLedgerAppendWriter.BuildNewEventFiles(
            generatedSyntax.Lines,
            fixture.Baseline.Events.Length);
        var prospectiveFiles = Directory.EnumerateFiles(fixture.LedgerPath, "*.json")
            .Select(ReadEventFile)
            .Concat(pending)
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
        string command,
        string? baseRevision = null)
    {
        var console = new BufferedConsole();
        var arguments = baseRevision is null
            ? new[] { command, "--candidate-lean-report", fixture.ReportPath }
            : new[] { command, "--candidate-lean-report", fixture.ReportPath, "--base", baseRevision };
        var exitCode = CliApplication.Run(arguments, fixture.Environment, console);
        return (exitCode, console);
    }

    /// Same as Run, but the caller supplies the full argument list verbatim (including the
    /// leading command name) instead of the fixed `--candidate-lean-report FILE [--base REV]`
    /// shape -- for exercising TryParseArguments' malformed-input paths directly.
    private static (int ExitCode, BufferedConsole Console) RunArgs(
        LedgerSyncFixture fixture,
        params string[] arguments)
    {
        var console = new BufferedConsole();
        var exitCode = CliApplication.Run(arguments, fixture.Environment, console);
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
            int? changedModuleCount = null,
            bool currentChangesEmpty = false)
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
            RawLeanReportArtifact.WriteFile(ReportPath, snapshot, report);
            var changedPaths = candidates
                .Take(candidateChangeCount)
                .Select(static module => FrozenLedgerTestData.PathFor(module.Name))
                .ToArray();
            var currentChanges = currentChangesEmpty
                ? RawChangeSet.Create(Array.Empty<string>())
                : RawChangeSet.Create(changedPaths);
            Gateway = new FakeRepositoryGateway(
                currentChanges,
                raw,
                null,
                changesForBase: _ => RawChangeSet.Create(changedPaths));
            Environment = new ProductionCliEnvironment(
                temporary.Path,
                Gateway,
                new FakeLeanReportSource(null));
        }

        internal ImmutableArray<byte> BaselineBytes { get; }

        internal FrozenLedgerConsistent Baseline { get; }

        internal FrozenMaterialCatalog CandidateCatalog { get; }

        internal FakeRepositoryGateway Gateway { get; }

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
