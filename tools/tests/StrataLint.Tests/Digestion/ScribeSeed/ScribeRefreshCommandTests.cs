using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScribeRefreshCommandTests
{
    private const string DocumentsPath = "documents.txt";

    [Fact]
    public void SelectedDocumentExpandsEveryExistingReceipt()
    {
        var fixture = Stale(new ScribeSeedFixture(2));

        var execution = Execute(fixture, ScribeSeedFixture.ModuleGid + "\n");

        Assert.True(execution.Result.Success, execution.Result.Error);
        Assert.Equal(1, execution.ApplyCalls);
        Assert.Equal(2, execution.Result.Output.Split('\n').Count(static line =>
            line.StartsWith("SCRIBE_REFRESH atom_id=", StringComparison.Ordinal)));
        Assert.All(Load(execution.After).RequireDigestionEntries(), entry =>
        {
            var receipt = Assert.Single(entry.Receipts.Scribe);
            Assert.True(fixture.Verified.TryGet(ScribeSeedFixture.ModuleGid, out var verified));
            Assert.Equal(verified.DefinitionSha256, receipt.DefinitionSha256);
            Assert.Equal(verified.EmissionSha256, receipt.EmissionSha256);
        });
    }

    [Fact]
    public void ModuleGidReceiptRefreshesWithoutDeclarationReference()
    {
        var fixture = Stale(new ScribeSeedFixture(module: true));

        var execution = Execute(fixture, ScribeSeedFixture.ModuleGid + "\n");

        Assert.True(execution.Result.Success, execution.Result.Error);
        Assert.Equal(ScribeSeedFixture.ModuleGid,
            Assert.Single(Assert.Single(Load(execution.After).RequireDigestionEntries()).Receipts.Scribe).Gid);
    }

    [Fact]
    public void DeclarationReceiptRequiresVerifiedReference()
    {
        var fixture = Stale(new ScribeSeedFixture());
        Assert.True(fixture.Verified.TryGet(ScribeSeedFixture.ModuleGid, out var record));
        fixture.Verified = VerifiedScribeEmissions.Create([record]);

        var execution = Execute(fixture, ScribeSeedFixture.ModuleGid + "\n");

        Assert.False(execution.Result.Success);
        Assert.Contains("declaration-reference-missing", execution.Result.Output, StringComparison.Ordinal);
        Assert.Equal(0, execution.ApplyCalls);
        Assert.Equal(Image(execution.Before), Image(execution.After));
    }

    [Fact]
    public void BaselineReceiptFailureOutsideSelectedClosureDoesNotVetoRefresh()
    {
        var fixture = TwoDocuments();
        fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry =>
            entry.CoverageGids.Contains("D5/S0/Carrier/RefreshB.probe", StringComparer.Ordinal)
                ? entry with
                {
                    Coverage = entry.Coverage.Select(edge => edge with
                    {
                        TargetStatementId = "sha256:" + new string('0', 64),
                    }).ToImmutableArray(),
                }
                : entry);
        fixture.Baseline = fixture.Document;

        var execution = Execute(fixture, "D5/S0/Carrier/RefreshA\n");

        Assert.True(execution.Result.Success, execution.Result.Error);
        var entries = Load(execution.After).RequireDigestionEntries();
        var selected = Assert.Single(entries, static entry =>
            entry.CoverageGids.Contains("D5/S0/Carrier/RefreshA.probe", StringComparer.Ordinal));
        var outside = Assert.Single(entries, static entry =>
            entry.CoverageGids.Contains("D5/S0/Carrier/RefreshB.probe", StringComparer.Ordinal));
        Assert.DoesNotContain("sha256:aaaa", Assert.Single(selected.Receipts.Scribe).DefinitionSha256,
            StringComparison.Ordinal);
        Assert.Equal("sha256:" + new string('a', 64), Assert.Single(outside.Receipts.Scribe).DefinitionSha256);
    }

    [Fact]
    public void CandidateNewStructuralFailureInsideClosureRejectsWholePlan()
    {
        var fixture = Stale(new ScribeSeedFixture());
        var baseline = fixture.Raw(fixture.Baseline);
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] =
            "<<<<<<< HEAD\nconflicted candidate source\n";

        var execution = Execute(fixture, ScribeSeedFixture.ModuleGid + "\n", baseline: baseline);

        Assert.False(execution.Result.Success);
        Assert.Contains(DigestionSourceConflictMarkers.DiagnosticCode, execution.Result.Error,
            StringComparison.Ordinal);
        Assert.Equal(0, execution.ApplyCalls);
        Assert.Equal(Image(execution.Before), Image(execution.After));
    }

    [Fact]
    public void RefreshRejectsProtectedBaseAtomAbsent()
    {
        var fixture = Stale(new ScribeSeedFixture());
        var source = Assert.Single(fixture.Baseline.RequireDigestionSources());
        fixture.Baseline = fixture.Baseline.WithDigestionSources([source with { Entries = [] }]);

        var execution = Execute(fixture, ScribeSeedFixture.ModuleGid + "\n");

        AssertRefreshRejected(execution, "protected-base-atom-identity-absent");
    }

    [Fact]
    public void RefreshRejectsProtectedBaseCoverageEdgeAbsent()
    {
        var fixture = Stale(new ScribeSeedFixture());
        fixture.Baseline = ScribeSeedFixture.Map(fixture.Baseline, entry => entry with
        {
            Coverage = [],
            Receipts = entry.Receipts with { Scribe = [] },
        });

        var execution = Execute(fixture, ScribeSeedFixture.ModuleGid + "\n");

        AssertRefreshRejected(execution, "protected-base-coverage-edge-identity-absent");
    }

    [Fact]
    public void RefreshRejectsProtectedBaseCoverageTargetMismatch()
    {
        var fixture = Stale(new ScribeSeedFixture());
        fixture.Baseline = ScribeSeedFixture.Map(fixture.Baseline, entry => entry with
        {
            Coverage = entry.Coverage.Select(edge => edge with
            {
                TargetStatementId = "sha256:" + new string('0', 64),
            }).ToImmutableArray(),
        });

        var execution = Execute(fixture, ScribeSeedFixture.ModuleGid + "\n");

        AssertRefreshRejected(execution, "protected-base-coverage-edge-identity-absent");
    }

    [Fact]
    public void RefreshRejectsProtectedBaseScribeReceiptAbsent()
    {
        var fixture = Stale(new ScribeSeedFixture());
        fixture.Baseline = ScribeSeedFixture.Map(fixture.Baseline, entry => entry with
        {
            Receipts = entry.Receipts with { Scribe = [] },
        });

        var execution = Execute(fixture, ScribeSeedFixture.ModuleGid + "\n");

        AssertRefreshRejected(execution, "protected-base-scribe-receipt-identity-absent");
    }

    [Fact]
    public void PairSelectorUsesPromotedRefreshPolicyForModuleGid()
    {
        var fixture = Stale(new ScribeSeedFixture(module: true));

        var execution = Execute(
            fixture,
            string.Empty,
            arguments:
            [
                "--atom-id", fixture.First.AtomId,
                "--gid", ScribeSeedFixture.ModuleGid,
                "--base", "baseline",
            ]);

        Assert.True(execution.Result.Success, execution.Result.Error);
        Assert.Equal(1, execution.ApplyCalls);
        Assert.Equal(ScribeSeedFixture.ModuleGid,
            Assert.Single(Assert.Single(Load(execution.After).RequireDigestionEntries()).Receipts.Scribe).Gid);
    }

    [Fact]
    public void RefreshRejectsEvaluatorStatusChangeOutsideAuthorizedClosure()
    {
        var error = Assert.Throws<InvalidOperationException>(() =>
            CoverAtomCommand.RequireRefreshStatusChangesInsideClosure(
                ["selected-atom", "outside-atom"],
                new HashSet<string>(["selected-atom"], StringComparer.Ordinal)));

        Assert.Equal("status-change-outside-refresh-closure: outside-atom", error.Message);
    }

    [Fact]
    public void PlannedEntryByteChangeBeforeCommitRejectsWithoutWriting()
    {
        var fixture = Stale(new ScribeSeedFixture());
        var before = fixture.Raw(fixture.Document);
        var entryPath = EntryPath(fixture.First);
        var changedEntries = before.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        changedEntries[entryPath] = RawRepositoryEntry.FromText(
            entryPath,
            Encoding.UTF8.GetString(changedEntries[entryPath].Bytes.AsSpan()) + "# concurrent edit\n");
        var changed = RawRepositorySnapshot.Create(changedEntries.Values);

        var execution = Execute(
            fixture,
            ScribeSeedFixture.ModuleGid + "\n",
            currentReads: [before, changed]);

        Assert.False(execution.Result.Success);
        Assert.Contains("changed under us", execution.Result.Error, StringComparison.Ordinal);
        Assert.Equal(2, execution.ReadCurrentCalls);
        Assert.Equal(0, execution.ApplyCalls);
    }

    [Fact]
    public void UnrelatedLedgerByteChangeBeforeCommitIsPreserved()
    {
        var fixture = TwoDocuments();
        var before = fixture.Raw(fixture.Document);
        var outside = Assert.Single(fixture.Document.RequireDigestionEntries(), static entry =>
            entry.CoverageGids.Contains("D5/S0/Carrier/RefreshB.probe", StringComparer.Ordinal));
        var outsidePath = EntryPath(outside);
        var changedEntries = before.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        changedEntries[outsidePath] = RawRepositoryEntry.FromText(
            outsidePath,
            Encoding.UTF8.GetString(changedEntries[outsidePath].Bytes.AsSpan()) + "# concurrent edit\n");
        var changed = RawRepositorySnapshot.Create(changedEntries.Values);

        var execution = Execute(
            fixture,
            "D5/S0/Carrier/RefreshA\n",
            currentReads: [before, changed]);

        Assert.True(execution.Result.Success, execution.Result.Error);
        Assert.Equal(1, execution.ApplyCalls);
        var preserved = Assert.Single(execution.After.Entries, entry => entry.Path == outsidePath);
        Assert.EndsWith("# concurrent edit\n", Encoding.UTF8.GetString(preserved.Bytes.AsSpan()),
            StringComparison.Ordinal);
    }

    [Fact]
    public void DryRunPrintsClosureAndExactWriteSetWithoutWriting()
    {
        var fixture = Stale(new ScribeSeedFixture(2));

        var execution = Execute(
            fixture,
            ScribeSeedFixture.ModuleGid + "\n",
            dryRun: true);

        Assert.True(execution.Result.Success, execution.Result.Error);
        Assert.Equal(2, execution.Result.Output.Split('\n').Count(static line =>
            line.Contains("refresh=needed", StringComparison.Ordinal)));
        Assert.Equal(2, execution.Result.Output.Split('\n').Count(static line =>
            line.StartsWith("SCRIBE_REFRESH_WRITE path=", StringComparison.Ordinal)));
        Assert.Contains("SCRIBE_REFRESH_WRITE_SET count=2", execution.Result.Output, StringComparison.Ordinal);
        Assert.Equal(0, execution.ApplyCalls);
        Assert.Equal(Image(execution.Before), Image(execution.After));
    }

    [Fact]
    public void RefreshIsIdempotent()
    {
        var fixture = Stale(new ScribeSeedFixture());
        var first = Execute(fixture, ScribeSeedFixture.ModuleGid + "\n");
        Assert.True(first.Result.Success, first.Result.Error);
        fixture.Document = Load(first.After);

        var second = Execute(fixture, ScribeSeedFixture.ModuleGid + "\n");

        Assert.True(second.Result.Success, second.Result.Error);
        Assert.Contains("refresh=noop", second.Result.Output, StringComparison.Ordinal);
        Assert.Contains("SCRIBE_REFRESH_WRITE_SET count=0", second.Result.Output, StringComparison.Ordinal);
        Assert.Equal(0, second.ApplyCalls);
        Assert.Equal(Image(second.Before), Image(second.After));
    }

    [Theory]
    [InlineData("")]
    [InlineData("D5/S0/Carrier/Probe")]
    [InlineData("D5/S0/Carrier/Probe\r\n")]
    [InlineData("D5/S0/Carrier/Probe.probe\n")]
    [InlineData(" D5/S0/Carrier/Probe\n")]
    [InlineData("D5/S0/Carrier/Probe\nD5/S0/Carrier/Probe\n")]
    public void RefreshRejectsMalformedDocumentList(string documents)
    {
        var execution = Execute(Stale(new ScribeSeedFixture()), documents);

        Assert.False(execution.Result.Success);
        Assert.Contains("REFRESH_DOCUMENTS_INVALID", execution.Result.Error, StringComparison.Ordinal);
        Assert.Equal(0, execution.ApplyCalls);
    }

    [Fact]
    public void RefreshRejectsUnresolvedDocumentSelection()
    {
        var execution = Execute(
            Stale(new ScribeSeedFixture()),
            "D5/S0/Carrier/Unreferenced\n");

        Assert.False(execution.Result.Success);
        Assert.Contains("document-selection-unresolved", execution.Result.Error,
            StringComparison.Ordinal);
        Assert.Equal(0, execution.ApplyCalls);
    }

    private static ScribeSeedFixture Stale(ScribeSeedFixture fixture)
    {
        fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry with
        {
            Receipts = entry.Receipts with
            {
                Scribe = entry.Coverage.Select(edge => new DigestionScribeReceipt(
                    edge.Gid,
                    "sha256:" + new string('a', 64),
                    "sha256:" + new string('b', 64))).ToImmutableArray(),
            },
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Closed),
        });
        fixture.Baseline = fixture.Document;
        return fixture;
    }

    private static ScribeSeedFixture TwoDocuments()
    {
        var fixture = Stale(new ScribeSeedFixture(moduleGid: "D5/S0/Carrier/RefreshA"));
        var sibling = Stale(new ScribeSeedFixture(moduleGid: "D5/S0/Carrier/RefreshB"));
        foreach (var file in sibling.Files)
        {
            fixture.Files[file.Key] = file.Value;
        }

        var currentSource = Assert.Single(fixture.Document.RequireDigestionSources());
        fixture.Document = fixture.Document.WithDigestionSources([currentSource with
        {
            Entries = fixture.Document.RequireDigestionEntries()
                .AddRange(sibling.Document.RequireDigestionEntries()),
        }]);
        var baselineSource = Assert.Single(fixture.Baseline.RequireDigestionSources());
        fixture.Baseline = fixture.Baseline.WithDigestionSources([baselineSource with
        {
            Entries = fixture.Baseline.RequireDigestionEntries()
                .AddRange(sibling.Baseline.RequireDigestionEntries()),
        }]);
        fixture.Inputs = fixture.Inputs with
        {
            Report = LeanAxiomReport.Create(fixture.Inputs.Report.Files
                .Concat(sibling.Inputs.Report.Files)
                .ToDictionary(static pair => pair.Key.Value, static pair => pair.Value,
                    StringComparer.Ordinal)),
        };
        Assert.True(fixture.Verified.TryGet("D5/S0/Carrier/RefreshA", out var firstRecord));
        Assert.True(sibling.Verified.TryGet("D5/S0/Carrier/RefreshB", out var secondRecord));
        fixture.Verified = VerifiedScribeEmissions.Create(
            [firstRecord, secondRecord],
            ["D5/S0/Carrier/RefreshA.probe", "D5/S0/Carrier/RefreshB.probe"]);
        return fixture;
    }

    private static RefreshExecution Execute(
        ScribeSeedFixture fixture,
        string documents,
        bool dryRun = false,
        RawRepositorySnapshot? baseline = null,
        ImmutableArray<RawRepositorySnapshot> currentReads = default,
        IReadOnlyList<string>? arguments = null)
    {
        var before = fixture.Raw(fixture.Document);
        var after = before;
        var applyCalls = 0;
        var reads = currentReads.IsDefault ? ImmutableArray.Create(before) : currentReads;
        var readIndex = 0;
        var repository = new FakeRepositoryGateway(
            RawChangeSet.Create([]),
            before,
            baseline ?? fixture.Raw(fixture.Baseline),
            currentReader: () => reads[Math.Min(readIndex++, reads.Length - 1)]);
        var commandArguments = arguments?.ToList() ??
        [
            "--refresh", "--documents", DocumentsPath, "--base", "baseline",
        ];
        if (dryRun)
        {
            commandArguments.Add("--dry-run");
        }

        var result = AlignScribeReceiptCommand.Run(
            "synthetic-repository",
            repository,
            new FakeLeanReportSource(fixture.Inputs.Report),
            new FakeScribeEmissionVerifier(fixture.Verified),
            commandArguments,
            (_, path) =>
            {
                Assert.Equal(DocumentsPath, path);
                return ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(documents));
            },
            (_, current, updates) =>
            {
                applyCalls++;
                var files = current.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
                foreach (var update in updates)
                {
                    if (update.Bytes is { } bytes)
                    {
                        files[update.Path] = new RawRepositoryEntry(update.Path, bytes);
                    }
                    else
                    {
                        files.Remove(update.Path);
                    }
                }

                after = RawRepositorySnapshot.Create(files.Values);
            });
        return new RefreshExecution(
            result,
            before,
            after,
            applyCalls,
            repository.ReadCurrentCount);
    }

    private static void AssertRefreshRejected(RefreshExecution execution, string reason)
    {
        Assert.False(execution.Result.Success);
        Assert.Contains(reason, execution.Result.Error, StringComparison.Ordinal);
        Assert.Equal(0, execution.ApplyCalls);
        Assert.Equal(Image(execution.Before), Image(execution.After));
    }

    private static string EntryPath(DigestionLedgerEntry entry) =>
        BackfillInventoryLoader.RootPath + entry.SourceId + "/"
        + DigestionStatusNames.Migration(entry.ProjectedStatus.Migration) + "-"
        + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth) + "/"
        + entry.AtomId + ".yaml";

    private static BackfillInventoryDocument Load(RawRepositorySnapshot raw) =>
        BackfillInventoryLoader.Load(Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(raw)).Snapshot);

    private static string Image(RawRepositorySnapshot snapshot) => string.Concat(snapshot.Entries
        .OrderBy(static entry => entry.Path, StringComparer.Ordinal)
        .Select(static entry => entry.Path + "\0" + Convert.ToBase64String(entry.Bytes.AsSpan()) + "\n"));

    private sealed record RefreshExecution(
        CommandResult Result,
        RawRepositorySnapshot Before,
        RawRepositorySnapshot After,
        int ApplyCalls,
        int ReadCurrentCalls);
}
