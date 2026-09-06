using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ScribeSeedCommandTests
{
    [Fact]
    public void SeedDeclarationReceiptUsesVerifiedBuilderAndDerivesAbsorption()
    {
        var fixture = new ScribeSeedFixture();
        var execution = Execute(fixture);

        Assert.True(execution.Result.Success, execution.Result.Error);
        Assert.Equal(1, execution.ApplyCalls);
        var entry = Assert.Single(Load(execution.After).RequireDigestionEntries());
        Assert.Equal(fixture.First.Coverage.ToArray(), entry.Coverage.ToArray());
        Assert.Equal(new DigestionScribeReceipt(ScribeSeedFixture.DeclarationGid,
            DigestionFingerprint.Compute(Encoding.UTF8.GetBytes("scribe definition\n")).RawSha256,
            DigestionFingerprint.Compute(Encoding.UTF8.GetBytes("# emitted narrative\n")).RawSha256),
            Assert.Single(entry.Receipts.Scribe));
        Assert.Equal(new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
            entry.ProjectedStatus);
        Assert.Contains("eligibility=eligible", execution.Result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void SeedModuleReceiptRequiresModuleEmissionWithoutDeclarationReference()
    {
        var fixture = new ScribeSeedFixture(module: true);
        var execution = Execute(fixture);

        Assert.True(execution.Result.Success, execution.Result.Error);
        var entry = Assert.Single(Load(execution.After).RequireDigestionEntries());
        Assert.Equal(ScribeSeedFixture.ModuleGid, Assert.Single(entry.Receipts.Scribe).Gid);
        Assert.Equal(DigestionMigrationState.Absorbed, entry.ProjectedStatus.Migration);
    }

    [Fact]
    public void SeedPreservesUnresolvedSubitemsAndLeavesPartialStatus()
    {
        var fixture = new ScribeSeedFixture();
        fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry with
        {
            Receipts = entry.Receipts with { UnresolvedSubitems = ["pending-clause"] },
        });
        fixture.Baseline = fixture.Document;

        var execution = Execute(fixture);

        Assert.True(execution.Result.Success, execution.Result.Error);
        var entry = Assert.Single(Load(execution.After).RequireDigestionEntries());
        Assert.Equal(["pending-clause"], entry.Receipts.UnresolvedSubitems.ToArray());
        Assert.Single(entry.Receipts.Scribe);
        Assert.Equal(DigestionMigrationState.Partial, entry.ProjectedStatus.Migration);
    }

    [Fact]
    public void ExistingRefreshStillReplacesFingerprintsAndIsIdempotent()
    {
        var fixture = new ScribeSeedFixture();
        SetReceipts(fixture, 1);
        fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry with
        {
            ProjectedStatus = new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
        });
        fixture.Baseline = fixture.Document;
        var arguments = new[] { "--atom-id", fixture.First.AtomId, "--gid",
            ScribeSeedFixture.DeclarationGid, "--base", "baseline" };

        var execution = Execute(fixture, arguments);

        Assert.True(execution.Result.Success, execution.Result.Error);
        Assert.Contains("old_definition_sha256=sha256:aaaa", execution.Result.Output, StringComparison.Ordinal);
        Assert.True(fixture.Verified.TryGet(ScribeSeedFixture.ModuleGid, out var verified));
        var entry = Assert.Single(Load(execution.After).RequireDigestionEntries());
        Assert.Equal(verified.DefinitionSha256, Assert.Single(entry.Receipts.Scribe).DefinitionSha256);
        Assert.Equal(verified.EmissionSha256, Assert.Single(entry.Receipts.Scribe).EmissionSha256);
        Assert.Equal(DigestionMigrationState.Absorbed, entry.ProjectedStatus.Migration);
        fixture.Document = Load(execution.After);
        var replay = Execute(fixture, arguments);
        Assert.True(replay.Result.Success, replay.Result.Error);
        Assert.Contains("ledger_changed=false", replay.Result.Output, StringComparison.Ordinal);
        Assert.Equal(Image(replay.Before), Image(replay.After));
    }

    [Theory]
    [InlineData("existing-receipt", "SEED_RECEIPT_PRESENT")]
    [InlineData("duplicate-receipts", "SEED_RECEIPT_PRESENT")]
    [InlineData("missing-edge", "SEED_EDGE_AMBIGUOUS")]
    [InlineData("duplicate-edges", "SEED_EDGE_AMBIGUOUS")]
    [InlineData("missing-definition", "missing-definition")]
    [InlineData("missing-emission", "missing-emission")]
    [InlineData("missing-declaration-reference", "missing-declaration-reference")]
    [InlineData("missing-frozen-statement", "SEED_EDGE_NOT_CLOSED")]
    [InlineData("open-statement", "SEED_EDGE_NOT_CLOSED")]
    [InlineData("stale-target", "SEED_TARGET_MISMATCH")]
    [InlineData("absent-atom", "SEED_ATOM_AMBIGUOUS")]
    public void SeedRejectsIneligiblePairWithoutChangingAnyBytes(string scenario, string expected)
    {
        var fixture = new ScribeSeedFixture();
        MakeIneligible(fixture, scenario);
        var arguments = new[] { "--seed-missing", "--atom",
            scenario == "absent-atom" ? new string('a', 64) : fixture.First.AtomId,
            "--gid", ScribeSeedFixture.DeclarationGid, "--base", "baseline" };

        var execution = Execute(fixture, arguments);

        Assert.False(execution.Result.Success);
        Assert.Contains(expected, execution.Result.Error, StringComparison.Ordinal);
        Assert.Equal(0, execution.ApplyCalls);
        Assert.Equal(Image(execution.Before), Image(execution.After));
    }

    [Fact]
    public void SeedBatchRejectsAllPairsWhenOneIsIneligible()
    {
        var fixture = new ScribeSeedFixture(2);
        var first = fixture.First;
        var second = fixture.Document.RequireDigestionEntries()[1];
        fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry.AtomId == second.AtomId
            ? entry with { Coverage = [] } : entry);

        var execution = Execute(fixture, BatchArgs(),
            $"{first.AtomId}\t{ScribeSeedFixture.DeclarationGid}\n"
            + $"{second.AtomId}\t{ScribeSeedFixture.DeclarationGid}\n");

        Assert.False(execution.Result.Success);
        Assert.Contains("SEED_EDGE_AMBIGUOUS", execution.Result.Error, StringComparison.Ordinal);
        Assert.Equal(0, execution.ApplyCalls);
        Assert.Equal(Image(execution.Before), Image(execution.After));
    }

    [Fact]
    public void SeedBatchCommitsAllEligiblePairsInOneTransaction()
    {
        var fixture = new ScribeSeedFixture(2);
        var pairs = string.Concat(fixture.Document.RequireDigestionEntries().Select(entry =>
            $"{entry.AtomId}\t{ScribeSeedFixture.DeclarationGid}\n"));

        var execution = Execute(fixture, BatchArgs(), pairs);

        Assert.True(execution.Result.Success, execution.Result.Error);
        Assert.Equal(1, execution.ApplyCalls);
        Assert.All(Load(execution.After).RequireDigestionEntries(), entry =>
        {
            Assert.Single(entry.Receipts.Scribe);
            Assert.Equal(DigestionMigrationState.Absorbed, entry.ProjectedStatus.Migration);
        });
    }

    [Theory]
    [InlineData("")]
    [InlineData("atom gid\n")]
    [InlineData("atom\tgid\textra\n")]
    [InlineData("atom\tgid\r\n")]
    [InlineData("atom\tgid")]
    public void SeedBatchRejectsMalformedTsvWithoutWriting(string pairs)
    {
        var execution = Execute(new ScribeSeedFixture(), BatchArgs(), pairs);

        Assert.False(execution.Result.Success);
        Assert.Contains("SEED_PAIRS_INVALID", execution.Result.Error, StringComparison.Ordinal);
        Assert.Equal(0, execution.ApplyCalls);
        Assert.Equal(Image(execution.Before), Image(execution.After));
    }

    [Fact]
    public void SeedBatchRejectsDuplicatePairsWithoutWriting()
    {
        var fixture = new ScribeSeedFixture();
        var row = $"{fixture.First.AtomId}\t{ScribeSeedFixture.DeclarationGid}\n";
        var execution = Execute(fixture, BatchArgs(), row + row);

        Assert.False(execution.Result.Success);
        Assert.Contains("SEED_PAIRS_INVALID", execution.Result.Error, StringComparison.Ordinal);
        Assert.Equal(0, execution.ApplyCalls);
        Assert.Equal(Image(execution.Before), Image(execution.After));
    }

    [Fact]
    public void DryRunPartitionsAllFiveEligibilityStatesWithoutWriting()
    {
        string[] states = ["eligible", "missing-definition", "missing-emission",
            "missing-declaration-reference", "ambiguous-edge"];
        var fixtures = Enumerable.Range(0, states.Length).Select(index =>
            new ScribeSeedFixture(moduleGid: "D5/S0/Carrier/Probe" + index)).ToArray();
        var records = fixtures.Select(fixture =>
        {
            Assert.True(fixture.Verified.TryGet(
                ScribeEmissionAttestation.DocumentGid(fixture.First.Coverage[0].Gid), out var record));
            return record;
        }).ToArray();
        fixtures[1].Files.Remove(records[1].DefinitionPath);
        fixtures[4].Document = ScribeSeedFixture.Map(fixtures[4].Document, entry => entry with { Coverage = [] });
        var combined = fixtures[0];
        foreach (var fixture in fixtures.Skip(1))
        {
            foreach (var file in fixture.Files)
            {
                combined.Files[file.Key] = file.Value;
            }
        }
        var source = Assert.Single(combined.Document.RequireDigestionSources());
        combined.Document = combined.Document.WithDigestionSources([source with
        {
            Entries = fixtures.SelectMany(fixture => fixture.Document.RequireDigestionEntries()).ToImmutableArray(),
        }]);
        combined.Baseline = combined.Document;
        combined.Inputs = combined.Inputs with
        {
            Report = LeanAxiomReport.Create(fixtures.SelectMany(fixture => fixture.Inputs.Report.Files)
                .ToDictionary(static pair => pair.Key.Value, static pair => pair.Value, StringComparer.Ordinal)),
        };
        combined.Verified = VerifiedScribeEmissions.Create(
            records.Where((_, index) => index != 2), [records[0].Gid + ".probe"]);
        var pairs = string.Concat(fixtures.Select((fixture, index) =>
            $"{fixture.Baseline.RequireDigestionEntries()[0].AtomId}\t{records[index].Gid}.probe\n"));

        var execution = Execute(combined, [.. BatchArgs(), "--dry-run"], pairs);

        Assert.True(execution.Result.Success, execution.Result.Error);
        foreach (var state in states)
        {
            Assert.Single(execution.Result.Output.Split('\n'), line =>
                line.Contains("eligibility=" + state, StringComparison.Ordinal));
        }
        Assert.Equal(0, execution.ApplyCalls);
        Assert.Equal(Image(execution.Before), Image(execution.After));
    }

    private static string[] BatchArgs() => ["--seed-missing", "--pairs", "pairs.tsv", "--base", "baseline"];

    private static void SetReceipts(ScribeSeedFixture fixture, int count)
    {
        fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry with
        {
            Receipts = entry.Receipts with
            {
                Scribe = Enumerable.Repeat(new DigestionScribeReceipt(entry.Coverage[0].Gid,
                    "sha256:" + new string('a', 64), "sha256:" + new string('b', 64)), count).ToImmutableArray(),
            },
        });
        fixture.Baseline = fixture.Document;
    }

    private static void MakeIneligible(ScribeSeedFixture fixture, string scenario)
    {
        switch (scenario)
        {
            case "existing-receipt": SetReceipts(fixture, 1); break;
            case "duplicate-receipts": SetReceipts(fixture, 2); break;
            case "missing-edge":
                fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry with { Coverage = [] });
                break;
            case "duplicate-edges":
                fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry with
                { Coverage = entry.Coverage.Add(entry.Coverage[0]) });
                break;
            case "missing-definition":
                fixture.Files.Remove(ScribeEmissionAttestation.DefinitionPath(ScribeSeedFixture.ModuleGid));
                break;
            case "missing-emission": fixture.Verified = VerifiedScribeEmissions.Empty; break;
            case "missing-declaration-reference":
                Assert.True(fixture.Verified.TryGet(ScribeSeedFixture.ModuleGid, out var record));
                fixture.Verified = VerifiedScribeEmissions.Create([record]);
                break;
            case "missing-frozen-statement":
                foreach (var path in fixture.Files.Keys.Where(path => path.StartsWith("Golden/Frozen/", StringComparison.Ordinal)).ToArray())
                    fixture.Files.Remove(path);
                break;
            case "open-statement":
                fixture.Inputs = fixture.Inputs with
                {
                    Report = LeanAxiomReport.Create(fixture.Inputs.Report.Files.ToDictionary(
                        static pair => pair.Key.Value,
                        static pair => pair.Value with
                        {
                            Declarations = pair.Value.Declarations.Select(declaration => declaration with
                            { Axioms = ["sorryAx"] }).ToImmutableArray(),
                        })),
                };
                break;
            case "stale-target":
                fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry with
                { Coverage = [entry.Coverage[0] with { TargetStatementId = "sha256:" + new string('0', 64) }] });
                break;
        }
    }

    private static string Image(RawRepositorySnapshot snapshot) => string.Concat(snapshot.Entries
        .OrderBy(static entry => entry.Path, StringComparer.Ordinal)
        .Select(static entry => entry.Path + "\0" + Convert.ToBase64String(entry.Bytes.AsSpan()) + "\n"));

    private static SeedExecution Execute(
        ScribeSeedFixture fixture,
        IReadOnlyList<string>? arguments = null,
        string? pairs = null)
    {
        var before = fixture.Raw(fixture.Document);
        var after = before;
        var applyCalls = 0;
        var repository = new FakeRepositoryGateway(
            RawChangeSet.Create([ScribeSeedFixture.EntryPath(fixture.First)]),
            before, fixture.Raw(fixture.Baseline));
        var result = AlignScribeReceiptCommand.Run(
            "synthetic-repository", repository, new FakeLeanReportSource(fixture.Inputs.Report),
            new FakeScribeEmissionVerifier(fixture.Verified),
            arguments ?? ["--seed-missing", "--atom", fixture.First.AtomId, "--gid",
                fixture.First.Coverage[0].Gid, "--base", "baseline"],
            (_, path) =>
            {
                Assert.Equal("pairs.tsv", path);
                return ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(pairs!));
            },
            (_, current, updates) =>
            {
                applyCalls++;
                Assert.Equal(Image(before), Image(current));
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
        return new SeedExecution(result, before, after, applyCalls);
    }

    private static BackfillInventoryDocument Load(RawRepositorySnapshot raw) =>
        BackfillInventoryLoader.Load(Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(raw)).Snapshot);

    private sealed record SeedExecution(
        CommandResult Result, RawRepositorySnapshot Before, RawRepositorySnapshot After, int ApplyCalls);
}

internal sealed class ScribeSeedFixture
{
    internal const string ModuleGid = "D5/S0/Carrier/Probe";
    internal const string DeclarationGid = ModuleGid + ".probe";
    internal CoverInputs Inputs { get; set; }
    internal Dictionary<string, string> Files { get; }
    internal BackfillInventoryDocument Document { get; set; }
    internal BackfillInventoryDocument Baseline { get; set; }
    internal VerifiedScribeEmissions Verified { get; set; }
    internal DigestionLedgerEntry First => Document.RequireDigestionEntries()[0];

    internal ScribeSeedFixture(int count = 1, bool module = false, string moduleGid = ModuleGid)
    {
        var gid = module ? moduleGid : moduleGid + ".probe";
        Inputs = CoverWorld.Materialize(new CoverSpec
        {
            ModuleGid = moduleGid,
            Declaration = module ? null : "probe",
            InitialCoverage = [gid],
            Migration = "partial",
            Truth = "closed",
            BaselineTargetIdentical = true,
        });
        Files = new Dictionary<string, string>(Inputs.Files, StringComparer.Ordinal);
        Files[TheoryAtomizerDataLoader.DataPath] = Encoding.UTF8.GetString(DigestionTestSupport.RulesBytes);
        Verified = Inputs.VerifiedEmissions!;
        var template = Assert.Single(Inputs.Document.RequireDigestionEntries());
        Files.Remove(DigestionCasStore.RootPath + template.AtomId);
        var entries = Enumerable.Range(0, count).Select(index =>
        {
            var bytes = Encoding.UTF8.GetBytes($"synthetic receipt obligation {moduleGid} {index}\n");
            var fingerprint = DigestionFingerprint.Compute(bytes);
            var id = fingerprint.RawSha256["sha256:".Length..];
            Files[DigestionCasStore.RootPath + id] = Encoding.UTF8.GetString(bytes);
            return template with
            {
                AtomId = id,
                Atomizer = AtomizerRegistry.NoAtomizerId,
                Fingerprints = fingerprint,
                CasRef = fingerprint.RawSha256,
            };
        }).ToImmutableArray();
        var source = Assert.Single(Inputs.Document.RequireDigestionSources()) with
        {
            Atomizer = AtomizerRegistry.NoAtomizerId,
            GenreRegistryProjection = GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
            Entries = entries,
        };
        Document = Inputs.Document.WithDigestionSources([source]);
        Baseline = Document;
    }

    internal static BackfillInventoryDocument Map(
        BackfillInventoryDocument document,
        Func<DigestionLedgerEntry, DigestionLedgerEntry> transform) =>
        document.WithDigestionSources(document.RequireDigestionSources().Select(source =>
            source with { Entries = source.Entries.Select(transform).ToImmutableArray() }).ToImmutableArray());

    internal RawRepositorySnapshot Raw(BackfillInventoryDocument document)
    {
        var files = new Dictionary<string, string>(Files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, document);
        return RawRepositorySnapshot.Create(files.Select(static pair =>
            RawRepositoryEntry.FromText(pair.Key, pair.Value)));
    }

    internal FakeRepositoryGateway Gateway(RawChangeSet changes) =>
        new(changes, Raw(Document), Raw(Baseline));

    internal static string EntryPath(DigestionLedgerEntry entry) =>
        BackfillInventoryLoader.RootPath + entry.SourceId + "/partial-closed/" + entry.AtomId + ".yaml";
}
