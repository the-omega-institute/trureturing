using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestRobustTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Ingest_RecoveryAndNewIntakePreserveExistingInputs(bool actualShape)
    {
        var text = actualShape ? RecoveryText : AlphaText;
        var fixture = RedundantIdentityFixture(text: text);
        fixture.Files[AlphaPath] += Addition;
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.ReadRepository(temporary);
        var openPath = RecoveryOpenPath(text);

        var result = Environment(fixture, temporary).Ingest(Arguments("alpha"));

        Assert.True(result.Success, result.Error);
        Assert.Contains("residual_open_added=1", result.Output, StringComparison.Ordinal);
        var after = DirectoryLedgerTestSupport.ReadRepository(temporary);
        Assert.DoesNotContain(after.Entries, entry => entry.Path == openPath);
        AssertExistingLedgerFilesUnchanged(
            RawRepositorySnapshot.Create(before.Entries.Where(entry => entry.Path != openPath)), after);
        var entries = BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries();
        var addedId = Atom(Addition).Fingerprints.RawSha256[7..];
        var added = Assert.Single(entries, entry => entry.AtomId == addedId);
        Assert.Empty(added.Coverage);
        Assert.Equal(new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open),
            added.ProjectedStatus);
        Assert.Equal(Atom(Addition).RawBytes.ToArray(), File.ReadAllBytes(Path.Combine(
            temporary.Path, DigestionCasStore.RootPath + addedId)));
        var repeated = IngestCommand.RunReportFree(temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create([]), after, after), Arguments("alpha"));
        Assert.True(repeated.Success, repeated.Error);
        Assert.Contains("ledger_changed=false", repeated.Output, StringComparison.Ordinal);
        AssertSameRepository(after, DirectoryLedgerTestSupport.ReadRepository(temporary));
    }

    [Theory]
    [InlineData("unresolved", false)]
    [InlineData("unresolved", true)]
    [InlineData("chain", false)]
    [InlineData("chain", true)]
    [InlineData("tail", false)]
    [InlineData("tail", true)]
    [InlineData("quarantine", false)]
    [InlineData("disposition", false)]
    [InlineData("nonpropositional", false)]
    public void Ingest_RecoveryRejectsNonemptyReceiptsBeforeWrites(string receipt, bool covered)
    {
        var fixture = RedundantIdentityFixture();
        TransformRecoveryEntries(fixture, entry =>
        {
            if ((!entry.Coverage.IsEmpty) != covered) return entry;
            return entry with
            {
                Receipts = receipt switch
                {
                    "unresolved" => entry.Receipts with { UnresolvedSubitems = ["pending"] },
                    "chain" => entry.Receipts with { ChainAtoms = [new string('a', 64)] },
                    "tail" => entry.Receipts with
                    {
                        TailAuthorization = new DigestionExternalReceipt("receipt.json", "sha256:" + new string('b', 64)),
                    },
                    "quarantine" => entry.Receipts with
                    {
                        Quarantine = new DigestionQuarantine("blocked", "resolved", "missing-prerequisite"),
                    },
                    "disposition" => entry.Receipts with
                    {
                        CoverDisposition = new DigestionCoverDisposition(entry.ProjectedStatus, [], []),
                    },
                    "nonpropositional" => entry.Receipts with
                    {
                        Nonpropositional = new DigestionNonpropositional("upstream only", null, null),
                    },
                    _ => throw new ArgumentOutOfRangeException(nameof(receipt)),
                },
            };
        });
        AssertRecoveryRejectedWithoutWrites(fixture);
    }

    [Theory]
    [InlineData("raw")]
    [InlineData("cas")]
    [InlineData("normalized")]
    [InlineData("unbound-coverage")]
    [InlineData("partial")]
    [InlineData("tail")]
    [InlineData("open-coverage")]
    public void Ingest_RecoveryRejectsUnsupportedIdentityAndStates(string fault)
    {
        var fixture = RedundantIdentityFixture();
        TransformRecoveryEntries(fixture, entry => fault switch
        {
            "raw" => entry with { Fingerprints = entry.Fingerprints with { RawSha256 = "sha256:" + new string('9', 64) } },
            "cas" => entry with { CasRef = "sha256:" + new string('9', 64) },
            "normalized" => entry with { Fingerprints = entry.Fingerprints with { NormalizedSha256 = "invalid" } },
            "unbound-coverage" when !entry.Coverage.IsEmpty => entry with { Coverage = [new(RecoveryGid, null)] },
            "partial" when !entry.Coverage.IsEmpty => entry with
            {
                ProjectedStatus = new(DigestionMigrationState.Partial, DigestionTruthState.Closed),
            },
            "tail" when !entry.Coverage.IsEmpty => entry with
            {
                ProjectedStatus = new(DigestionMigrationState.Absorbed, DigestionTruthState.Tail),
            },
            "open-coverage" when entry.Coverage.IsEmpty => entry with { Coverage = [new(RecoveryGid, RecoveryStatementId)] },
            _ => entry,
        });
        AssertRecoveryRejectedWithoutWrites(fixture);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Ingest_RecoveryRejectsForeignOrUnselectedDuplicatePairs(bool bothForeign)
    {
        var fixture = RedundantIdentityFixture();
        var document = BackfillInventoryLoader.LoadForDigestion(Decode(Raw(fixture.Files)));
        var alpha = document.RequireDigestionSources().Single(source => source.SourceId == "alpha");
        var beta = document.RequireDigestionSources().Single(source => source.SourceId == "beta");
        var moved = alpha.Entries.Where(entry => bothForeign || !entry.Coverage.IsEmpty).ToArray();
        alpha = alpha with { Entries = [.. alpha.Entries.Except(moved)] };
        beta = beta with
        {
            Entries = [.. beta.Entries, .. moved.Select(entry => entry with { SourceId = "beta", SourcePath = BetaPath })],
        };
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Files, TwoSourceLedger(alpha, beta));
        AssertRecoveryRejectedWithoutWrites(fixture);
    }

    [Fact]
    public void Ingest_RecoveryRejectsMissingCasBeforeWrites()
    {
        var fixture = RedundantIdentityFixture();
        fixture.Files.Remove(DigestionCasStore.RootPath + Atom(AlphaText).Fingerprints.RawSha256[7..]);
        AssertRecoveryRejectedWithoutWrites(fixture);
    }

    [Theory]
    [InlineData("open", false)]
    [InlineData("open", true)]
    [InlineData("covered", false)]
    [InlineData("covered", true)]
    [InlineData("cas", false)]
    [InlineData("cas", true)]
    [InlineData("source", false)]
    [InlineData("metadata", false)]
    public void Ingest_RecoveryRejectsPhysicalInputChangesAndPreservesConcurrentBytes(string input, bool delete)
    {
        var fixture = RedundantIdentityFixture();
        fixture.Files[AlphaPath] += Addition;
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var openPath = RecoveryOpenPath(AlphaText);
        var path = input switch
        {
            "open" => openPath,
            "covered" => openPath.Replace("/residual-open/", "/absorbed-closed/", StringComparison.Ordinal),
            "cas" => DigestionCasStore.RootPath + Atom(AlphaText).Fingerprints.RawSha256[7..],
            "source" => AlphaPath,
            "metadata" => SourcePrefix("alpha") + "source.toml",
            _ => throw new ArgumentOutOfRangeException(nameof(input)),
        };
        string? concurrent = null;
        var dependencies = new ReportFreeIngestDependencies(BeforeCommit: () =>
        {
            var fullPath = Path.Combine(temporary.Path, path);
            if (delete) File.Delete(fullPath);
            else File.AppendAllText(fullPath, "concurrent edit\n");
            concurrent = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        });

        var result = Environment(fixture, temporary, dependencies: dependencies).Ingest(Arguments("alpha"));

        Assert.False(result.Success);
        Assert.Contains("changed under us: " + path, result.Error, StringComparison.Ordinal);
        Assert.NotNull(concurrent);
        Assert.Equal(concurrent, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        Assert.Empty(Directory.EnumerateFiles(temporary.Path, "*.tmp", SearchOption.AllDirectories));
    }

    [Fact]
    public void Ingest_RecoveryPublicationFailureRollsBackNewIntakeAndCas()
    {
        var fixture = RedundantIdentityFixture();
        fixture.Files[AlphaPath] += Addition;
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var attempts = 0;
        var dependencies = new ReportFreeIngestDependencies(CommitLedgerFile: (pending, target) =>
        {
            if (++attempts == 2) throw new IOException("injected recovery publication failure");
            File.Move(pending, target, overwrite: false);
        });

        var result = Environment(fixture, temporary, dependencies: dependencies).Ingest(Arguments("alpha"));

        Assert.False(result.Success);
        Assert.Equal(2, attempts);
        Assert.Contains("injected recovery publication failure", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        Assert.Empty(Directory.EnumerateFiles(temporary.Path, "*.tmp", SearchOption.AllDirectories));
    }

    [Fact]
    public void RecoveryDeletionUsesExistingTransactionRollback()
    {
        var fixture = RedundantIdentityFixture();
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.ReadRepository(temporary);
        var openPath = RecoveryOpenPath(AlphaText);
        var newPath = SourcePrefix("alpha") + "residual-open/" + new string('9', 64) + ".yaml";

        Assert.Throws<IOException>(() => IngestCommand.ApplyLedgerUpdatesAtomically(temporary.Path, before,
            [new(openPath, null), new(newPath, [.. Encoding.UTF8.GetBytes("pending")], 1)],
            (_, _) =>
            {
                Assert.False(File.Exists(Path.Combine(temporary.Path, openPath)));
                throw new IOException("failure after recovery deletion");
            }));

        AssertSameRepository(before, DirectoryLedgerTestSupport.ReadRepository(temporary));
        Assert.Empty(Directory.EnumerateFiles(temporary.Path, "*.tmp", SearchOption.AllDirectories));
    }

    private static string RecoveryOpenPath(string text) =>
        SourcePrefix("alpha") + "residual-open/" + Atom(text).Fingerprints.RawSha256[7..] + ".yaml";

    private static void TransformRecoveryEntries(RuleFixture fixture, Func<DigestionLedgerEntry, DigestionLedgerEntry> transform)
    {
        var document = BackfillInventoryLoader.LoadForDigestion(Decode(Raw(fixture.Files)));
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Files,
            document.WithDigestionSources([.. document.RequireDigestionSources().Select(source => source.SourceId == "alpha"
                ? source with { Entries = [.. source.Entries.Select(transform)] } : source)]));
    }

    private static void AssertRecoveryRejectedWithoutWrites(RuleFixture fixture)
    {
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var result = Environment(fixture, temporary).Ingest(Arguments("alpha"));
        Assert.False(result.Success);
        Assert.Contains("INGEST_INVALID", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }
}
