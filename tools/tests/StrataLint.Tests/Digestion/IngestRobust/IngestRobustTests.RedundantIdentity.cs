using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestRobustTests
{
    private const string RecoveryGid =
        "D5/S3/Quantum/Recovery/FourPathWeightedEqualityRemainder.weighted_equality_remainder";

    [Fact]
    public void Ingest_RecoversSameSourceOpenDuplicateAndPreservesCoveredBytesCasAndEdge()
    {
        var fixture = RedundantIdentityFixture();
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var atomId = Atom(AlphaText).Fingerprints.RawSha256[7..];
        var openPath = Assert.Single(
            fixture.Files.Keys.Where(path => path.StartsWith(SourcePrefix("alpha"), StringComparison.Ordinal)
                && path.EndsWith($"/{atomId}.yaml", StringComparison.Ordinal)
                && path.Contains("/residual-open/", StringComparison.Ordinal)));
        var coveredPath = Assert.Single(
            fixture.Files.Keys.Where(path => path.StartsWith(SourcePrefix("alpha"), StringComparison.Ordinal)
                && path.EndsWith($"/{atomId}.yaml", StringComparison.Ordinal)
                && path.Contains("/absorbed-closed/", StringComparison.Ordinal)));
        var casPath = DigestionCasStore.RootPath + atomId;
        var coveredBytes = fixture.Files[coveredPath];
        var casBytes = fixture.Files[casPath];

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath])).Ingest(Arguments("alpha"));

        Assert.True(result.Success, result.Error);
        Assert.False(File.Exists(Path.Combine(temporary.Path, openPath)));
        Assert.Equal(
            coveredBytes,
            File.ReadAllText(Path.Combine(temporary.Path, coveredPath)));
        Assert.Equal(
            casBytes,
            File.ReadAllText(Path.Combine(temporary.Path, casPath)));
        var source = BackfillInventoryLoader.LoadRoot(temporary.Path)
            .RequireDigestionSources().Single(source => source.SourceId == "alpha");
        var entry = Assert.Single(source.Entries);
        Assert.Equal([RecoveryGid], entry.CoverageGids.ToArray());
        Assert.Equal(
            "sha256:" + new string('8', 64),
            entry.Coverage.Single().TargetStatementId);
    }

    [Fact]
    public void Ingest_RecoversDuplicateIdempotentlyAfterTheOpenOccurrenceIsGone()
    {
        var fixture = RedundantIdentityFixture();
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var first = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath])).Ingest(Arguments("alpha"));
        Assert.True(first.Success, first.Error);
        var afterFirst = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var generated = DirectoryLedgerTestSupport.OverlayRepositoryFiles(temporary, fixture.Files);
        var second = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([AlphaPath]),
                Raw(generated),
                Raw(generated)),
            new FakeLeanReportSource(null),
            new FakeScribeEmissionVerifier(null));

        var secondResult = second.Ingest(Arguments("alpha"));

        Assert.True(secondResult.Success, secondResult.Error);
        Assert.Contains("ledger_changed=false", secondResult.Output, StringComparison.Ordinal);
        Assert.Equal(afterFirst, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    [Fact]
    public void Ingest_RejectsCompetingCoveredDuplicatesBeforeAnyWrite()
    {
        var fixture = RedundantIdentityFixture(competingCoverage: true);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath])).Ingest(Arguments("alpha"));

        Assert.False(result.Success);
        Assert.Contains("cannot recover duplicate atom id", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    [Fact]
    public void Ingest_RejectsMismatchedDuplicateIdentityBeforeAnyWrite()
    {
        var fixture = RedundantIdentityFixture(mismatchedIdentity: true);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath])).Ingest(Arguments("alpha"));

        Assert.False(result.Success);
        Assert.Contains("source identity, fingerprints, or CAS differ", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    private static RuleFixture RedundantIdentityFixture(
        bool competingCoverage = false,
        bool mismatchedIdentity = false)
    {
        var atom = Atom(AlphaText);
        var open = DigestionTestSupport.Entry(
            atom,
            atom.Fingerprints.RawSha256[7..],
            AtomizerRegistry.GenericId,
            sourceId: "alpha",
            sourcePath: AlphaPath);
        var covered = open with
        {
            Fingerprints = mismatchedIdentity
                ? open.Fingerprints with { NormalizedSha256 = "sha256:" + new string('9', 64) }
                : open.Fingerprints,
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Closed),
            Coverage =
            [
                new DigestionCoverageEdge(
                    RecoveryGid,
                    competingCoverage ? null : "sha256:" + new string('8', 64)),
            ],
        };
        var competing = covered with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Closed),
            Coverage =
            [
                new DigestionCoverageEdge(
                    "D5/S3/Quantum/Recovery/Competing.other",
                    "sha256:" + new string('7', 64)),
            ],
        };
        var beta = Source("beta", BetaPath, BetaText);
        var current = TwoSourceLedger(
            Source("alpha", AlphaPath, AlphaText) with
            {
                Entries = competingCoverage ? [open, covered, competing] : [open, covered],
            },
            beta);
        return RobustFixture(current, current, AlphaText, BetaText);
    }
}
