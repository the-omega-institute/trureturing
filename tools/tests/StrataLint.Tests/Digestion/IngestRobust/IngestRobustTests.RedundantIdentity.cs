using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestRobustTests
{
    private const string RecoveryText = "**Lemma 10.1 (weighted equality remainder).** Let $v\\in\\mathbb C^4$, $U\\in U(4)$, and put\n\n$$\nK=U\\operatorname{diag}(v),\\qquad\n a_i=|v_i|,\\qquad L=\\sum_{i=1}^4a_i,\\qquad\n t=|\\operatorname{Tr}K|,\\qquad \\tau=L^2-t^2.\n\\tag{10.1}\n$$\n\nThere is a phase $\\lambda\\in\\mathbb C$ with $|\\lambda|=1$ such that\n\n$$\n\\boxed{\\ \\|K-\\lambda\\operatorname{diag}(a_1,a_2,a_3,a_4)\\|_{\\mathrm{HS}}^2\\le2\\tau.\\ }\n\\tag{10.2}\n$$\n\n**Proof.** Choose $\\lambda$ so that $\\overline\\lambda\\operatorname{Tr}K=t$; when $t=0$, choose any unit phase. Set\n\n$$\n r_i=a_i-\\operatorname{Re}\\bigl(\\overline\\lambda\\,U_{ii}v_i\\bigr)\\ge0.\n$$\n\nThe inequalities $|U_{ii}|\\le1$ give the nonnegativity, and $\\sum_i r_i=L-t$. Direct expansion gives\n\n$$\n\\begin{aligned}\n\\|K-\\lambda\\operatorname{diag}(a_i)\\|_{\\mathrm{HS}}^2\n &=2\\sum_i a_i^2-2\\sum_i a_i\\operatorname{Re}\\bigl(\\overline\\lambda\\,U_{ii}v_i\\bigr)\\\\\n &=2\\sum_i a_i r_i\n \\le2L(L-t)\\le2(L+t)(L-t)=2\\tau.\n\\end{aligned}\n$$\n\nThe same calculation covers $L=0$ and zero coordinates. $\\square$\n\n";

    private const string RecoveryGid =
        "D5/S3/Quantum/Recovery/FourPathWeightedEqualityRemainder.weighted_equality_remainder";

    private const string RecoveryStatementId =
        "sha256:88bfe3b5bfcd7dd3bf3d5b264c9cf2d659560aaac499d115570fbf4c55b824a3";

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Ingest_RecoversSameSourceOpenDuplicateAndPreservesCoveredBytesCasAndEdge(bool actualShape)
    {
        var text = actualShape ? RecoveryText : AlphaText;
        var fixture = RedundantIdentityFixture(text: text);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var atomId = Atom(text).Fingerprints.RawSha256[7..];
        if (actualShape)
            Assert.Equal("2ea4a553fb7295410c16bbb5071f46b687c4f12010f984d4fe1a207a47c9cca4", atomId);
        var openPath = Assert.Single(
            fixture.Files.Keys, path => path.StartsWith(SourcePrefix("alpha"), StringComparison.Ordinal)
                && path.EndsWith($"/{atomId}.yaml", StringComparison.Ordinal)
                && path.Contains("/residual-open/", StringComparison.Ordinal));
        var coveredPath = Assert.Single(
            fixture.Files.Keys, path => path.StartsWith(SourcePrefix("alpha"), StringComparison.Ordinal)
                && path.EndsWith($"/{atomId}.yaml", StringComparison.Ordinal)
                && path.Contains("/absorbed-closed/", StringComparison.Ordinal));
        var casPath = DigestionCasStore.RootPath + atomId;
        var coveredBytes = File.ReadAllBytes(Path.Combine(temporary.Path, coveredPath));
        var casBytes = File.ReadAllBytes(Path.Combine(temporary.Path, casPath));
        var before = DirectoryLedgerTestSupport.ReadRepository(temporary);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath])).Ingest(Arguments("alpha"));

        Assert.True(result.Success, result.Error);
        Assert.False(File.Exists(Path.Combine(temporary.Path, openPath)));
        Assert.Equal(
            coveredBytes,
            File.ReadAllBytes(Path.Combine(temporary.Path, coveredPath)));
        Assert.Equal(
            casBytes,
            File.ReadAllBytes(Path.Combine(temporary.Path, casPath)));
        AssertExistingLedgerFilesUnchanged(
            RawRepositorySnapshot.Create(before.Entries.Where(entry => entry.Path != openPath)),
            DirectoryLedgerTestSupport.ReadRepository(temporary));
        var source = BackfillInventoryLoader.LoadRoot(temporary.Path)
            .RequireDigestionSources().Single(source => source.SourceId == "alpha");
        var entry = Assert.Single(source.Entries);
        Assert.Equal([RecoveryGid], entry.CoverageGids.ToArray());
        Assert.Equal(
            RecoveryStatementId,
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
        var generated = DirectoryLedgerTestSupport.ReadRepository(temporary);
        var second = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([AlphaPath]),
                generated,
                generated),
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
        bool mismatchedIdentity = false,
        string text = AlphaText)
    {
        var atom = Atom(text);
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
                    RecoveryStatementId),
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
            Source("alpha", AlphaPath, text) with
            {
                Entries = competingCoverage ? [open, covered, competing] : [open, covered],
            },
            beta);
        return RobustFixture(current, current, text, BetaText);
    }
}
