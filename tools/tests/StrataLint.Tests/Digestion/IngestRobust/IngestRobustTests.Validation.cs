using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestRobustTests
{
    [Fact]
    public void Ingest_SelectedSourceFormatErrorStillFails()
    {
        var fixture = Fixture();
        fixture.Files[AlphaPath] += Addition;
        var dependencies = new ReportFreeIngestDependencies(
            AtomizerResolver: _ => (_, _) =>
                throw new TheorySourceFormatException("selected format failure"));
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath]),
            dependencies).Ingest(Arguments("alpha"));

        Assert.False(result.Success);
        Assert.Contains(
            "source alpha atomization failed: selected format failure",
            result.Error,
            StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    [Fact]
    public void Ingest_WriteSetIsAdditionsOnly()
    {
        var fixture = Fixture();
        fixture.Files[BetaPath] += Addition;
        var beforeLedger = ExistingLedgerFiles(fixture.Files);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);

        var result = Environment(fixture, temporary).Ingest(Arguments());

        Assert.True(result.Success, result.Error);
        var after = Overlay(temporary, fixture);
        AssertExistingLedgerFilesUnchanged(beforeLedger, after);
        var added = after.Entries.Where(item => !fixture.Files.ContainsKey(item.Path)).ToArray();
        Assert.NotEmpty(added);
        Assert.All(added, static item => Assert.True(
            DigestionCasStore.IsCanonicalPath(item.Path)
            || item.Path.Contains("/residual-open/", StringComparison.Ordinal),
            $"unexpected report-free path: {item.Path}"));
    }

    [Theory]
    [InlineData("cas-integrity")]
    [InlineData("write-set-bound")]
    public void Ingest_NewCasIntegrityAndWriteSetBoundFailBeforeAnyWrite(string fault)
    {
        var fixture = Fixture();
        fixture.Files[BetaPath] += Addition;
        var dependencies = new ReportFreeIngestDependencies(
            BeforeValidation: plan => fault switch
            {
                "cas-integrity" => CorruptFirstCas(plan),
                "write-set-bound" => RewriteExistingSourceMetadata(plan),
                _ => throw new ArgumentOutOfRangeException(nameof(fault)),
            });
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([BetaPath]),
            dependencies).Ingest(Arguments("beta"));

        Assert.False(result.Success);
        Assert.Contains("ingest append-only write set contains forbidden path", result.Error);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    [Fact]
    public void Ingest_RetiredFlagsRejected()
    {
        var fixture = Fixture();
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);

        var result = Environment(fixture, temporary).Ingest(
            ["--base", "baseline", "--report-input-state", "changed"]);

        Assert.False(result.Success);
        Assert.Contains("USAGE:", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    private static ReportFreeDigestionIngestPlan CorruptFirstCas(
        ReportFreeDigestionIngestPlan plan)
    {
        var captured = Assert.Single(plan.CasObjects);
        var bytes = captured.Bytes.ToBuilder();
        bytes[0] ^= 0xff;
        return plan with
        {
            CasObjects = [captured with { Bytes = bytes.ToImmutable() }],
        };
    }

    private static ReportFreeDigestionIngestPlan RewriteExistingSourceMetadata(
        ReportFreeDigestionIngestPlan plan)
    {
        var sources = plan.Document.RequireDigestionSources();
        var beta = sources.Single(static source => source.SourceId == "beta");
        var existingId = beta.Entries[0].AtomId;
        return plan with
        {
            Document = plan.Document.WithDigestionSources(sources.Select(source =>
                source.SourceId == "beta"
                    ? source with { AcknowledgedStale = [existingId] }
                    : source).ToImmutableArray()),
        };
    }
}
