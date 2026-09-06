using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestRobustTests
{
    [Theory]
    [InlineData("deleted")]
    [InlineData("bytes")]
    public void Ingest_RepositorySnapshotReflectsLivePathsAndRawBytes(string fault)
    {
        var document = Ledger();
        var fixture = Fixture(document);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var path = AtomPath(document.RequireDigestionSources()[0].Entries[0]);
        byte[] bytes = [0xff, 0xfe, 0x00, 0x61, 0x80];
        if (fault == "deleted") File.Delete(Path.Combine(temporary.Path, path));
        else File.WriteAllBytes(Path.Combine(temporary.Path, path), bytes);

        var snapshot = DirectoryLedgerTestSupport.ReadRepository(temporary);

        if (fault == "deleted") Assert.DoesNotContain(snapshot.Entries, entry => entry.Path == path);
        else Assert.Equal(bytes, Assert.Single(snapshot.Entries, entry => entry.Path == path).Bytes.ToArray());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Ingest_ConcurrentCrossSourceSameAtomIsNotDuplicated_AllAndSource(bool sourceScoped)
    {
        var fixture = Fixture();
        fixture.Files[AlphaPath] += Addition;
        fixture.Files[BetaPath] += Addition;
        var atomId = Atom(Addition).Fingerprints.RawSha256["sha256:".Length..];
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        string? afterWinner = null;
        var dependencies = new ReportFreeIngestDependencies(BeforeValidation: plan =>
        {
            Assert.Contains(atomId, plan.AddedAtomIds);
            var winner = Environment(fixture, temporary).Ingest(Arguments("beta"));
            Assert.True(winner.Success, winner.Error);
            var entry = Assert.Single(BackfillInventoryLoader.LoadRoot(temporary.Path)
                .RequireDigestionEntries(), entry => entry.AtomId == atomId);
            Assert.Equal("beta", entry.SourceId);
            afterWinner = DirectoryLedgerTestSupport.RepositoryImage(temporary);
            return plan;
        });

        var result = Environment(fixture, temporary, dependencies: dependencies).Ingest(
            sourceScoped ? Arguments("alpha") : Arguments());

        Assert.False(result.Success);
        Assert.Contains($"atom id {atomId} already registered by beta since planning", result.Error,
            StringComparison.Ordinal);
        Assert.NotNull(afterWinner);
        Assert.Equal(afterWinner, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        var paths = Directory.EnumerateFiles(
            Path.Combine(temporary.Path, BackfillInventoryLoader.RootPath),
            atomId + ".yaml", SearchOption.AllDirectories).ToArray();
        Assert.Equal(Path.Combine(temporary.Path, SourcePrefix("beta"), "residual-open", atomId + ".yaml"),
            Assert.Single(paths));
        Assert.Equal(Atom(Addition).RawBytes.ToArray(),
            File.ReadAllBytes(Path.Combine(temporary.Path, DigestionCasStore.RootPath, atomId)));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Ingest_SelectedMalformedSourceFailsEvenWhenOtherSourceOwnsContentHash(bool includeGamma)
    {
        const string malformed = "**Claim 1.1 malformed**\n\nAlpha content.\n";
        const string gammaPath = "docs/develop/theory/GAMMA.md";
        var bytes = Encoding.UTF8.GetBytes(malformed);
        Assert.Throws<TheorySourceFormatException>(() =>
            ConeAtomizer.Atomize(bytes, DigestionTestSupport.Rules));
        var opaque = DigestionAtom.FromFrozenCas(
            ImmutableArray.CreateRange(bytes), DigestionFingerprint.ComputeOpaque(bytes));
        var holder = DigestionTestSupport.Entry(opaque, opaque.Fingerprints.RawSha256[7..],
            AtomizerRegistry.NoAtomizerId, sourceId: "beta", sourcePath: BetaPath);
        var alpha = Source("alpha", AlphaPath, AlphaText) with { Atomizer = AtomizerRegistry.ConeId };
        var document = BackfillInventoryDocument.Create(
        [
            alpha,
            EmptySource("beta", BetaPath) with { Atomizer = AtomizerRegistry.NoAtomizerId, Entries = [holder] },
            EmptySource("gamma", gammaPath),
        ], []);
        Assert.DoesNotContain(alpha.Entries, entry => entry.AtomId == holder.AtomId);
        var fixture = Fixture(document);
        fixture.Files[AlphaPath] = malformed;
        fixture.Files[gammaPath] = Addition;
        fixture.Baseline[gammaPath] = Addition;
        AddCas(fixture.Files, opaque);
        AddCas(fixture.Baseline, opaque);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);

        var result = Environment(fixture, temporary).Ingest(
            includeGamma ? Arguments("alpha", "gamma") : Arguments("alpha"));

        Assert.False(result.Success);
        Assert.Contains("source alpha atomization failed:", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

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
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var beforeLedger = DirectoryLedgerTestSupport.ReadRepository(temporary);

        var result = Environment(fixture, temporary).Ingest(Arguments("beta"));

        Assert.True(result.Success, result.Error);
        var after = DirectoryLedgerTestSupport.ReadRepository(temporary);
        AssertExistingLedgerFilesUnchanged(beforeLedger, after);
        var beforePaths = beforeLedger.Entries.Select(static item => item.Path).ToHashSet(StringComparer.Ordinal);
        var added = after.Entries.Where(item => !beforePaths.Contains(item.Path)).ToArray();
        Assert.NotEmpty(added);
        Assert.All(added, static item => Assert.True(
            DigestionCasStore.IsCanonicalPath(item.Path)
            || item.Path.Contains("/residual-open/", StringComparison.Ordinal),
            $"unexpected report-free path: {item.Path}"));
    }

    [Theory]
    [InlineData("cas-integrity")]
    [InlineData("cas-fingerprint")]
    [InlineData("write-set-bound")]
    public void Ingest_NewCasIntegrityAndWriteSetBoundFailBeforeAnyWrite(string fault)
    {
        var fixture = Fixture();
        fixture.Files[BetaPath] += Addition;
        var dependencies = new ReportFreeIngestDependencies(
            BeforeValidation: plan => fault switch
            {
                "cas-integrity" => CorruptFirstCas(plan),
                "cas-fingerprint" => CorruptNewFingerprint(plan),
                "write-set-bound" => MoveNewEntryOutsideSelectedSource(plan),
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

    private static ReportFreeDigestionIngestPlan MoveNewEntryOutsideSelectedSource(
        ReportFreeDigestionIngestPlan plan)
    {
        var sources = plan.Document.RequireDigestionSources();
        var beta = sources.Single(static source => source.SourceId == "beta");
        var added = Assert.Single(beta.Entries, entry => plan.AddedAtomIds.Contains(entry.AtomId));
        return plan with
        {
            Document = plan.Document.WithDigestionSources(sources.Select(source =>
                source.SourceId == "beta"
                    ? source with { Entries = source.Entries.Remove(added) }
                    : source with
                    {
                        Entries = source.Entries.Add(added with
                        {
                            SourceId = source.SourceId,
                            SourcePath = source.SourcePath,
                        }),
                    }).ToImmutableArray()),
        };
    }

    private static ReportFreeDigestionIngestPlan CorruptNewFingerprint(ReportFreeDigestionIngestPlan plan) =>
        plan with
        {
            Document = plan.Document.WithDigestionSources(plan.Document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(entry => plan.AddedAtomIds.Contains(entry.AtomId)
                        ? entry with
                        {
                            Fingerprints = entry.Fingerprints with { RawSha256 = "sha256:" + new string('a', 64) },
                        }
                        : entry).ToImmutableArray(),
                }).ToImmutableArray()),
        };
}
