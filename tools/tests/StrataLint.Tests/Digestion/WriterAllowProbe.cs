using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestScopeTests
{
    [Fact]
    public void InstalledIngestWritesOnlySelectedSourceWithUnrelatedMalformedRecords()
    {
        var fixture = Fixture();
        const string badMetadata = "Meta/Digestion/backfill/alpha/source.toml";
        fixture.Files[badMetadata] = "malformed [";
        fixture.Files[BetaPath] += Addition;
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([BetaPath]), Raw(fixture.Files), Raw(fixture.Baseline));
        var report = new FakeLeanReportSource(null);
        var environment = new ProductionCliEnvironment(temporary.Path, gateway, report, new FakeScribeEmissionVerifier(null));
        var result = environment.Ingest(Arguments("beta"));
        Assert.True(result.Success, result.Error);
        Assert.Equal("malformed [", File.ReadAllText(Path.Combine(temporary.Path, badMetadata)));
        var id = Atom(Addition).Fingerprints.RawSha256[7..];
        Assert.True(File.Exists(Path.Combine(temporary.Path, DigestionCasStore.RootPath + id)));
        Assert.True(File.Exists(Path.Combine(temporary.Path, SourcePrefix("beta") + "residual-open/" + id + ".yaml")));
        Assert.Equal(0, gateway.WholeTreeReadCount);
        Assert.Equal(0, report.CallCount);
        Assert.DoesNotContain(gateway.ScopedCurrentReads.SelectMany(static scope => scope), path => path.Contains("backfill/alpha", StringComparison.Ordinal));
    }
}

public sealed class WriterAllowProbe
{
    [Fact]
    public void InstalledNestedDecompositionPreservesUnrelatedMalformedRecords()
    {
        const string nested = "**Theorem 1.1** First assertion.\n\n**Bundle**\n\nPreamble.\n\n- alpha\n- beta\n";
        var fixture = new DecomposeFixture(nested);
        var first = DecomposeAtomCommand.Run("synthetic", fixture.Gateway, fixture.Args(), fixture.Apply);
        Assert.True(first.Success, first.Error);
        var child = Assert.Single(fixture.Document.RequireDigestionEntries(), entry => entry.AtomId != fixture.Parent.AtomId
            && fixture.Snapshot.TryGetFile(DigestionCasStore.RootPath + entry.AtomId, out var blob)
            && DigestionDecompositionPolicy.IsMultiClause(DigestionAtom.FromFrozenCas(blob.RawBytes)));
        const string badMetadata = "Meta/Digestion/backfill/unrelated/source.toml";
        var badAtom = "Meta/Digestion/backfill/probe/residual-open/" + new string('e', 64) + ".yaml";
        fixture.Current = RawRepositorySnapshot.Create(fixture.Current.Entries.Concat([
            RawRepositoryEntry.FromText(badMetadata, "malformed ["), RawRepositoryEntry.FromText(badAtom, "malformed [") ]));
        var result = DecomposeAtomCommand.Run("synthetic", fixture.Gateway, fixture.Args(child.AtomId), fixture.Apply);
        Assert.True(result.Success, result.Error);
        Assert.Equal(2, fixture.Writes);
        Assert.Contains(fixture.Current.Entries, entry => entry.Path == badMetadata && Encoding.UTF8.GetString(entry.Bytes.AsSpan()) == "malformed [");
        Assert.Contains(fixture.Current.Entries, entry => entry.Path == badAtom && Encoding.UTF8.GetString(entry.Bytes.AsSpan()) == "malformed [");
        Assert.Equal(0, fixture.Gateway.WholeTreeReadCount);
        Assert.DoesNotContain(fixture.Gateway.ScopedCurrentReads.SelectMany(static scope => scope), path => path.Contains("unrelated", StringComparison.Ordinal) || path.Contains(new string('e', 64), StringComparison.Ordinal));
    }

    [Fact]
    public void InstalledReconciliationPreservesDescendantsAndNeedsNoLeanOrScribe()
    {
        var retained = new ReconcileChainTests();
        retained.LegalExplicitRegroupWritesOnlyParentAndPreservesEveryDescendant();
        retained.RegisteredProductionDispatchNeedsNeitherLeanNorScribe();
        new DecomposeAtomTests().SharedIdentityReusesExistingEntryAndCas();
    }

    [Fact]
    public void InstalledSettlementWritesSelectedAtomWithUnrelatedMalformedRecords()
    {
        var fixture = AtomContextFixture.Create();
        var id = AtomContextFixture.Id(fixture.Atomized.Claims[1]);
        const string badMetadata = "Meta/Digestion/backfill/unrelated/source.toml";
        var raw = RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Append(RawRepositoryEntry.FromText(badMetadata, "malformed [")));
        using var temporary = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, raw);
        var result = SettleAtomCommandTests.Run(temporary.Path, raw, SettleAtomCommandTests.Request(fixture, id));
        Assert.True(result.Success, result.Error);
        Assert.Equal("malformed [", File.ReadAllText(Path.Combine(temporary.Path, badMetadata)));
    }
}

public sealed partial class CoverAtomTests
{
    [Fact]
    public void InstalledCoverageValidatesFrozenTruthAndIgnoresUnrelatedMalformedRecords()
    {
        var inputs = new CoverSpec().Materialize();
        var files = DirectoryLedgerTestSupport.Project(inputs.Files);
        const string badMetadata = "Meta/Digestion/backfill/unrelated/source.toml";
        files[badMetadata] = "malformed [";
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, files);
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), CoverWorld.Raw(files), CoverWorld.Raw(files));
        var result = CoverAtomCommand.Run(temporary.Path, gateway, new FakeLeanReportSource(inputs.Report), CoverWorld.FixtureUtc,
            ["--cover-atom", CoverWorld.DefaultAtomId, "--gid", inputs.Gid]);
        Assert.True(result.Success, result.Error);
        Assert.Equal("malformed [", File.ReadAllText(Path.Combine(temporary.Path, badMetadata)));
        Assert.Equal(0, gateway.WholeTreeReadCount);
        Assert.Empty(gateway.ReadRevisionCalls);
        Assert.Empty(gateway.ReadChangesCalls);
    }
}
