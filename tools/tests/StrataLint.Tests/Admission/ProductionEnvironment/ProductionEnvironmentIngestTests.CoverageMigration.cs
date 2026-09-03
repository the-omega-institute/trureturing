using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CoverageSchemaMigrationWritesCanonicalAtomsAndSecondRunHasNoByteDiff()
    {
        const string coverageGid = "D5/S0/Carrier/Ring";
        var fixture = new RuleFixture();
        var sourceBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。claim。\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(
            SyntheticNumberedAtomizer.Id,
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            FrozenStatementReceiptTestData.AddLedger(
                files,
                new FrozenStatementReceiptTestData.Module(
                    coverageGid + ".lean",
                    FrozenStatementReceiptTestData.Id('d'),
                    []));
        }

        InstallDirectoryLedger(fixture, SyntheticNumberedAtomizer.Id, atom);
        var atomPath = DirectoryAtomPath(AtomId(atom), "residual-open");
        var sourceKey = "source_" + "sha256";
        var legacyAtom = DirectoryAtom(atom)
            .Replace(
                "coverage_gids: []",
                $"coverage_gids:\n  - {coverageGid}",
                StringComparison.Ordinal)
            .Replace(
                "receipts:\n  scribe: []",
                "receipts:\n"
                    + "  coverage:\n"
                    + $"    - gid: {coverageGid}\n"
                    + $"      {sourceKey}: {atom.Fingerprints.RawSha256}\n"
                    + $"      target_statement_id: sha256:{new string('0', 64)}\n"
                    + "  scribe: []",
                StringComparison.Ordinal);
        fixture.Files[atomPath] = legacyAtom;
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var firstEnvironment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var first = firstEnvironment.MigrateDigestionCoverage([]);

        Assert.True(first.Success, first.Error);
        Assert.Contains("relationships_before=1", first.Output, StringComparison.Ordinal);
        Assert.Contains("relationships_after=1", first.Output, StringComparison.Ordinal);
        Assert.Contains("second_pass_changed_files=0", first.Output, StringComparison.Ordinal);
        var migratedBytes = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var migratedFiles = new Dictionary<string, string>(fixture.Files, StringComparer.Ordinal)
        {
            [atomPath] = File.ReadAllText(Path.Combine(
                temporary.Path,
                atomPath.Replace('/', Path.DirectorySeparatorChar))),
        };
        var secondEnvironment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(migratedFiles),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var second = secondEnvironment.MigrateDigestionCoverage([]);

        Assert.True(second.Success, second.Error);
        Assert.Contains("changed_files=0", second.Output, StringComparison.Ordinal);
        Assert.Equal(migratedBytes, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }
}
