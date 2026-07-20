using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void DigestStatusReportsCasSeenAcrossNormalizedSourceRewrite()
    {
        var fixture = new RuleFixture();
        var atomizerId = AtomizerRegistry.RegisteredIds[0];
        var ledgerBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\r\n\r\n**定理 1.1(Test)**。claim。\r\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, ledgerBytes).Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Files.Remove(GoldenCorpus.FixtureCasPath);
        fixture.Files[captured.RelativePath] = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
        fixture.Files["Meta/BACKFILL.yaml"] = $$"""
            schema_version: 3
            ledger: theory-digestion-v1
            sources:
              - source_id: fixture-source
                path: {{GoldenCorpus.FixtureDigestionSourcePath}}
                atomizer: {{atomizerId}}
                acknowledged_stale: []
                entries:
                  - atom_id: normalized-receipt
                    ast_path: {{atom.AstPath}}
                    fingerprints:
                      raw_sha256: {{atom.Fingerprints.RawSha256}}
                      normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
                    cas_ref: {{captured.Reference}}
                    coverage_gids: []
                    receipts:
                      coverage: []
                      scribe: []
                      unresolved_subitems: []
                      chain_atoms: []
                      tail_authorization: null
                    status:
                      migration: residual
                      truth: open
            ticket_index: []
            """;
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(["--json"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"alignment\": \"seen\"", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("normalized-seen-not-deletable", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"deletable\": false", result.Output, StringComparison.Ordinal);
    }
}
