using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class QuarantineSummaryCommandTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ResidualSummaryAndSourceShardKeepQuarantineDetailsInFrontier(bool hasSubitems)
    {
        var capture = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("synthetic quarantined claim\n"));
        var atomId = capture.Reference["sha256:".Length..];
        var fingerprints = DigestionFingerprint.Compute(capture.Bytes.AsSpan());
        var subitems = hasSubitems ? "\n    - remaining-proof" : "[]";
        var raw = RawRepositorySnapshot.Create(
        [
            RawRepositoryEntry.FromText(TheoryAtomizerDataLoader.DataPath, TheoryAtomizerDataTests.Minimal),
            RawRepositoryEntry.FromText("Meta/Digestion/backfill/source-a/source.toml", """
                source_id = "source-a"
                path = "synthetic/source-a.md"
                atomizer = "none"
                genre_registry_check = "no-registry"
                unregistered_genres = []
                """ + "\n"),
            RawRepositoryEntry.FromText($"Meta/Digestion/backfill/source-a/residual-open/{atomId}.yaml", $$"""
                fingerprints:
                  raw_sha256: {{fingerprints.RawSha256}}
                  normalized_sha256: {{fingerprints.NormalizedSha256}}
                cas_ref: {{capture.Reference}}
                coverage_gids: []
                receipts:
                  scribe: []
                  unresolved_subitems: {{subitems}}
                  chain_atoms: []
                  tail_authorization: null
                  quarantine:
                    blocker_class: missing-prerequisite
                    justification: missing witness
                    reentry_condition: supply witness
                """),
            new RawRepositoryEntry(capture.RelativePath, capture.Bytes),
        ]);
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, raw);
        var report = new FakeLeanReportSource(LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)));
        var scribe = new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty);

        var result = DigestStatusCommand.Run(gateway, report, scribe, ["--residual-summary"]);
        Assert.True(result.Success, result.Error);
        var shards = DigestStatusCommand.RenderShards(gateway, report, scribe, "baseline");

        var sourceShard = shards["Generated/echo-residuals/source-a.md"];
        foreach (var output in new[] { result.Output, sourceShard })
        {
            Assert.Contains("- unresolved_subitems: 0", output, StringComparison.Ordinal);
            Assert.Contains("- mother_residual_atom_ids: 0", output, StringComparison.Ordinal);
            var frontier = output[output.IndexOf("## frontier", StringComparison.Ordinal)..];
            var nextSection = frontier.IndexOf("\n## ", StringComparison.Ordinal);
            if (nextSection >= 0)
            {
                frontier = frontier[..nextSection];
            }
            Assert.Contains(atomId, frontier, StringComparison.Ordinal);
            Assert.Contains("  - blocker_class: `missing-prerequisite`", frontier, StringComparison.Ordinal);
            Assert.Contains("  - justification: `missing witness`", frontier, StringComparison.Ordinal);
            Assert.Contains("  - reentry_condition: `supply witness`", frontier, StringComparison.Ordinal);
            Assert.Equal(hasSubitems, frontier.Contains("`remaining-proof`", StringComparison.Ordinal));
        }
    }
}
