using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void IngestWarnsWithoutBlockingWhenSharedResidueIsClearedOnOnlyOneSource()
    {
        var result = RunSharedResidueIngest(clearFirst: true, clearSecond: false);

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            "GAP atom=atom-a code=cross-volume-shared-residue-half-cleared severity=warn "
                + "detail={\"residue\":\"shared-residue\",\"cleared_source\":\"source-a\","
                + "\"hanging_hosts\":[\"source-b/atom-b\"]}",
            result.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestDoesNotWarnWhenSharedResidueIsClearedOnEverySource()
    {
        var result = RunSharedResidueIngest(clearFirst: true, clearSecond: true);

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain(
            "cross-volume-shared-residue-half-cleared",
            result.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestDoesNotWarnWhenAnotherAtomOnTheSameSourceRetainsTheSharedResidue()
    {
        var result = RunSharedResidueIngest(
            clearFirst: true,
            clearSecond: false,
            includeSecondFirstSourceAtom: true,
            clearSecondFirstSourceAtom: false);

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain(
            "cross-volume-shared-residue-half-cleared",
            result.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestWarnsOnceWhenEveryAtomOnOneSourceClearsTheSharedResidue()
    {
        var result = RunSharedResidueIngest(
            clearFirst: true,
            clearSecond: false,
            includeSecondFirstSourceAtom: true,
            clearSecondFirstSourceAtom: true);

        Assert.True(result.Success, result.Error);
        Assert.Single(
            result.Output.Split('\n'),
            static line => line.Contains(
                "code=cross-volume-shared-residue-half-cleared",
                StringComparison.Ordinal));
    }

    private static string SharedResidueLedger(
        string atomizerId,
        DigestionAtom atom,
        bool clearFirst,
        bool clearSecond,
        bool includeSecondFirstSourceAtom,
        bool clearSecondFirstSourceAtom) => $$"""
        schema_version: 3
        ledger: theory-digestion-v1
        sources:
          - source_id: source-a
            path: {{GoldenCorpus.FixtureDigestionSourcePath}}
            atomizer: {{atomizerId}}
            acknowledged_stale: []
            entries:
              - atom_id: atom-a
                ast_path: {{atom.AstPath}}
                fingerprints:
                  raw_sha256: {{atom.Fingerprints.RawSha256}}
                  normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
                cas_ref: {{atom.Fingerprints.RawSha256}}
                coverage_gids: []
                receipts:
                  coverage: []
                  scribe: []
                  unresolved_subitems: {{(clearFirst ? "[]" : "\n            - shared-residue")}}
                  chain_atoms: []
                  tail_authorization: null
                status:
                  migration: residual
                  truth: open
        {{(includeSecondFirstSourceAtom ? $$"""
              - atom_id: atom-a-duplicate
                ast_path: {{atom.AstPath}}
                fingerprints:
                  raw_sha256: {{atom.Fingerprints.RawSha256}}
                  normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
                cas_ref: {{atom.Fingerprints.RawSha256}}
                coverage_gids: []
                receipts:
                  coverage: []
                  scribe: []
                  unresolved_subitems: {{(clearSecondFirstSourceAtom ? "[]" : "\n            - shared-residue")}}
                  chain_atoms: []
                  tail_authorization: null
                status:
                  migration: residual
                  truth: open
        """ : string.Empty)}}
          - source_id: source-b
            path: docs/CONTRIBUTING.md
            atomizer: {{atomizerId}}
            acknowledged_stale: []
            entries:
              - atom_id: atom-b
                ast_path: {{atom.AstPath}}
                fingerprints:
                  raw_sha256: {{atom.Fingerprints.RawSha256}}
                  normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
                cas_ref: {{atom.Fingerprints.RawSha256}}
                coverage_gids: []
                receipts:
                  coverage: []
                  scribe: []
                  unresolved_subitems: {{(clearSecond ? "[]" : "\n            - shared-residue")}}
                  chain_atoms: []
                  tail_authorization: null
                status:
                  migration: residual
                  truth: open
        ticket_index: []
        """;

    private static CommandResult RunSharedResidueIngest(
        bool clearFirst,
        bool clearSecond,
        bool includeSecondFirstSourceAtom = false,
        bool clearSecondFirstSourceAtom = false)
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceText = "# Synthetic\n\n**定理 1.1(A)**。claim。\n";
        var sourceBytes = Encoding.UTF8.GetBytes(sourceText);
        var atom = Assert.Single(AtomizerRegistry.Atomize(
            atomizerId,
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var baselineLedger = SharedResidueLedger(
            atomizerId,
            atom,
            clearFirst: false,
            clearSecond: false,
            includeSecondFirstSourceAtom,
            clearSecondFirstSourceAtom: false);
        var currentLedger = SharedResidueLedger(
            atomizerId,
            atom,
            clearFirst,
            clearSecond,
            includeSecondFirstSourceAtom,
            clearSecondFirstSourceAtom);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = sourceText;
        fixture.Files["docs/CONTRIBUTING.md"] = sourceText;
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = sourceText;
        fixture.Baseline["docs/CONTRIBUTING.md"] = sourceText;
        fixture.Files[BackfillInventoryLoader.RelativePath] = currentLedger;
        fixture.Baseline[BackfillInventoryLoader.RelativePath] = baselineLedger;
        fixture.Files.Remove(GoldenCorpus.FixtureCasPath);
        fixture.Baseline.Remove(GoldenCorpus.FixtureCasPath);
        fixture.Files[captured.RelativePath] = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
        fixture.Baseline[captured.RelativePath] = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, currentLedger, new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        return environment.Ingest(["--base", "baseline"]);
    }
}
