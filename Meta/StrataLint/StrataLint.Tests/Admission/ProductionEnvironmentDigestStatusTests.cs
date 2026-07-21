using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private const string EchoResidualStartMarker =
        "<!-- stratalint:echo-residual-summary:start -->";
    private const string EchoResidualEndMarker =
        "<!-- stratalint:echo-residual-summary:end -->";

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

    [Fact]
    public void ResidualSummaryBindsTheCandidateAndBaselineSnapshots()
    {
        var (environment, _) = CreateResidualEnvironment();

        var result = environment.DigestStatus(["--residual-summary", "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.StartsWith(EchoResidualStartMarker + "\n", result.Output, StringComparison.Ordinal);
        Assert.Matches(
            "(?m)^- candidate_snapshot_sha256: `sha256:[0-9a-f]{64}`$",
            result.Output);
        Assert.Matches(
            "(?m)^- baseline_snapshot_sha256: `sha256:[0-9a-f]{64}`$",
            result.Output);
        Assert.EndsWith(EchoResidualEndMarker + "\n", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void EchoReviewVerificationAcceptsExactlyOneCurrentResidualBlock()
    {
        var (environment, _) = CreateResidualEnvironment();
        var block = RenderResidualBlock(environment);
        using var temporary = new TemporaryDirectory();
        var review = Path.Combine(temporary.Path, ".echo-review.md");
        File.WriteAllText(
            review,
            "# Statement Echo\n\nMachine evidence follows.\n\n" + block,
            new UTF8Encoding(false));

        var result = environment.DigestStatus(
            ["--residual-summary", "--base", "baseline", "--verify-review", review]);

        Assert.True(result.Success, result.Error);
        Assert.StartsWith("ECHO_REVIEW_VALID ", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void EchoReviewVerificationRejectsAMissingResidualBlock()
    {
        var (environment, _) = CreateResidualEnvironment();
        using var temporary = new TemporaryDirectory();
        var review = Path.Combine(temporary.Path, ".echo-review.md");
        File.WriteAllText(review, "# Statement Echo\n", new UTF8Encoding(false));

        var result = environment.DigestStatus(
            ["--residual-summary", "--base", "baseline", "--verify-review", review]);

        Assert.False(result.Success);
        Assert.StartsWith("ECHO_REVIEW_INVALID ", result.Error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("edited")]
    [InlineData("reordered")]
    [InlineData("duplicated")]
    [InlineData("line-endings")]
    public void EchoReviewVerificationRejectsNonVerbatimResidualBlocks(string mutation)
    {
        var (environment, _) = CreateResidualEnvironment();
        var block = RenderResidualBlock(environment);
        var invalidBlock = mutation switch
        {
            "edited" => block.Replace("# Echo Residual Summary", "# Edited Residual Summary", StringComparison.Ordinal),
            "reordered" => block.Replace(
                "  - `alpha-residual`\n  - `zeta-residual`",
                "  - `zeta-residual`\n  - `alpha-residual`",
                StringComparison.Ordinal),
            "duplicated" => block + "\n" + block,
            "line-endings" => block.Replace("\n", "\r\n", StringComparison.Ordinal),
            _ => throw new ArgumentOutOfRangeException(nameof(mutation)),
        };
        using var temporary = new TemporaryDirectory();
        var review = Path.Combine(temporary.Path, ".echo-review.md");
        File.WriteAllText(review, invalidBlock, new UTF8Encoding(false));

        var result = environment.DigestStatus(
            ["--residual-summary", "--base", "baseline", "--verify-review", review]);

        Assert.False(result.Success);
        Assert.StartsWith("ECHO_REVIEW_INVALID ", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void EchoReviewVerificationRejectsAStaleCandidateSnapshot()
    {
        var (originalEnvironment, fixture) = CreateResidualEnvironment();
        var staleBlock = RenderResidualBlock(originalEnvironment);
        fixture.Files[RuleFixture.BlueprintPath] += "Stale candidate change.\n";
        var currentEnvironment = EnvironmentFor(fixture);
        using var temporary = new TemporaryDirectory();
        var review = Path.Combine(temporary.Path, ".echo-review.md");
        File.WriteAllText(review, staleBlock, new UTF8Encoding(false));

        var result = currentEnvironment.DigestStatus(
            ["--residual-summary", "--base", "baseline", "--verify-review", review]);

        Assert.False(result.Success);
        Assert.StartsWith("ECHO_REVIEW_INVALID ", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void EchoReviewVerificationRejectsAStaleBaselineSnapshot()
    {
        var (originalEnvironment, fixture) = CreateResidualEnvironment();
        var staleBlock = RenderResidualBlock(originalEnvironment);
        fixture.Baseline[RuleFixture.BlueprintPath] += "Stale baseline change.\n";
        var currentEnvironment = EnvironmentFor(fixture);
        using var temporary = new TemporaryDirectory();
        var review = Path.Combine(temporary.Path, ".echo-review.md");
        File.WriteAllText(review, staleBlock, new UTF8Encoding(false));

        var result = currentEnvironment.DigestStatus(
            ["--residual-summary", "--base", "baseline", "--verify-review", review]);

        Assert.False(result.Success);
        Assert.StartsWith("ECHO_REVIEW_INVALID ", result.Error, StringComparison.Ordinal);
    }

    private static (ProductionCliEnvironment Environment, RuleFixture Fixture)
        CreateResidualEnvironment()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[BackfillInventoryLoader.RelativePath] = fixture.Files[BackfillInventoryLoader.RelativePath]
            .Replace(
                "          unresolved_subitems: []",
                "          unresolved_subitems:\n            - zeta-residual\n            - alpha-residual",
                StringComparison.Ordinal);
        return (EnvironmentFor(fixture), fixture);
    }

    private static ProductionCliEnvironment EnvironmentFor(RuleFixture fixture) => new(
        "/repo",
        new FakeRepositoryGateway(
            RawChangeSet.Create(Array.Empty<string>()),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline)),
        new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
        new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

    private static string RenderResidualBlock(ProductionCliEnvironment environment)
    {
        var result = environment.DigestStatus(["--residual-summary", "--base", "baseline"]);
        Assert.True(result.Success, result.Error);
        return result.Output;
    }
}
