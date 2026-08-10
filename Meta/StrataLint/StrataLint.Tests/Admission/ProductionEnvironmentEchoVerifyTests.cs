using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void EchoVerifyWritesOnlyCanonicalShardDirectoryAndConvergesMarkdownFiles()
    {
        using var temporary = new TemporaryDirectory();
        var outside = Path.Combine(temporary.Path, "outside.md");
        File.WriteAllText(outside, "keep");
        var output = Path.Combine(temporary.Path, "Generated", "echo-residuals");
        Directory.CreateDirectory(output);
        File.WriteAllText(Path.Combine(output, "stale.md"), "remove");
        File.WriteAllText(Path.Combine(output, "keep.txt"), "keep");
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.RingPath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var emitted = environment.EchoVerify(["--emit", "--base", "baseline"]);

        Assert.Equal(0, emitted.ExitCode);
        Assert.StartsWith(
            "<!-- echo-residual-summary:v3 residual=sha256:",
            emitted.Output,
            StringComparison.Ordinal);
        Assert.True(File.Exists(outside));
        Assert.True(File.Exists(Path.Combine(output, "keep.txt")));
        Assert.False(File.Exists(Path.Combine(output, "stale.md")));
        var expectedFileNames = BackfillInventoryLoader.Load(fixture.Files["Meta/BACKFILL.yaml"])
            .RequireDigestionSources()
            .Select(static source => source.SourceId + ".md")
            .Order(StringComparer.Ordinal)
            .ToArray();
        var actualFileNames = Directory.GetFiles(output, "*.md", SearchOption.TopDirectoryOnly)
            .Select(Path.GetFileName)
            .Order(StringComparer.Ordinal)
            .ToArray();
        Assert.Equal(expectedFileNames, actualFileNames);
    }
}
