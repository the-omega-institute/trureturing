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
        Directory.CreateDirectory(Path.Combine(temporary.Path, "agents"));
        File.WriteAllText(
            Path.Combine(temporary.Path, "agents", "echo-template.md"),
            "Remark-closure guard numerical certificate independently testable identity "
                + "upgrade-candidate retained_residual unresolved_subitems\n");
        File.WriteAllText(Path.Combine(output, "stale.md"), "remove");
        File.WriteAllText(Path.Combine(output, "keep.txt"), "keep");
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var verifier = new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.RingPath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            verifier);

        var emitted = environment.EchoVerify(["--emit", "--base", "baseline"]);

        Assert.Equal(0, emitted.ExitCode);
        Assert.NotEmpty(verifier.Scopes);
        Assert.All(verifier.Scopes, scope => Assert.Equal([RuleFixture.RingPath], scope.Paths.Select(path => path.Value).ToArray()));
        Assert.StartsWith(
            "<!-- echo-residual-summary:v3 residual=sha256:",
            emitted.Output,
            StringComparison.Ordinal);
        Assert.True(File.Exists(outside));
        Assert.True(File.Exists(Path.Combine(output, "keep.txt")));
        Assert.False(File.Exists(Path.Combine(output, "stale.md")));
        var expectedFileNames = BackfillInventoryLoader.Load(fixture.Build().Current)
            .RequireDigestionSources()
            .Select(static source => source.SourceId + ".md")
            .Order(StringComparer.Ordinal)
            .ToArray();
        var actualFileNames = Directory.GetFiles(output, "*.md", SearchOption.TopDirectoryOnly)
            .Select(Path.GetFileName)
            .Order(StringComparer.Ordinal)
            .ToArray();
        Assert.Equal(expectedFileNames, actualFileNames);
        Assert.Equal("keep", File.ReadAllText(outside));
    }
}
