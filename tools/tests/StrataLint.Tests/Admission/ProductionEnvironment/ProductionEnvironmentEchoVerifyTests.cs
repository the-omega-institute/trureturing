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
        var historyAvailable = true;
        var history = new FakeAtomHistorySource(() => historyAvailable
            ? FakeAtomHistorySource.ForPaths(fixture.Files.Keys).Read()
            : throw new IOException("synthetic history unavailable"));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.RingPath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty),
            atomHistorySource: history);

        var emitted = environment.EchoVerify(["--emit", "--base", "baseline"]);

        Assert.Equal(0, emitted.ExitCode);
        Assert.Contains("## age", emitted.Output, StringComparison.Ordinal);
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
        foreach (var name in actualFileNames)
            Assert.DoesNotContain("## age", File.ReadAllText(Path.Combine(output, name!)), StringComparison.Ordinal);

        var before = Directory.GetFiles(output).ToDictionary(
            static path => path, File.ReadAllBytes, StringComparer.Ordinal);
        historyAvailable = false;

        var unavailable = environment.EchoVerify(["--emit", "--base", "baseline"]);

        Assert.Equal(2, history.Calls);
        Assert.Equal(2, unavailable.ExitCode);
        Assert.Empty(unavailable.Output);
        Assert.Equal("ECHO_VERIFY_INFRASTRUCTURE residual derivation failed\n"
            + "DIGEST_AGE_HISTORY_UNAVAILABLE synthetic history unavailable\n", unavailable.Error);
        Assert.Equal(before.Keys.Order(StringComparer.Ordinal),
            Directory.GetFiles(output).Order(StringComparer.Ordinal));
        foreach (var (path, bytes) in before)
            Assert.Equal(bytes, File.ReadAllBytes(path));
        Assert.Equal("keep", File.ReadAllText(outside));
    }
}
