using StrataLint.Cli;

namespace StrataLint.Tests;

[Collection("Lean report environment")]
public sealed class PrecomputedLeanReportSourceTests
{
    [Fact]
    public void ConfiguredReportPathOverridesTheCanonicalArtifact()
    {
        using var repository = new TemporaryDirectory();
        var configured = Path.Combine(repository.Path, "private-report.json");
        var previous = Environment.GetEnvironmentVariable("STRATALINT_LEAN_REPORT");
        Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", configured);

        try
        {
            var source = new PrecomputedLeanReportSource(repository.Path);
            var exception = Assert.ThrowsAny<IOException>(() => source.Load(null!));

            Assert.Contains(configured, exception.Message, StringComparison.Ordinal);
        }
        finally
        {
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", previous);
        }
    }
}

[CollectionDefinition("Lean report environment", DisableParallelization = true)]
public sealed class LeanReportEnvironmentCollection;
