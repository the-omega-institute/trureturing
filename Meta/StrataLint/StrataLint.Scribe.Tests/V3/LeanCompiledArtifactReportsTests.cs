using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

[Collection("Lean report environment")]
public sealed class LeanCompiledArtifactReportsTests
{
    [Fact]
    public void MissingRawLeanReportFailsWithProducerInstruction()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(root);

        try
        {
            var exception = Assert.Throws<InvalidOperationException>(
                () => LeanCompiledArtifactReports.InspectRepository(root));

            Assert.Contains("raw Lean report", exception.Message, StringComparison.Ordinal);
            Assert.Contains("inspect.sh", exception.Message, StringComparison.Ordinal);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void ConfiguredReportPathOverridesTheCanonicalArtifact()
    {
        var repositoryRoot = FindRepositoryRoot();
        var configured = Path.Combine(
            Path.GetTempPath(),
            "stratalint-configured-report-" + Guid.NewGuid().ToString("N") + ".json");
        var previous = Environment.GetEnvironmentVariable("STRATALINT_LEAN_REPORT");
        Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", configured);

        try
        {
            var exception = Assert.Throws<InvalidOperationException>(
                () => LeanCompiledArtifactReports.InspectRepository(repositoryRoot));

            Assert.Contains(configured, exception.Message, StringComparison.Ordinal);
        }
        finally
        {
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_REPORT", previous);
        }
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}

[CollectionDefinition("Lean report environment", DisableParallelization = true)]
public sealed class LeanReportEnvironmentCollection;
