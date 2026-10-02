using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class LeanCompiledArtifactReportsTests
{
    [Fact]
    public void MissingRawLeanReportFailsWithProducerInstruction()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-" + Guid.NewGuid().ToString("N"));
        TemporaryFileSystem.Directory.CreateDirectory(root);

        try
        {
            var exception = Assert.Throws<InvalidOperationException>(
                () => LeanCompiledArtifactReports.InspectRepository(root));

            Assert.Contains("raw Lean report", exception.Message, StringComparison.Ordinal);
            Assert.Contains("inspect.sh", exception.Message, StringComparison.Ordinal);
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void ConfiguredReportPathOverridesTheCanonicalArtifact()
    {
        var repositoryRoot = RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound).Root.FullPath;
        var configured = Path.Combine(
            Path.GetTempPath(),
            "stratalint-configured-report-" + Guid.NewGuid().ToString("N") + ".json");
        var exception = Assert.Throws<InvalidOperationException>(
            () => LeanCompiledArtifactReports.ReadRepository(repositoryRoot, configured));

        Assert.Contains(configured, exception.Message, StringComparison.Ordinal);
    }
}
