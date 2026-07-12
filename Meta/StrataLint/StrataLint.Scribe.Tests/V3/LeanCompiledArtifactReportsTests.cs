using StrataLint.Cli;

namespace StrataLint.Scribe.Tests;

public sealed class LeanCompiledArtifactReportsTests
{
    [Fact]
    public void MissingLakeArtifactsFailWithBuildInstruction()
    {
        var root = Path.Combine(
            Path.GetTempPath(),
            "stratalint-scribe-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(root);

        try
        {
            var exception = Assert.Throws<InvalidOperationException>(
                () => LeanCompiledArtifactReports.InspectRepository(root));

            Assert.Contains(".lake", exception.Message, StringComparison.Ordinal);
            Assert.Contains("lake build", exception.Message, StringComparison.Ordinal);
        }
        finally
        {
            Directory.Delete(root, recursive: true);
        }
    }
}
