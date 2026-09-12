using StrataLint.Cli;

namespace StrataLint.ArchitectureTests;

public sealed class FileMapReferenceTests
{
    [Fact]
    public void CommittedFileMapPatternsHaveTrackedPresentFiles()
    {
        var findings = FileMapPolicy.InspectRepository(RepositoryLayout.FindRoot())
            .Where(static finding => finding.Code == "FILEMAP-PATTERN-EMPTY");

        Assert.Empty(findings);
    }
}
