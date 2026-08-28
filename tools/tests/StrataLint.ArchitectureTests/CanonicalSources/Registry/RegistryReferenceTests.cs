using StrataLint.Cli;

namespace StrataLint.ArchitectureTests;

public sealed class RegistryReferenceTests
{
    [Fact]
    public void CanonicalRegistryReferencesOnlyTrackedPresentFiles()
    {
        var findings = FileMapPolicy.InspectRepository(RepositoryLayout.FindRoot())
            .Where(static finding => finding.Code == "FILEMAP-REGISTRY-DANGLING");

        Assert.Empty(findings);
    }
}
