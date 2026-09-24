namespace StrataLint.RepositoryFileMap.Tests;

[Collection(nameof(CanonicalFileMapCollection))]
public sealed class RegistryReferenceTests(CanonicalFileMapFixture fixture)
{
    [Fact]
    public void CanonicalRegistryReferencesOnlyTrackedPresentFiles()
    {
        var findings = fixture.Findings
            .Where(static finding => finding.Code == "FILEMAP-REGISTRY-DANGLING");

        Assert.Empty(findings);
    }
}
