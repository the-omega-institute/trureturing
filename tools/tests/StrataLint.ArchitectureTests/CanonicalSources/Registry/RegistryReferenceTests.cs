namespace StrataLint.ArchitectureTests;

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
