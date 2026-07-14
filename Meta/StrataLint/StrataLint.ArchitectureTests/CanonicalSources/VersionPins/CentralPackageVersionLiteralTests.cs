namespace StrataLint.ArchitectureTests;

public sealed class CentralPackageVersionLiteralTests
{
    [Fact]
    public void RepositoryCSharpDoesNotCopyCentralPackageVersions()
    {
        var findings = CentralPackageVersionLiteralPolicy.InspectRepository(
            RepositoryLayout.FindRoot());

        Assert.True(
            findings.Count == 0,
            string.Join(
                Environment.NewLine,
                findings.Select(static finding =>
                    $"{finding.Path}: copied central version {finding.Value}")));
    }

    [Fact]
    public void CentralPackageVersionLiteralIsRejectedByTheRedFixture()
    {
        var version = string.Concat("9.", "8.7");
        var source = "const string copied = \"9.8.7\";";

        var finding = Assert.Single(CentralPackageVersionLiteralPolicy.InspectSource(
            "Meta/StrataLint/Synthetic.cs",
            source,
            new HashSet<string>(StringComparer.Ordinal) { version }));

        Assert.Contains("Directory.Packages.props", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void EmptyCentralVersionCatalogIsRejectedByTheRedFixture()
    {
        Assert.Throws<FormatException>(() =>
            CentralPackageVersionLiteralPolicy.LoadVersions("<Project />"));
    }

    [Fact]
    public void UnrelatedVersionFixtureIsNotRejected()
    {
        var source = "const string fixture = \"9.8.7\";";

        Assert.Empty(CentralPackageVersionLiteralPolicy.InspectSource(
            "Meta/StrataLint/Synthetic.cs",
            source,
            new HashSet<string>(StringComparer.Ordinal) { "1.2.3" }));
    }
}
