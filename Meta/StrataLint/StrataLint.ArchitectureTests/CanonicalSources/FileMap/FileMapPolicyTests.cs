using System.Text;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

public sealed class FileMapPolicyTests
{
    [Fact]
    public void RepositoryFilesConformToTheCanonicalFileMap()
    {
        var findings = FileMapPolicy.InspectRepository(RepositoryLayout.FindRoot());

        Assert.True(
            findings.Count == 0,
            string.Join(
                Environment.NewLine,
                findings.Select(static finding =>
                    $"{finding.Code} {finding.Path}: {finding.Message}")));
    }

    [Fact]
    public void UnclassifiedFileIsRejectedByTheRedFixture()
    {
        var manifest = Parse(Entry("D5/**/*.lean", "truth", "none", "lake", "lean-build"));

        var finding = Assert.Single(FileMapPolicy.InspectCoverage(
            manifest,
            ["D5/S0/Ring.lean", "README.md"]));

        Assert.Equal("FILEMAP-UNCLASSIFIED", finding.Code);
        Assert.Equal("README.md", finding.Path);
    }

    [Fact]
    public void OverlappingPatternsAreRejectedByTheRedFixture()
    {
        var manifest = Parse(
            Entry("D5/**/*.lean", "truth", "none", "lake", "lean-build"),
            Entry("D5/S0/**/*.lean", "truth", "none", "lake", "lean-build"));

        var finding = Assert.Single(FileMapPolicy.InspectCoverage(
            manifest,
            ["D5/S0/Ring.lean"]));

        Assert.Equal("FILEMAP-AMBIGUOUS", finding.Code);
        Assert.Contains("D5/**/*.lean", finding.Message, StringComparison.Ordinal);
        Assert.Contains("D5/S0/**/*.lean", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RegistryAndTrackedRootDriftIsRejectedByTheRedFixture()
    {
        var finding = Assert.Single(FileMapPolicy.InspectRegistryRootAlignment(
            ["README.md"],
            ["Makefile", "README.md"]));

        Assert.Equal("FILEMAP-REGISTRY-ALIGNMENT", finding.Code);
        Assert.Contains("Makefile", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DataWithoutAnExistingLoaderIsRejectedByTheRedFixture()
    {
        var manifest = Parse(Entry(
            "Data/**/*.toml",
            "data",
            "none",
            "MissingLoader",
            "MissingLoader"));

        var finding = Assert.Single(FileMapPolicy.InspectDataVerifiers(
            manifest,
            new HashSet<string>(StringComparer.Ordinal)));

        Assert.Equal("FILEMAP-DATA-VERIFIER", finding.Code);
    }

    [Fact]
    public void GeneratedFileWithoutProducerInventoryIsRejectedByTheRedFixture()
    {
        var manifest = Parse(Entry(
            "Generated/output.json",
            "generated",
            "JsonEmitter",
            "reader",
            "emit-check"));

        var finding = Assert.Single(FileMapPolicy.InspectGeneratedInventory(
            manifest,
            ["Generated/output.json"],
            []));

        Assert.Equal("FILEMAP-GENERATED-INVENTORY", finding.Code);
    }

    [Fact]
    public void GeneratedDeclarationWithoutProducerIsRejectedByTheRedFixture()
    {
        var source = Entry(
            "Generated/output.json",
            "generated",
            "none",
            "reader",
            "emit-check");

        var exception = Assert.Throws<FormatException>(() => Parse(source));

        Assert.Contains("produced_by must name a producer", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void GeneratedProducerMismatchIsRejectedByTheRedFixture()
    {
        var manifest = Parse(Entry(
            "Generated/output.json",
            "generated",
            "JsonEmitter",
            "reader",
            "emit-check"));
        var inventory = new GeneratedArtifactIdentity(
            "Generated/output.json",
            "OtherEmitter",
            "emit-check");

        var finding = Assert.Single(FileMapPolicy.InspectGeneratedInventory(
            manifest,
            ["Generated/output.json"],
            [inventory]));

        Assert.Equal("FILEMAP-GENERATED-PRODUCER", finding.Code);
    }

    [Theory]
    [InlineData("Generated/manual.md", "data", "FILEMAP-DIRECTORY-KIND")]
    [InlineData("Meta/StrataLint/cases.toml", "data", "FILEMAP-DATA-RESIDENCE")]
    public void ClassDirectoryMixingIsRejectedByTheRedFixture(
        string path,
        string kind,
        string expectedCode)
    {
        var manifest = Parse(Entry(path, kind, "none", "reader", "SnapshotDecoder"));

        var finding = Assert.Single(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));

        Assert.Equal(expectedCode, finding.Code);
    }

    [Fact]
    public void DataAndLeanGeneratedDependenciesAreRejectedByTheRedFixture()
    {
        var manifest = Parse(
            Entry("Data/**/*.toml", "data", "none", "loader", "SnapshotDecoder"),
            Entry("Generated/**/*.json", "generated", "JsonEmitter", "program", "emit-check"),
            Entry("Generated/**/*.lean", "generated", "LeanEmitter", "lake", "emit-check"),
            Entry("Main.lean", "truth", "none", "lake", "lean-build"));
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["Data/input.toml"] = "projection = \"Generated/output.json\"\n",
            ["Generated/output.json"] = "{}\n",
            ["Generated/Proof.lean"] = "def generated : Nat := 0\n",
            ["Main.lean"] = "import Generated.Proof\n",
        };

        var findings = FileMapPolicy.InspectDependencies(manifest, files);

        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-DATA-GENERATED-DEPENDENCY");
        Assert.Contains(findings, static finding => finding.Code == "FILEMAP-LEAN-GENERATED-IMPORT");
    }

    private static FileMapManifest Parse(params string[] entries) =>
        FileMapLoader.Parse(
            Encoding.UTF8.GetBytes("schema_version = 1\n\n" + string.Join("\n", entries)),
            "fixture.toml");

    private static string Entry(
        string pattern,
        string kind,
        string producedBy,
        string consumedBy,
        string verifiedBy) => $$"""
        [[files]]
        pattern = "{{pattern}}"
        kind = "{{kind}}"
        produced_by = "{{producedBy}}"
        consumed_by = ["{{consumedBy}}"]
        verified_by = ["{{verifiedBy}}"]
        """ + "\n";
}
