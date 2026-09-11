using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

public sealed partial class FileMapPolicyTests
{
    [Fact]
    public void RegisteredTestPolicyFixtureIsJudgeData()
    {
        const string path = "tools/tests/StrataLint.Tests/Fixtures/fixture-registry.yaml";
        var root = RepositoryLayout.FindRoot();
        Assert.True(File.Exists(Path.Combine(root, path)));
        var manifest = FileMapLoader.LoadRepository(root);

        var entry = Assert.Single(manifest.Match(path));

        Assert.Equal(path, entry.Pattern);
        Assert.Equal(FileMapKind.Data, entry.Kind);
        Assert.Equal(["TestRegistry"], entry.ConsumedBy.ToArray());
        Assert.Equal(["TestRegistry"], entry.VerifiedBy.ToArray());
        Assert.Equal(FileMapAdmissionPlane.Judge, entry.AdmissionPlane);
        Assert.Empty(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));
    }

    [Fact]
    public void RegisteredTestPolicyFixtureAndJudgePathAreJudgeOnly()
    {
        var root = RepositoryLayout.FindRoot();
        string[] paths =
        [
            "tools/tests/StrataLint.Tests/Fixtures/fixture-registry.yaml",
            "tools/StrataLint.Engine/RepositoryIo/AdmissionPlanePolicy.cs",
        ];
        Assert.All(paths, path => Assert.True(File.Exists(Path.Combine(root, path))));

        var decision = AdmissionPlanePolicy.Evaluate(
            File.ReadAllBytes(Path.Combine(root, FileMapLoader.RelativePath)),
            paths);

        Assert.Equal(AdmissionPlaneClassification.JudgeOnly, decision.Classification);
        Assert.True(decision.IsAdmissible);
        Assert.Empty(decision.Code);
    }

    [Fact]
    public void RegisteredLeanContentAndJudgePathRemainMixedAndRejected()
    {
        var root = RepositoryLayout.FindRoot();
        string[] paths =
        [
            "D5/S0/Carrier/Ring.lean",
            "tools/StrataLint.Engine/RepositoryIo/AdmissionPlanePolicy.cs",
        ];
        Assert.All(paths, path => Assert.True(File.Exists(Path.Combine(root, path))));

        var decision = AdmissionPlanePolicy.Evaluate(
            File.ReadAllBytes(Path.Combine(root, FileMapLoader.RelativePath)),
            paths);

        Assert.Equal(AdmissionPlaneClassification.Mixed, decision.Classification);
        Assert.False(decision.IsAdmissible);
        Assert.Equal("ADMISSION-PLANE-MIXED", decision.Code);
    }

    [Fact]
    public void AdmissionPlaneIsAcceptedByTheStrictLoader()
    {
        var exception = Record.Exception(() => Parse(AdmissionEntry(
            "tools/example.cs",
            "program",
            "judge")));

        Assert.Null(exception);
    }

    [Fact]
    public void AdmissionPlaneIsRequiredByTheStrictLoader()
    {
        var entryWithoutAdmissionPlane = Entry(
            "tools/example.cs",
            "program",
            "none",
            "dotnet",
            "dotnet-test").Replace(
                "admission_plane = \"judge\"\n",
                string.Empty,
                StringComparison.Ordinal);

        var exception = Assert.ThrowsAny<FormatException>(() => Parse(entryWithoutAdmissionPlane));

        Assert.Contains(
            "FILEMAP-ADMISSION-PLANE-MISSING",
            exception.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void UnknownAdmissionPlaneIsRejectedByTheStrictLoader()
    {
        var exception = Assert.ThrowsAny<FormatException>(() => Parse(AdmissionEntry(
            "tools/example.cs",
            "program",
            "unknown")));

        Assert.Contains(
            "FILEMAP-ADMISSION-PLANE-INVALID",
            exception.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void NonStringAdmissionPlaneIsRejectedByTheStrictLoader()
    {
        var source = AdmissionEntry("tools/example.cs", "program", "judge").Replace(
            "admission_plane = \"judge\"",
            "admission_plane = 1",
            StringComparison.Ordinal);

        var exception = Assert.ThrowsAny<FormatException>(() => Parse(source));

        Assert.Contains(
            "FILEMAP-ADMISSION-PLANE-INVALID",
            exception.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void FileMapPolicySourceMustBeInTheJudgeAdmissionPlane()
    {
        const string path = "Meta/FILEMAP.toml";
        var manifest = Parse(AdmissionEntry(path, "data", "content"));

        var finding = Assert.Single(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));

        Assert.Equal("FILEMAP-ADMISSION-PLANE-INVALID", finding.Code);
        Assert.Equal(path, finding.Path);
    }

    [Fact]
    public void ContentAdmissionPlaneIsAcceptedForContentData()
    {
        const string path = "README.md";
        var manifest = Parse(AdmissionEntry(path, "data", "content"));

        Assert.Empty(FileMapPolicy.InspectDirectoryKinds(manifest, [path]));
    }

    private static string AdmissionEntry(
        string pattern,
        string kind,
        string admissionPlane) => $$"""
        [[files]]
        pattern = "{{pattern}}"
        kind = "{{kind}}"
        admission_plane = "{{admissionPlane}}"
        produced_by = "none"
        consumed_by = ["{{(kind == "program" ? "dotnet" : "reader")}}"]
        verified_by = ["{{(kind == "program" ? "dotnet-test" : "SnapshotDecoder")}}"]
        runtime_disposition = "committed-source"
        artifact_id = "none"
        """ + "\n";
}
