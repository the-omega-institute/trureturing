using StrataLint.Engine;

namespace StrataLint.FileMap.Tests;

public sealed class FileMapProgramTests
{
    [Theory]
    [InlineData("unexpected")]
    [InlineData("--scope")]
    [InlineData("--producer-write-set")]
    public void StandaloneEntryPreservesUsageAndStreams(string argument)
    {
        using var output = new StringWriter();
        using var error = new StringWriter();
        var exit = FileMapProgram.Run([argument], "unused", output, error);
        Assert.Equal(2, exit);
        Assert.Empty(output.ToString());
        Assert.Equal(FileMapConformCommand.Usage + "\n", error.ToString());
    }

    [Fact]
    public void StandaloneEntryPreservesInfrastructureFailure()
    {
        using var fixture = new TemporaryDirectory();
        using var output = new StringWriter();
        using var error = new StringWriter();
        var expected = FileMapConformCommand.Run([], fixture.Path);
        var exit = FileMapProgram.Run([], fixture.Path, output, error);
        Assert.Equal(2, exit);
        Assert.Equal(expected.Output, output.ToString());
        Assert.Equal(expected.Error, error.ToString());
    }

    [Fact]
    public void RequiredDocumentInputRemainsInInventoryAndDuplicatesAreRejected()
    {
        var inventory = GeneratedArtifactInventory.Create(["Blueprint/Z.md", "Blueprint/A.md"]);
        Assert.Equal(8, inventory.Length);
        Assert.Equal(inventory.Select(item => item.Path).Order(StringComparer.Ordinal),
            inventory.Select(item => item.Path));
        Assert.Equal("ScribeEmitter", inventory.Single(item => item.Path == "Blueprint/A.md").Producer);
        Assert.Equal("none", inventory.Single(item => item.Path == "Blueprint/A.md").ArtifactId);
        Assert.Throws<InvalidOperationException>(() =>
            GeneratedArtifactInventory.Create(["Blueprint/A.md", "Blueprint/A.md"]));
        Assert.Throws<InvalidOperationException>(() =>
            GeneratedArtifactInventory.Create(["Generated/DAG.md"]));
    }

    [Fact]
    public void StandaloneScopeReportsSelectedUnregisteredPathWithoutWholeTreeInventoryFindings()
    {
        using var fixture = new TemporaryDirectory();
        Directory.CreateDirectory(Path.Combine(fixture.Path, "Meta"));
        File.WriteAllText(Path.Combine(fixture.Path, "Meta/FILEMAP.toml"), TestFileMap.Canonical);
        File.WriteAllText(Path.Combine(fixture.Path, "Meta/domains.yaml"), TestFileMap.Domains);
        File.WriteAllText(Path.Combine(fixture.Path, ".gitignore"),
            ".caller-review-prompt.md\n.echo-review.md\n.sshx-*\n/Generated/echo-residuals/\n");
        File.WriteAllText(Path.Combine(fixture.Path, "unregistered.md"), "unregistered\n");
        TestGit.Run(fixture.Path, "init");
        TestGit.Run(fixture.Path, "add", ".");
        File.WriteAllText(Path.Combine(fixture.Path, "scope.json"),
            "{\"paths\":[\"unregistered.md\"],\"actors\":false}");
        using var output = new StringWriter();
        using var error = new StringWriter();
        var exit = FileMapProgram.Run(["--scope", "scope.json"], fixture.Path, output, error);
        Assert.Equal(1, exit);
        Assert.Empty(error.ToString());
        Assert.StartsWith("FILEMAP_SCOPE {\"scope\":\"delta\",\"paths\":1,\"actors\":false,\"inventory\":false}\n",
            output.ToString(), StringComparison.Ordinal);
        Assert.Contains("FILEMAP-UNCLASSIFIED unregistered.md:", output.ToString(), StringComparison.Ordinal);
        Assert.DoesNotContain("FILEMAP-GENERATED", output.ToString(), StringComparison.Ordinal);
    }
}
