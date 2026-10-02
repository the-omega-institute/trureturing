using System.Reflection;
using System.Text.Json;

namespace StrataLint.TruthRelease.Tests;

public sealed partial class TruthReleaseCommandTests
{
    [Theory]
    [InlineData("digest", "scribe pack digest mismatch")]
    [InlineData("missing", "scribe resource pack could not be read")]
    [InlineData("malformed", "scribe resource pack could not be read")]
    public void ResourcePackRejectsInvalidInputWithoutWritingBundle(string input, string diagnostic)
    {
        using var fixture = CreateFixture();
        using var resources = new TemporaryDirectory();
        using var output = new TemporaryDirectory();
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var digest = ScribeResourcePack.Write(packPath, [SimpleDefinition(BlueprintGid)]).TotalSha256;
        if (input == "digest") digest = new string('0', 64);
        if (input == "missing") File.Delete(packPath);
        if (input == "malformed") File.WriteAllBytes(packPath, [0xff]);

        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments(), PackArguments(packPath, digest));

        Assert.Equal(2, exitCode);
        Assert.Contains("TRUTH_RELEASE_INVALID", console.Error, StringComparison.Ordinal);
        Assert.Contains(diagnostic, console.Error, StringComparison.Ordinal);
        Assert.Empty(Directory.GetFileSystemEntries(output.Path));
    }

    [Theory]
    [InlineData("--scribe-pack", "resources.zip")]
    [InlineData("--scribe-pack-digest", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")]
    public void ResourcePackOptionsMustBePaired(string option, string value)
    {
        using var fixture = CreateFixture();
        using var output = new TemporaryDirectory();
        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments(), [option, value]);

        Assert.Equal(1, exitCode);
        Assert.Contains(PackUsage, console.Error, StringComparison.Ordinal);
        Assert.Empty(Directory.GetFileSystemEntries(output.Path));
    }

    [Theory]
    [InlineData("")]
    [InlineData("aaaa")]
    [InlineData("sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")]
    [InlineData("gggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggg")]
    public void ResourcePackRejectsInvalidDigestSyntax(string digest)
    {
        using var fixture = CreateFixture();
        using var output = new TemporaryDirectory();
        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments(), PackArguments("resources.zip", digest));

        Assert.Equal(1, exitCode);
        Assert.Contains(PackUsage, console.Error, StringComparison.Ordinal);
        Assert.Empty(Directory.GetFileSystemEntries(output.Path));
    }

    [Theory]
    [InlineData(false, "unregistered Scribe source:")]
    [InlineData(true, "registered Scribe source is missing:")]
    public void ResourcePackRequiresSnapshotSourceBijection(bool extra, string diagnostic)
    {
        using var fixture = CreateFixture();
        using var resources = new TemporaryDirectory();
        using var output = new TemporaryDirectory();
        DocumentDefinition[] definitions = extra
            ? [SimpleDefinition(BlueprintGid), SimpleDefinition("D5/S0/Carrier/Extra")]
            : [];
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var digest = ScribeResourcePack.Write(packPath, definitions).TotalSha256;

        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments(), PackArguments(packPath, digest));

        Assert.Equal(2, exitCode);
        Assert.Contains("TRUTH_RELEASE_INVALID", console.Error, StringComparison.Ordinal);
        Assert.Contains(diagnostic, console.Error, StringComparison.Ordinal);
        Assert.Empty(Directory.GetFileSystemEntries(output.Path));
    }

    [Fact]
    public void ResourcePackMatchesAssemblyBundleByteForByte()
    {
        using var fixture = CreateFixture();
        using var resources = new TemporaryDirectory();
        using var reference = new TemporaryDirectory();
        using var output = new TemporaryDirectory();
        var (referenceExit, referenceConsole) = Run(fixture, reference.Path, GreenTrustArguments());
        Assert.True(referenceExit == 0, referenceConsole.Error);
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var digest = ScribeResourcePack.Write(packPath, PackDefinitions(fixture)).TotalSha256;

        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments(), PackArguments(packPath, digest.ToUpperInvariant()));

        Assert.True(exitCode == 0, console.Error);
        var expectedFiles = Directory.GetFiles(reference.Path).Select(Path.GetFileName).Order(StringComparer.Ordinal).ToArray();
        Assert.Equal(expectedFiles, Directory.GetFiles(output.Path).Select(Path.GetFileName).Order(StringComparer.Ordinal));
        foreach (var file in expectedFiles)
            Assert.Equal(File.ReadAllBytes(Path.Combine(reference.Path, file!)), File.ReadAllBytes(Path.Combine(output.Path, file!)));
    }

    [Fact]
    public void ResourcePackUsesPackDocumentContentInsteadOfAssemblyContent()
    {
        using var fixture = CreateFixture();
        using var resources = new TemporaryDirectory();
        using var output = new TemporaryDirectory();
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var digest = ScribeResourcePack.Write(packPath, [SimpleDefinition(BlueprintGid)]).TotalSha256;

        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments(), PackArguments(packPath, digest));

        Assert.True(exitCode == 0, console.Error);
        using var graph = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(output.Path, "truth-graph.v1.json")));
        Assert.Empty(graph.RootElement.GetProperty("documents").GetProperty("describe_nodes").EnumerateArray());
        Assert.Equal(BlueprintGid, Assert.Single(
            graph.RootElement.GetProperty("documents").GetProperty("document_nodes").EnumerateArray()).GetProperty("gid").GetString());
    }

    private const string PackUsage = "[--scribe-pack FILE --scribe-pack-digest HEX64]";

    private static string[] PackArguments(string path, string digest) =>
        ["--scribe-pack", path, "--scribe-pack-digest", digest];

    private static DocumentDefinition[] PackDefinitions(Fixture fixture) =>
        DocumentDefinitions.Discover(Assembly.Load("StrataLint.Scribe.Documents"),
            Path.Combine(Path.GetDirectoryName(fixture.ReportPath)!, "repository"))
            .Where(definition => definition.Document.Header.Gid.Value == BlueprintGid).ToArray();

    private static DocumentDefinition SimpleDefinition(string gid) => DocumentDefinition.Create(
        ScribeDocument.Create(DefinitionDsl.Header(gid, "Resource fixture"), Heading.Create("Resource fixture"),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Body")))),
        "Blueprint/" + gid + ".scribe.cs");
}
