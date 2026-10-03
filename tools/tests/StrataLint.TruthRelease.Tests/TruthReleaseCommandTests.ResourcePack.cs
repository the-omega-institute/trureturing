using System.Collections.Immutable;
using System.Reflection;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.Engine;
using Trureturing.Truth;

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
        var digest = WriteCorrespondingReleasePack(fixture, packPath, [SimpleDefinition(BlueprintGid)]).TotalSha256;
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
    [InlineData(false, "diskOnly=1")]
    [InlineData(true, "packOnly=1")]
    public void ResourcePackRequiresSnapshotSourceBijection(bool extra, string diagnostic)
    {
        using var fixture = CreateFixture();
        using var resources = new TemporaryDirectory();
        using var output = new TemporaryDirectory();
        DocumentDefinition[] definitions = extra
            ? [SimpleDefinition(BlueprintGid), SimpleDefinition("D5/S0/Carrier/Extra")]
            : [];
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var digest = WriteCorrespondingReleasePack(fixture, packPath, definitions).TotalSha256;

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
        var digest = WriteCorrespondingReleasePack(fixture, packPath, PackDefinitions(fixture)).TotalSha256;

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
        var digest = WriteCorrespondingReleasePack(fixture, packPath, [SimpleDefinition(BlueprintGid)]).TotalSha256;

        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments(), PackArguments(packPath, digest));

        Assert.True(exitCode == 0, console.Error);
        using var graph = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(output.Path, "truth-graph.v1.json")));
        Assert.Empty(graph.RootElement.GetProperty("documents").GetProperty("describe_nodes").EnumerateArray());
        Assert.Equal(BlueprintGid, Assert.Single(
            graph.RootElement.GetProperty("documents").GetProperty("document_nodes").EnumerateArray()).GetProperty("gid").GetString());
    }

    [Theory]
    [InlineData(ReleaseDefinitionInput)]
    [InlineData(ReleaseDataInput)]
    [InlineData(ReleaseSharedInput)]
    public void ResourcePackAcceptsRevisionInputsWithUncommittedWorkingTreeChanges(string inputPath)
    {
        using var fixture = CreateResourceInputFixture();
        using var resources = new TemporaryDirectory();
        using var reference = new TemporaryDirectory();
        using var output = new TemporaryDirectory();
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var digest = WriteReleaseInputPack(fixture, packPath).TotalSha256;
        var (referenceExit, referenceConsole) = Run(fixture, reference.Path, GreenTrustArguments(), PackArguments(packPath, digest));
        Assert.True(referenceExit == 0, referenceConsole.Error);
        File.AppendAllText(Path.Combine(ReleaseRepositoryRoot(fixture), inputPath), "\n");

        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments(), PackArguments(packPath, digest));

        Assert.True(exitCode == 0, console.Error);
        var expectedFiles = Directory.GetFiles(reference.Path).Select(Path.GetFileName).Order(StringComparer.Ordinal).ToArray();
        Assert.Equal(expectedFiles, Directory.GetFiles(output.Path).Select(Path.GetFileName).Order(StringComparer.Ordinal));
        foreach (var file in expectedFiles)
            Assert.Equal(File.ReadAllBytes(Path.Combine(reference.Path, file!)), File.ReadAllBytes(Path.Combine(output.Path, file!)));
    }

    [Theory]
    [InlineData(ReleaseDefinitionInput)]
    [InlineData(ReleaseDataInput)]
    [InlineData(ReleaseSharedInput)]
    public void ResourcePackRejectsWorkingTreeInputsThatDifferFromRevision(string inputPath)
    {
        using var fixture = CreateResourceInputFixture();
        using var resources = new TemporaryDirectory();
        using var output = new TemporaryDirectory();
        File.AppendAllText(Path.Combine(ReleaseRepositoryRoot(fixture), inputPath), "\n");
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var digest = WriteReleaseInputPack(fixture, packPath).TotalSha256;

        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments(), PackArguments(packPath, digest));

        Assert.Equal(2, exitCode);
        Assert.Contains("TRUTH_RELEASE_INVALID", console.Error, StringComparison.Ordinal);
        Assert.Contains("ScribePackCorrespondenceMismatch", console.Error, StringComparison.Ordinal);
        Assert.Contains("该包与当前文件不对应", console.Error, StringComparison.Ordinal);
        Assert.Contains("inputsChanged=1", console.Error, StringComparison.Ordinal);
        Assert.Contains(ReleaseDefinitionInput, console.Error, StringComparison.Ordinal);
        Assert.Contains("input=" + inputPath, console.Error, StringComparison.Ordinal);
        Assert.Empty(Directory.GetFileSystemEntries(output.Path));
    }

    [Fact]
    public void ResourcePackAcceptsRecordedMissingRevisionInputAfterWorkingTreeCreation()
    {
        using var fixture = CreateResourceInputFixture();
        using var resources = new TemporaryDirectory();
        using var output = new TemporaryDirectory();
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var digest = WriteReleaseInputPack(fixture, packPath).TotalSha256;
        File.WriteAllText(Path.Combine(ReleaseRepositoryRoot(fixture), ReleaseAbsentInput), "{}");

        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments(), PackArguments(packPath, digest));

        Assert.True(exitCode == 0, console.Error);
        Assert.NotEmpty(Directory.GetFiles(output.Path));
    }

    private const string ReleaseDefinitionInput = "Blueprint/" + BlueprintGid + ".scribe.cs";
    private const string ReleaseDataInput = "Golden/resource-input.json";
    private const string ReleaseSharedInput = "Blueprint/Shared/ResourceInput.cs";
    private const string ReleaseAbsentInput = "Golden/optional-resource-input.json";

    private static Fixture CreateResourceInputFixture() => CreateFixture(resourceFiles: new Dictionary<string, string>
    {
        [ReleaseDataInput] = "{}",
        [ReleaseSharedInput] = "// shared fixture\n",
    });

    private static ScribeResourcePackManifest WriteReleaseInputPack(Fixture fixture, string path)
    {
        var definitions = PackDefinitions(fixture);
        var paths = new[] { ReleaseDefinitionInput, ReleaseDataInput, ReleaseSharedInput, ReleaseAbsentInput };
        var inputs = definitions.ToDictionary(definition => definition.Document.Header.Gid.Value, _ =>
            paths.Select(inputPath =>
            {
                var fullPath = Path.Combine(ReleaseRepositoryRoot(fixture), inputPath);
                return new ScribeResourceInput(inputPath, File.Exists(fullPath)
                    ? Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(fullPath))) : null);
            }).ToImmutableArray(), StringComparer.Ordinal);
        return ScribeResourcePack.Write(path, definitions, inputs);
    }

    private static string ReleaseRepositoryRoot(Fixture fixture) =>
        Path.Combine(Path.GetDirectoryName(fixture.ReportPath)!, "repository");

    private static ScribeResourcePackManifest WriteCorrespondingReleasePack(
        Fixture fixture, string path, IEnumerable<DocumentDefinition> definitions)
    {
        var list = definitions.ToArray();
        var inputs = list.ToDictionary(definition => definition.Document.Header.Gid.Value, definition =>
        {
            var sourcePath = "Blueprint/" + definition.Document.Header.Gid.Value + ".scribe.cs";
            var fullPath = Path.Combine(ReleaseRepositoryRoot(fixture), sourcePath);
            if (!File.Exists(fullPath))
            {
                Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
                File.WriteAllText(fullPath, "// definition fixture\n");
            }
            return ImmutableArray.Create(new ScribeResourceInput(sourcePath,
                Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(fullPath)))));
        }, StringComparer.Ordinal);
        return ScribeResourcePack.Write(path, list, inputs);
    }

    private const string PackUsage = "[--scribe-pack FILE --scribe-pack-digest HEX64]";

    [Fact]
    public void ResourcePackProductionVerifierAcceptsSnapshotDefinitionsWithoutAssemblyDiscovery()
    {
        using var fixture = CreateFixture(productionVerifier: true);
        using var resources = new TemporaryDirectory();
        using var output = new TemporaryDirectory();
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var digest = WriteCorrespondingReleasePack(fixture, packPath, [SimpleDefinition(BlueprintGid)]).TotalSha256;

        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments(), PackArguments(packPath, digest));

        Assert.True(exitCode == 0, console.Error);
        var verified = TruthReleaseVerification.Verify(output.Path, Assert.Single(
            console.Output.Split(' ', StringSplitOptions.RemoveEmptyEntries),
            part => part.StartsWith("release_digest=", StringComparison.Ordinal))["release_digest=".Length..]);
        Assert.Empty(verified.ReadTruthGraph().Documents.DescribeNodes);
    }

    [Fact]
    public void ResourcePackProductionVerifierRejectsPackLiteratureReferenceWithoutWritingBundle()
    {
        using var fixture = CreateFixture(productionVerifier: true);
        using var resources = new TemporaryDirectory();
        using var output = new TemporaryDirectory();
        var definition = DocumentDefinition.Create(ScribeDocument.Create(
            DefinitionDsl.Header(BlueprintGid, "Resource fixture", Anchor.ParseCanonical("lit/fixture2000reference")),
            Heading.Create("Resource fixture"),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Body")))),
            "Blueprint/" + BlueprintGid + ".scribe.cs");
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var digest = WriteCorrespondingReleasePack(fixture, packPath, [definition]).TotalSha256;

        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments(), PackArguments(packPath, digest));

        Assert.Equal(2, exitCode);
        Assert.Contains("Scribe emission verification failed:", console.Error, StringComparison.Ordinal);
        Assert.Contains("dangling-literature-reference", console.Error, StringComparison.Ordinal);
        Assert.Contains("lit/fixture2000reference", console.Error, StringComparison.Ordinal);
        Assert.Empty(Directory.GetFileSystemEntries(output.Path));
    }

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
