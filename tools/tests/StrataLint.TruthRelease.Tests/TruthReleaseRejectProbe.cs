using StrataLint.Scribe;
using Trureturing.Truth;
using Xunit;

namespace StrataLint.TruthRelease.Tests;

public sealed partial class TruthReleaseCommandTests
{
    [Fact]
    public void InstalledTruthReleaseRejectsDanglingScribeReferenceWithoutWriting()
    {
        using var fixture = CreateFixture(productionVerifier: true);
        using var resources = new TemporaryDirectory();
        using var output = new TemporaryDirectory();
        var definition = DocumentDefinition.Create(ScribeDocument.Create(
            DefinitionDsl.Header(BlueprintGid, "Installed rejection probe", Anchor.ParseCanonical("lit/integrationprobe2000missing")),
            Heading.Create("Installed rejection probe"),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Probe body")))),
            "Blueprint/" + BlueprintGid + ".scribe.cs");
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var digest = ScribeResourcePack.Write(packPath, [definition]).TotalSha256;
        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments(), PackArguments(packPath, digest));
        Assert.Equal(2, exitCode);
        Assert.Contains("TRUTH_RELEASE_INVALID", console.Error, StringComparison.Ordinal);
        Assert.Contains("dangling-literature-reference", console.Error, StringComparison.Ordinal);
        Assert.Empty(Directory.EnumerateFileSystemEntries(output.Path));
    }

    [Fact]
    public void InstalledTruthReleaseReaderRejectsRetiredSchemaAndResidualField()
    {
        using var fixture = CreateFixture(productionVerifier: true);
        using var output = new TemporaryDirectory();
        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments());
        Assert.True(exitCode == 0, console.Error);
        var manifest = File.ReadAllText(Path.Combine(output.Path, TruthReleaseBundleWriter.ManifestFileName));
        Assert.Throws<FormatException>(() => TruthReleaseManifestReader.Read(
            manifest.Replace("truth-release.v2", "truth-release.v1", StringComparison.Ordinal)));
        Assert.Throws<FormatException>(() => TruthReleaseManifestReader.Read(
            manifest.Replace("\"artifacts\":{", "\"artifacts\":{\"residual_frontier\":{},", StringComparison.Ordinal)));
    }
}
