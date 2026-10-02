using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.CoverBatch.Tests;

public sealed partial class CoverBatchCommandTests
{
    [Theory]
    [InlineData("digest", "scribe pack digest mismatch")]
    [InlineData("missing", "scribe resource pack could not be read")]
    [InlineData("malformed", "scribe resource pack could not be read")]
    public void DagResourcePackRejectsInvalidInputWithoutWritingArtifacts(string input, string diagnostic)
    {
        using var world = new BatchWorld();
        using var resources = new TemporaryDirectory();
        WriteEmissionInputs(world.Root);
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var digest = ScribeResourcePack.Write(packPath, [new BatchClaimDefinition().Create()]).TotalSha256;
        if (input == "digest") digest = new string('0', 64);
        if (input == "missing") File.Delete(packPath);
        if (input == "malformed") File.WriteAllBytes(packPath, [0xff]);

        var result = RunPackedDag(world, ["--scribe-pack", packPath, "--scribe-pack-digest", digest]);

        Assert.False(result.Success);
        Assert.Contains("dag-render:", result.Error, StringComparison.Ordinal);
        Assert.Contains(diagnostic, result.Error, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(world.Root, "Generated/DAG.md")));
        Assert.False(File.Exists(Path.Combine(world.Root, "Generated/truth-graph.v1.json")));
    }

    [Theory]
    [InlineData("--scribe-pack", "resources.zip")]
    [InlineData("--scribe-pack-digest", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")]
    public void DagResourcePackOptionsMustBePaired(string option, string value)
    {
        using var world = new BatchWorld();
        var result = RunPackedDag(world, [option, value]);

        Assert.False(result.Success);
        Assert.Contains("must be supplied together", result.Error, StringComparison.Ordinal);
        Assert.Contains(DagPackUsage, result.Error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("")]
    [InlineData("sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")]
    [InlineData("gggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggggg")]
    [InlineData("aaaa")]
    public void DagResourcePackRejectsInvalidDigestSyntax(string digest)
    {
        using var world = new BatchWorld();
        var result = RunPackedDag(world, ["--scribe-pack", "resources.zip", "--scribe-pack-digest", digest]);

        Assert.False(result.Success);
        Assert.Contains("64 hexadecimal", result.Error, StringComparison.Ordinal);
        Assert.Contains(DagPackUsage, result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void DagResourcePackMatchesAssemblyArtifactsByteForByteAndSupportsCheck()
    {
        using var world = new BatchWorld { UseGitReader = true };
        using var resources = new TemporaryDirectory();
        WriteEmissionInputs(world.Root);
        world.WriteReportBundle();
        var truth = DagLedgerCommandPreparation.BuildTruth(world.Repository, new PrecomputedLeanReportSource(world.Root));
        var assembly = typeof(BatchClaimDefinition).Assembly;
        var reference = DagRenderCommand.Run(world.Root, truth, false, assembly);
        Assert.True(reference.Success, reference.Error);
        var paths = new[] { "Generated/DAG.md", "Generated/truth-graph.v1.json" };
        var expected = paths.ToDictionary(path => path, path => File.ReadAllBytes(Path.Combine(world.Root, path)));
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var digest = ScribeResourcePack.Write(packPath, DocumentDefinitions.Discover(assembly, world.Root)).TotalSha256;
        foreach (var path in paths) File.Delete(Path.Combine(world.Root, path));
        string[] arguments = ["--scribe-pack", packPath, "--scribe-pack-digest", digest.ToUpperInvariant()];

        var result = RunPackedDag(world, arguments);

        Assert.True(result.Success, result.Error);
        foreach (var path in paths) Assert.Equal(expected[path], File.ReadAllBytes(Path.Combine(world.Root, path)));
        var check = RunPackedDag(world, ["--check", ..arguments]);
        Assert.True(check.Success, check.Error);
        foreach (var path in paths) Assert.Equal(expected[path], File.ReadAllBytes(Path.Combine(world.Root, path)));
    }

    [Fact]
    public void DagResourcePackUsesPackDefinitionsWithoutDiscoveringAssemblyDefinitions()
    {
        using var world = new BatchWorld { UseGitReader = true };
        using var resources = new TemporaryDirectory();
        WriteEmissionInputs(world.Root);
        world.WriteReportBundle();
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var document = ScribeDocument.Create(DefinitionDsl.Header("D5/S0/Carrier/Probe", "Resource fixture"),
            Heading.Create("Resource fixture"), DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Body"))));
        var digest = ScribeResourcePack.Write(packPath,
            [DocumentDefinition.Create(document, "Blueprint/D5/S0/Carrier/Probe.scribe.cs")]).TotalSha256;

        var result = RunPackedDag(world, ["--scribe-pack", packPath, "--scribe-pack-digest", digest]);

        Assert.True(result.Success, result.Error);
        using var graph = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(world.Root, "Generated/truth-graph.v1.json")));
        Assert.Empty(graph.RootElement.GetProperty("documents").GetProperty("describe_nodes").EnumerateArray());
        Assert.Equal("D5/S0/Carrier/Probe", Assert.Single(
            graph.RootElement.GetProperty("documents").GetProperty("document_nodes").EnumerateArray()).GetProperty("gid").GetString());
    }

    private const string DagPackUsage =
        "usage: dag-render [--check] [--scribe-pack FILE --scribe-pack-digest HEX64]";

    private static CommandResult RunPackedDag(BatchWorld world, IReadOnlyList<string> arguments) =>
        DagRenderCommand.Run(world.Root, world.Repository, new PrecomputedLeanReportSource(world.Root), arguments);
}
