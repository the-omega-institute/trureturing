using System.Collections.Immutable;
using System.Security.Cryptography;
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
        var digest = WriteCorrespondingDagPack(world.Root, packPath, [new BatchClaimDefinition().Create()]).TotalSha256;
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
        var digest = WriteCorrespondingDagPack(world.Root, packPath, DocumentDefinitions.Discover(assembly, world.Root)).TotalSha256;
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
        var digest = WriteCorrespondingDagPack(world.Root, packPath,
            [DocumentDefinition.Create(document, "Blueprint/D5/S0/Carrier/Probe.scribe.cs")]).TotalSha256;

        var result = RunPackedDag(world, ["--scribe-pack", packPath, "--scribe-pack-digest", digest]);

        Assert.True(result.Success, result.Error);
        using var graph = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(world.Root, "Generated/truth-graph.v1.json")));
        Assert.Empty(graph.RootElement.GetProperty("documents").GetProperty("describe_nodes").EnumerateArray());
        Assert.Equal("D5/S0/Carrier/Probe", Assert.Single(
            graph.RootElement.GetProperty("documents").GetProperty("document_nodes").EnumerateArray()).GetProperty("gid").GetString());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DagResourcePackRejectsChangedDefinitionWithoutWritingArtifacts(bool check)
    {
        using var world = new BatchWorld { UseGitReader = true };
        using var resources = new TemporaryDirectory();
        WriteEmissionInputs(world.Root);
        world.WriteReportBundle();
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var digest = WriteCorrespondingDagPack(world.Root, packPath, [new BatchClaimDefinition().Create()]).TotalSha256;
        const string definitionPath = "Blueprint/D5/S0/Carrier/Probe.scribe.cs";
        File.AppendAllText(Path.Combine(world.Root, definitionPath), "\n");
        var before = DagFileImage(world.Root);
        string[] arguments = ["--scribe-pack", packPath, "--scribe-pack-digest", digest];

        var result = RunPackedDagCli(world, check ? ["--check", ..arguments] : arguments);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("ScribePackCorrespondenceMismatch", result.Console.Error, StringComparison.Ordinal);
        Assert.Contains("该包与当前文件不对应", result.Console.Error, StringComparison.Ordinal);
        Assert.Contains("inputsChanged=1", result.Console.Error, StringComparison.Ordinal);
        Assert.Contains(definitionPath, result.Console.Error, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(world.Root, "Generated/DAG.md")));
        Assert.False(File.Exists(Path.Combine(world.Root, "Generated/truth-graph.v1.json")));
        AssertDagFileImage(before, world.Root);
    }

    private static ScribeResourcePackManifest WriteCorrespondingDagPack(
        string root, string path, IEnumerable<DocumentDefinition> definitions)
    {
        var list = definitions.ToArray();
        var inputs = list.ToDictionary(definition => definition.Document.Header.Gid.Value, definition =>
        {
            var sourcePath = "Blueprint/" + definition.Document.Header.Gid.Value + ".scribe.cs";
            var fullPath = Path.Combine(root, sourcePath);
            if (!File.Exists(fullPath)) WriteScribeFixture(root, sourcePath, "// definition fixture\n");
            return ImmutableArray.Create(new ScribeResourceInput(sourcePath,
                Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(fullPath)))));
        }, StringComparer.Ordinal);
        return ScribeResourcePack.Write(path, list, inputs);
    }

    private const string DagPackUsage =
        "usage: dag-render [--check] [--scribe-pack FILE --scribe-pack-digest HEX64]";

    [Theory]
    [InlineData("Generated/DAG.md")]
    [InlineData("Generated/truth-graph.v1.json")]
    public void DagResourcePackCheckRejectsMissingArtifactWithoutWritingFiles(string path)
    {
        using var world = new BatchWorld { UseGitReader = true };
        using var resources = new TemporaryDirectory();
        WriteEmissionInputs(world.Root);
        world.WriteReportBundle();
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var digest = WriteCorrespondingDagPack(world.Root, packPath, [new BatchClaimDefinition().Create()]).TotalSha256;
        string[] arguments = ["--scribe-pack", packPath, "--scribe-pack-digest", digest];
        var emitted = RunPackedDag(world, arguments);
        Assert.True(emitted.Success, emitted.Error);
        File.Delete(Path.Combine(world.Root, path));
        var before = DagFileImage(world.Root);

        var result = RunPackedDagCli(world, ["--check", ..arguments]);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains(path, result.Console.Error, StringComparison.Ordinal);
        AssertDagFileImage(before, world.Root);
    }

    [Theory]
    [InlineData("Generated/DAG.md")]
    [InlineData("Generated/truth-graph.v1.json")]
    public void DagResourcePackCheckRejectsStaleArtifactWithoutWritingFiles(string path)
    {
        using var world = new BatchWorld { UseGitReader = true };
        using var resources = new TemporaryDirectory();
        WriteEmissionInputs(world.Root);
        world.WriteReportBundle();
        var packPath = Path.Combine(resources.Path, "resources.zip");
        var digest = WriteCorrespondingDagPack(world.Root, packPath, [new BatchClaimDefinition().Create()]).TotalSha256;
        string[] arguments = ["--scribe-pack", packPath, "--scribe-pack-digest", digest];
        var emitted = RunPackedDag(world, arguments);
        Assert.True(emitted.Success, emitted.Error);
        File.WriteAllText(Path.Combine(world.Root, path), "stale\n");
        var before = DagFileImage(world.Root);

        var result = RunPackedDagCli(world, ["--check", ..arguments]);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains(path, result.Console.Error, StringComparison.Ordinal);
        AssertDagFileImage(before, world.Root);
    }

    private static Dictionary<string, byte[]> DagFileImage(string root) =>
        Directory.GetFiles(root, "*", SearchOption.AllDirectories)
            .Select(path => Path.GetRelativePath(root, path))
            .Where(path => !path.StartsWith(".git/", StringComparison.Ordinal))
            .ToDictionary(path => path, path => File.ReadAllBytes(Path.Combine(root, path)), StringComparer.Ordinal);

    private static (int ExitCode, BufferedConsole Console) RunPackedDagCli(
        BatchWorld world, IReadOnlyList<string> arguments)
    {
        var console = new BufferedConsole();
        var environment = new ProductionCliEnvironment(world.Root, world.Repository,
            new PrecomputedLeanReportSource(world.Root), new ProductionScribeEmissionVerifier());
        return (CliApplication.Run(["dag-render", ..arguments], environment, console), console);
    }

    private static void AssertDagFileImage(IReadOnlyDictionary<string, byte[]> before, string root)
    {
        var after = DagFileImage(root);
        Assert.Equal(before.Keys.Order(StringComparer.Ordinal), after.Keys.Order(StringComparer.Ordinal));
        foreach (var (path, bytes) in before) Assert.Equal(bytes, after[path]);
    }

    private static CommandResult RunPackedDag(BatchWorld world, IReadOnlyList<string> arguments) =>
        DagRenderCommand.Run(world.Root, world.Repository, new PrecomputedLeanReportSource(world.Root), arguments);
}
