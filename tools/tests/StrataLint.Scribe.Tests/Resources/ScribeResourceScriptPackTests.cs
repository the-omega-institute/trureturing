using System.Collections.Immutable;
using System.Reflection;
using System.Text;
using System.Text.Json.Nodes;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeResourceScriptPackTests
{
    [Fact]
    public void PackReportsEveryHostFailureWithoutCreatingOutput()
    {
        using var root = Prepare();
        Write(root.Path, "Alpha", "internal sealed class Alpha { }");
        Write(root.Path, "Beta", "internal sealed class Beta { }");
        var error = new StringWriter();
        Assert.Equal(1, Cli(root.Path, ["resources", "pack", "--out", "resources.zip"], TextWriter.Null, error));
        Assert.Contains(PathFor("Alpha"), error.ToString(), StringComparison.Ordinal);
        Assert.Contains(PathFor("Beta"), error.ToString(), StringComparison.Ordinal);
        Assert.Contains("DefinitionMissing", error.ToString(), StringComparison.Ordinal);
        Assert.False(File.Exists(root.Resolve("resources.zip")));
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("malformed")]
    [InlineData("version")]
    [InlineData("entry-digest")]
    public void InvalidReusePackReturnsTwoWithoutOutput(string kind)
    {
        using var root = Prepare();
        Definition(root.Path, "Alpha");
        var old = root.Resolve("input.zip");
        if (kind == "malformed") TemporaryFileSystem.File.WriteAllBytes(old, [0xff]);
        if (kind is "version" or "entry-digest")
        {
            ScribeResourcePack.Write(old, [ScribeResourcePackTests.Definition("Alpha")]);
            var entries = ScribeResourcePackTests.ReadZip(old);
            if (kind == "entry-digest") entries[0].Bytes[0] ^= 1;
            else
            {
                var index = entries.FindIndex(item => item.Name == "manifest.json");
                var manifest = JsonNode.Parse(entries[index].Bytes)!;
                manifest["version"] = -1;
                entries[index] = ("manifest.json", Encoding.UTF8.GetBytes(manifest.ToJsonString()));
            }
            ScribeResourcePackTests.RewriteZip(old, entries);
        }
        var error = new StringWriter();
        Assert.Equal(2, Cli(root.Path,
            ["resources", "pack", "--out", "output.zip", "--reuse-from", "input.zip"], TextWriter.Null, error));
        Assert.NotEmpty(error.ToString());
        Assert.False(File.Exists(root.Resolve("output.zip")));
    }

    [Fact]
    public void PackUsesScriptsAndMatchesDirectCanonicalEncoding()
    {
        using var root = Prepare();
        Definition(root.Path, "Alpha");
        Definition(root.Path, "Beta");
        var output = new StringWriter();
        var error = new StringWriter();
        Assert.Equal(0, Cli(root.Path, ["resources", "pack", "--out", "resources.zip"], output, error));
        Assert.Empty(error.ToString());
        Assert.Contains("executed=2 reused=0", output.ToString(), StringComparison.Ordinal);
        Assert.Single(output.ToString().Split(Environment.NewLine, StringSplitOptions.RemoveEmptyEntries));
        var pack = ScribeResourcePack.Open(root.Resolve("resources.zip"));
        Assert.Equal(2, pack.Manifest.EntryCount);
        foreach (var name in new[] { "Alpha", "Beta" })
        {
            var result = ScribeScriptHost.Execute(root.Path, PathFor(name));
            Assert.True(result.IsSuccess, result.Failure?.ToString());
            Assert.Equal(ScribeResourceCodec.Encode(result.Definition!), pack.EncodedBytes(GidFor(name)).ToArray());
        }
    }

    [Fact]
    public void UnchangedInputsReuseEveryPathAndPreserveManifestDigest()
    {
        using var root = Prepare();
        Definition(root.Path, "Alpha");
        Definition(root.Path, "Beta");
        var first = Pack(root.Path, "first.zip");
        var second = Pack(root.Path, "second.zip", "first.zip");
        AssertPaths(first.Executed, "Alpha", "Beta");
        Assert.Empty(first.Reused);
        Assert.Empty(second.Executed);
        AssertPaths(second.Reused, "Alpha", "Beta");
        Assert.Equal(first.Manifest.TotalSha256, second.Manifest.TotalSha256);
        foreach (var name in new[] { "Alpha", "Beta" })
            Assert.Equal(ScribeResourcePack.Open(root.Resolve("first.zip")).EncodedBytes(GidFor(name)).ToArray(),
                ScribeResourcePack.Open(root.Resolve("second.zip")).EncodedBytes(GidFor(name)).ToArray());
    }

    [Fact]
    public void EntryChangeExecutesOnlyThatPath()
    {
        using var root = Prepare();
        Definition(root.Path, "Alpha");
        Definition(root.Path, "Beta");
        Pack(root.Path, "first.zip");
        Definition(root.Path, "Alpha", "changed");
        var second = Pack(root.Path, "second.zip", "first.zip");
        AssertPaths(second.Executed, "Alpha");
        AssertPaths(second.Reused, "Beta");
        Assert.Equal(Pack(root.Path, "full.zip").Manifest.TotalSha256, second.Manifest.TotalSha256);
    }

    [Fact]
    public void SharedClosureChangeExecutesOnlyItsTransitiveDependents()
    {
        using var root = Prepare();
        SharedTree(root.Path, "first");
        Pack(root.Path, "first.zip");
        SharedTree(root.Path, "second");
        var second = Pack(root.Path, "second.zip", "first.zip");
        AssertPaths(second.Executed, "Alpha", "Leaf", "Shared");
        AssertPaths(second.Reused, "Beta");
        Assert.Equal(Pack(root.Path, "full.zip").Manifest.TotalSha256, second.Manifest.TotalSha256);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ProjectionAssessmentChangeExecutesOnlyItsReferencingPath(bool unprojectable)
    {
        using var root = new StatementProjectionTestRepository();
        TemporaryFileSystem.File.WriteAllText(System.IO.Path.Combine(root.Path, "global.json"), "{}");
        ProjectionFixture(root, 1, unprojectable);
        Definition(root.Path, "Alpha", projection: true, unprojectable: unprojectable);
        Definition(root.Path, "Beta");
        Pack(root.Path, "first.zip");
        ProjectionFixture(root, 2, unprojectable);
        var second = Pack(root.Path, "second.zip", "first.zip");
        AssertPaths(second.Executed, "Alpha");
        AssertPaths(second.Reused, "Beta");
        Assert.Equal(Pack(root.Path, "full.zip").Manifest.TotalSha256, second.Manifest.TotalSha256);
    }

    [Fact]
    public void SemanticVersionChangeInvalidatesEveryInputKey()
    {
        using var root = Prepare();
        Definition(root.Path, "Alpha");
        Definition(root.Path, "Beta");
        var first = Pack(root.Path, "first.zip", version: 41);
        var second = Pack(root.Path, "second.zip", "first.zip", version: 42);
        AssertPaths(second.Executed, "Alpha", "Beta");
        Assert.Empty(second.Reused);
        Assert.NotEqual(first.Manifest.TotalSha256, second.Manifest.TotalSha256);
        var before = InputKeys(root.Resolve("first.zip"));
        var after = InputKeys(root.Resolve("second.zip"));
        Assert.All(before.Keys, key => Assert.NotEqual(before[key], after[key]));
    }

    [Fact]
    public void AddedPathExecutesAndDeletedPathIsAbsent()
    {
        using var root = Prepare();
        Definition(root.Path, "Alpha");
        Definition(root.Path, "Beta");
        Pack(root.Path, "first.zip");
        TemporaryFileSystem.File.Delete(root.Resolve(PathFor("Alpha")));
        Definition(root.Path, "Gamma");
        var second = Pack(root.Path, "second.zip", "first.zip");
        AssertPaths(second.Executed, "Gamma");
        AssertPaths(second.Reused, "Beta");
        Assert.Equal(new[] { GidFor("Beta"), GidFor("Gamma") }, second.Manifest.Entries.Select(item => item.Gid));
    }

    private static void ProjectionFixture(StatementProjectionTestRepository root, int number, bool unprojectable) =>
        root.WriteFixture("pilot", new StatementProjectionTestRepository.Pin("Fixture.claim", GidFor("Alpha") + ".lean",
            unprojectable ? "unregistered-" + number : StatementProjectionResolutionTests.Equality(number)));

    private static Dictionary<string, string> InputKeys(string path)
    {
        var manifest = JsonNode.Parse(ScribeResourcePackTests.ReadZip(path).Single(item => item.Name == "manifest.json").Bytes)!;
        return manifest["entries"]!.AsArray().ToDictionary(item => item!["path"]!.GetValue<string>(),
            item => item!["inputKey"]!.GetValue<string>(), StringComparer.Ordinal);
    }

    private static PackObservation Pack(string root, string output, string? reuse = null, int? version = null)
    {
        var type = typeof(ScribeResourcePack).Assembly.GetType("StrataLint.Scribe.ScribeResourceScriptPacker");
        Assert.NotNull(type);
        object? value;
        if (version is null)
            value = type.GetMethod("Write", BindingFlags.Public | BindingFlags.Static)!
                .Invoke(null, [root, System.IO.Path.Combine(root, output), reuse is null ? null : System.IO.Path.Combine(root, reuse)]);
        else
            value = type.GetMethod("WriteCore", BindingFlags.NonPublic | BindingFlags.Static)!
                .Invoke(null, [root, System.IO.Path.Combine(root, output), reuse is null ? null : System.IO.Path.Combine(root, reuse), version.Value]);
        Assert.NotNull(value);
        T Get<T>(string name) => Assert.IsType<T>(value.GetType().GetProperty(name)!.GetValue(value));
        Assert.Empty(Get<ImmutableArray<ScribeScriptFailure>>("Failures"));
        return new(Get<ScribeResourcePackManifest>("Manifest"),
            Get<ImmutableArray<string>>("ExecutedPaths"), Get<ImmutableArray<string>>("ReusedPaths"));
    }

    private sealed record PackObservation(ScribeResourcePackManifest Manifest, ImmutableArray<string> Executed, ImmutableArray<string> Reused);

    private static TemporaryRoot Prepare()
    {
        var root = new TemporaryRoot();
        TemporaryFileSystem.File.WriteAllText(root.Resolve("global.json"), "{}");
        TemporaryFileSystem.Directory.CreateDirectory(root.Resolve("Blueprint"));
        return root;
    }

    private static int Cli(string root, string[] arguments, TextWriter output, TextWriter error) =>
        ScribeCli.Run(typeof(ScribeResourcePack).Assembly, arguments, root, output, error);

    private static void AssertPaths(IEnumerable<string> paths, params string[] names) =>
        Assert.Equal(names.Select(PathFor), paths);

    private static string PathFor(string name) => "Blueprint/" + GidFor(name) + ".scribe.cs";
    private static string GidFor(string name) => "D5/S0/Test/" + name;

    private static void SharedTree(string root, string content)
    {
        Definition(root, "Leaf", extra: $"internal const string Value = \"{content}\";");
        Definition(root, "Shared", expression: "Leaf.Value", shared: "Leaf", extra: "internal static string Value => Leaf.Value;");
        Definition(root, "Alpha", expression: "Shared.Value", shared: "Shared");
        Definition(root, "Beta");
    }

    private static void Definition(string root, string name, string content = "content", string? expression = null,
        string? shared = null, string extra = "", bool projection = false, bool unprojectable = false)
    {
        var block = projection
            ? $"new DocumentBlock.Section(H(\"Section\"), Blocks(Describe.Lean(DescribeId.Create(\"claim\"), DeclarationHandle.Create(\"{GidFor(name)}.claim\"), H(\"Claim\"), StatementSource.{(unprojectable ? "FromAuthor(Num(7))" : "FromLean()")}, AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(\"content\"))), DescribeRole.Theorem)))"
            : $"Paragraph(Text({expression ?? "\"" + content + "\""}))";
        Write(root, name, $$"""
            {{(shared is null ? "" : $"[ScribeSharedSource(\"{PathFor(shared)}\")]")}}
            internal sealed class {{name}} : IScribeDocumentDefinition
            {
                {{extra}}
                public DocumentDefinition Create() => DocumentDefinition.Create(
                    ScribeNode.Create("digest", H("title"), Blocks({{block}})));
            }
            """);
    }

    private static void Write(string root, string name, string body)
    {
        var full = System.IO.Path.Combine(root, PathFor(name));
        TemporaryFileSystem.Directory.CreateDirectory(System.IO.Path.GetDirectoryName(full)!);
        TemporaryFileSystem.File.WriteAllText(full, "using StrataLint.Engine; using StrataLint.Scribe; using static StrataLint.Scribe.DefinitionDsl; " + body);
    }
}
