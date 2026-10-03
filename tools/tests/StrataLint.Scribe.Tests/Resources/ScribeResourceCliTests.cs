using System.Reflection;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json.Nodes;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeResourceCliTests
{
    private static readonly Assembly Documents = new FixtureAssembly();

    [Fact]
    public void GeneralUsageIncludesTheResourcePackCommand()
    {
        using var root = Prepare();
        var error = new StringWriter();
        Assert.Equal(2, ScribeCli.Run(Documents, [], root.Path, TextWriter.Null, error));
        Assert.Contains("resources pack --out <file>", error.ToString(), StringComparison.Ordinal);
        Assert.Contains("resources verify --pack <file>", error.ToString(), StringComparison.Ordinal);
        Assert.Contains("resources release --out <directory>", error.ToString(), StringComparison.Ordinal);
        Assert.Contains("resources verify-release --dir <directory>", error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("resources")]
    [InlineData("resources", "pack")]
    [InlineData("resources", "pack", "--pack", "file.zip")]
    [InlineData("resources", "verify", "--out", "file.zip")]
    [InlineData("resources", "pack", "--out", "")]
    [InlineData("resources", "verify", "--pack", "file.zip", "--extra")]
    [InlineData("resources", "unknown", "--out", "file.zip")]
    public void InvalidArgumentsReturnTwoAndResourceUsage(params string[] arguments)
    {
        using var root = new TemporaryRoot();
        var error = new StringWriter();

        Assert.Equal(2, ScribeCli.Run(Documents, arguments, root.Path, TextWriter.Null, error));
        Assert.Contains("resources pack --out <file>", error.ToString(), StringComparison.Ordinal);
        Assert.Contains("resources release --out <directory>", error.ToString(), StringComparison.Ordinal);
        Assert.Contains("resources verify-release --dir <directory>", error.ToString(), StringComparison.Ordinal);
        Assert.Contains("resources verify --pack <file>", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void VerifyReportsOneByteCorruptionWithNamedReason()
    {
        using var root = Prepare();
        var path = root.Resolve("resources.zip");
        ScribeResourcePack.Write(path, [ScribeResourcePackTests.Definition("First"), ScribeResourcePackTests.Definition("Second")]);
        var entries = ScribeResourcePackTests.ReadZip(path);
        entries[0].Bytes[0] ^= 1;
        ScribeResourcePackTests.RewriteZip(path, entries);
        var error = new StringWriter();

        Assert.Equal(1, Run(root, ["resources", "verify", "--pack", path], TextWriter.Null, error));
        Assert.Contains("EntryDigestMismatch", error.ToString(), StringComparison.Ordinal);
        Assert.Contains("D5/S0/Synthetic/First.scribe.json", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void VerifyRejectsMissingInputWithExitTwo()
    {
        using var root = new TemporaryRoot();
        var error = new StringWriter();

        Assert.Equal(2, Run(root, ["resources", "verify", "--pack", "missing.zip"], TextWriter.Null, error));
        Assert.Contains("missing.zip", error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public void VerifyReportsEntryCountAndTotalDigestWithoutRepositoryOrAssembly(int count)
    {
        using var root = new TemporaryRoot();
        var path = root.Resolve("resources.zip");
        var manifest = ScribeResourcePack.Write(path,
            new[] { "First", "Second" }.Take(count).Select(ScribeResourcePackTests.Definition));
        var list = "[" + string.Join(",", manifest.Entries.Select(entry =>
            $"{{\"path\":\"{entry.Path}\",\"gid\":\"{entry.Gid}\",\"sha256\":\"{entry.Sha256}\"}}")) + "]";
        var digest = Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(list)));
        var output = new StringWriter();
        var error = new StringWriter();

        Assert.False(Directory.Exists(root.Resolve("Blueprint")));
        Assert.Equal(0, ScribeCli.Run(() => throw new InvalidOperationException("Definitions must not be loaded."),
            ["resources", "verify", "--pack", "resources.zip"], root.Path, output, error));
        Assert.Equal($"resources verify: entries={count} totalSha256={digest}{Environment.NewLine}", output.ToString());
        Assert.Empty(error.ToString());
    }

    [Fact]
    public void VerifyRejectsNonZipInputWithExitTwo()
    {
        using var root = new TemporaryRoot();
        TemporaryFileSystem.File.WriteAllText(root.Resolve("resources.zip"), "not a zip");
        var error = new StringWriter();

        Assert.Equal(2, Run(root, ["resources", "verify", "--pack", "resources.zip"], TextWriter.Null, error));
        Assert.Contains("InvalidArchive", error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("totalSha256", 1, "TotalDigestMismatch")]
    [InlineData("entryCount", 2, "InvalidManifest")]
    public void VerifyDistinguishesDigestMismatchFromMalformedManifest(string field, int exit, string reason)
    {
        using var root = Prepare();
        var path = root.Resolve("resources.zip");
        ScribeResourcePack.Write(path, [ScribeResourcePackTests.Definition("First")]);
        var entries = ScribeResourcePackTests.ReadZip(path);
        var index = entries.FindIndex(item => item.Name == "manifest.json");
        var manifest = JsonNode.Parse(entries[index].Bytes)!;
        manifest[field] = field == "totalSha256" ? JsonValue.Create(new string('0', 64)) : JsonValue.Create(9);
        entries[index] = ("manifest.json", Encoding.UTF8.GetBytes(manifest.ToJsonString()));
        ScribeResourcePackTests.RewriteZip(path, entries);
        var error = new StringWriter();

        Assert.Equal(exit, Run(root, ["resources", "verify", "--pack", path], TextWriter.Null, error));
        Assert.Contains(reason, error.ToString(), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("extra")]
    [InlineData("content")]
    public void VerifyAcceptsPackIndependentOfLocalDefinitionSetAndContent(string mismatch)
    {
        using var root = Prepare();
        var path = root.Resolve("resources.zip");
        var definitions = new List<DocumentDefinition> { ScribeResourcePackTests.Definition("First") };
        if (mismatch != "missing") definitions.Add(ScribeResourcePackTests.Definition("Second"));
        if (mismatch == "extra") definitions.Add(ScribeResourcePackTests.Definition("Third"));
        if (mismatch == "content")
        {
            var document = definitions[0].Document;
            definitions[0] = DocumentDefinition.Create(
                ScribeDocument.Create(document.Header, DefinitionDsl.H("Changed"), document.Content), definitions[0].SourcePath);
        }
        ScribeResourcePack.Write(path, definitions);
        var output = new StringWriter();
        var error = new StringWriter();

        Assert.Equal(0, Run(root, ["resources", "verify", "--pack", path], output, error));
        Assert.Equal($"resources verify: entries={definitions.Count} totalSha256={ScribeResourcePack.Open(path).Manifest.TotalSha256}{Environment.NewLine}",
            output.ToString());
        Assert.Empty(error.ToString());
    }

    [Theory]
    [InlineData("formatting", 0, null)]
    [InlineData("unknown-tag", 1, "UnknownType")]
    public void VerifyAcceptsFormattingAndStronglyDecodesEveryDigestValidResource(
        string change, int expectedExit, string? expectedReason)
    {
        using var root = Prepare();
        var path = root.Resolve("resources.zip");
        ScribeResourcePack.Write(path, [ScribeResourcePackTests.Definition("First"), ScribeResourcePackTests.Definition("Second")]);
        var entries = ScribeResourcePackTests.ReadZip(path);
        var text = Encoding.UTF8.GetString(entries[1].Bytes);
        entries[1] = (entries[1].Name, Encoding.UTF8.GetBytes(change == "formatting" ? " " + text :
            text.Replace("\"type\":\"ScribeDocument\"", "\"type\":\"Unknown\"", StringComparison.Ordinal)));
        var index = entries.FindIndex(item => item.Name == "manifest.json");
        var manifest = JsonNode.Parse(entries[index].Bytes)!;
        manifest["entries"]![1]!["sha256"] = Convert.ToHexStringLower(SHA256.HashData(entries[1].Bytes));
        manifest["totalSha256"] = Convert.ToHexStringLower(SHA256.HashData(
            Encoding.UTF8.GetBytes(manifest["entries"]!.ToJsonString())));
        entries[index] = ("manifest.json", Encoding.UTF8.GetBytes(manifest.ToJsonString()));
        ScribeResourcePackTests.RewriteZip(path, entries);
        var error = new StringWriter();
        var output = new StringWriter();

        Assert.Equal(expectedExit, Run(root, ["resources", "verify", "--pack", path], output, error));
        if (expectedReason is null)
        {
            Assert.Empty(error.ToString());
            Assert.Equal($"resources verify: entries=2 totalSha256={manifest["totalSha256"]}{Environment.NewLine}", output.ToString());
        }
        else
        {
            Assert.Contains(expectedReason, error.ToString(), StringComparison.Ordinal);
            Assert.Contains("D5/S0/Synthetic/Second", error.ToString(), StringComparison.Ordinal);
            Assert.Empty(output.ToString());
        }
    }

    [Fact]
    public void VerifyRejectsUnreachableDescribeWithExitOneAndGid()
    {
        using var root = Prepare();
        var path = root.Resolve("resources.zip");
        var definition = ScribeResourceCodecTests.ClaimDefinition();
        ScribeResourcePack.Write(path, [definition]);
        var entries = ScribeResourcePackTests.ReadZip(path);
        var resource = JsonNode.Parse(entries[0].Bytes)!;
        resource["document"]!["content"]![0]!["construction"]!["statementFormula"] = null;
        entries[0] = (entries[0].Name, Encoding.UTF8.GetBytes(resource.ToJsonString()));
        var index = entries.FindIndex(item => item.Name == "manifest.json");
        var manifest = JsonNode.Parse(entries[index].Bytes)!;
        manifest["entries"]![0]!["sha256"] = Convert.ToHexStringLower(SHA256.HashData(entries[0].Bytes));
        manifest["totalSha256"] = Convert.ToHexStringLower(SHA256.HashData(
            Encoding.UTF8.GetBytes(manifest["entries"]!.ToJsonString())));
        entries[index] = ("manifest.json", Encoding.UTF8.GetBytes(manifest.ToJsonString()));
        ScribeResourcePackTests.RewriteZip(path, entries);
        var error = new StringWriter();

        Assert.Equal(1, Run(root, ["resources", "verify", "--pack", path], TextWriter.Null, error));
        Assert.Contains("ExtraField", error.ToString(), StringComparison.Ordinal);
        Assert.Contains(definition.Document.Header.Gid.Value, error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void PackScriptsThenVerifyReportsPackSummary()
    {
        using var root = Prepare();
        var output = new StringWriter();
        var error = new StringWriter();

        Assert.Equal(0, Run(root, ["resources", "pack", "--out", "resources.zip"], output, error));
        Assert.Contains("entries=2", output.ToString(), StringComparison.Ordinal);
        Assert.Contains("uncompressedBytes=", output.ToString(), StringComparison.Ordinal);
        Assert.Contains("totalSha256=", output.ToString(), StringComparison.Ordinal);
        Assert.Single(output.ToString().Split(Environment.NewLine, StringSplitOptions.RemoveEmptyEntries));
        output.GetStringBuilder().Clear();
        Assert.Equal(0, Run(root, ["resources", "verify", "--pack", "resources.zip"], output, error));
        var pack = ScribeResourcePack.Open(root.Resolve("resources.zip"));
        Assert.Equal($"resources verify: entries=2 totalSha256={pack.Manifest.TotalSha256}{Environment.NewLine}", output.ToString());
        Assert.Empty(error.ToString());
        Assert.Equal(2, pack.ReadAll().Count());
    }

    private static TemporaryRoot Prepare()
    {
        var root = new TemporaryRoot();
        TemporaryFileSystem.File.WriteAllText(root.Resolve("global.json"), "{}");
        TemporaryFileSystem.Directory.CreateDirectory(root.Resolve("Blueprint"));
        foreach (var name in new[] { "First", "Second" })
        {
            var path = $"Blueprint/D5/S0/Synthetic/{name}.scribe.cs";
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(root.Resolve(path))!);
            TemporaryFileSystem.File.WriteAllText(root.Resolve(path), $$"""
                using StrataLint.Scribe;
                using static StrataLint.Scribe.DefinitionDsl;
                internal sealed class {{name}} : IScribeDocumentDefinition
                {
                    public DocumentDefinition Create() => DocumentDefinition.Create(
                        ScribeDocument.Create(Header("D5/S0/Synthetic/{{name}}", "Resource fixture"),
                            H("{{name}}"), Blocks(Paragraph(Text("body")))));
                }
                """);
        }
        return root;
    }

    private static int Run(TemporaryRoot root, IReadOnlyList<string> arguments, TextWriter output, TextWriter error) =>
        ScribeCli.Run(Documents, arguments, root.Path, output, error);

    private sealed class FixtureAssembly : Assembly
    {
        public override Type[] GetTypes() => [typeof(FirstDefinition), typeof(SecondDefinition)];
    }

    private sealed class FirstDefinition : IScribeDocumentDefinition
    {
        public DocumentDefinition Create() => ScribeResourcePackTests.Definition("First");
    }

    private sealed class SecondDefinition : IScribeDocumentDefinition
    {
        public DocumentDefinition Create() => ScribeResourcePackTests.Definition("Second");
    }
}
