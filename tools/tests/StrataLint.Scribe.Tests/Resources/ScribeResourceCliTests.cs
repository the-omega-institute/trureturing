using System.Reflection;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json.Nodes;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeResourceCliTests
{
    private static readonly Assembly Documents = new FixtureAssembly();

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

        Assert.Equal(2, Run(root, ["resources", "verify", "--pack", path], TextWriter.Null, error));
        Assert.Contains("EntryDigestMismatch", error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void VerifyRejectsMissingInputWithExitTwo()
    {
        using var root = Prepare();
        var error = new StringWriter();

        Assert.Equal(2, Run(root, ["resources", "verify", "--pack", "missing.zip"], TextWriter.Null, error));
        Assert.NotEmpty(error.ToString());
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("extra")]
    [InlineData("content")]
    public void VerifyReportsDefinitionSetAndCanonicalContentMismatch(string mismatch)
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

        Assert.Equal(1, Run(root, ["resources", "verify", "--pack", path], output, error));
        Assert.Contains("entries=", output.ToString(), StringComparison.Ordinal);
        Assert.Contains("mismatches=1", output.ToString(), StringComparison.Ordinal);
        Assert.NotEmpty(error.ToString());
    }

    [Theory]
    [InlineData("formatting", 1, "Canonical content differs")]
    [InlineData("unknown-tag", 2, "UnknownType")]
    public void VerifyChecksOriginalBytesAndStronglyDecodesDigestValidResources(
        string change, int expectedExit, string expectedReason)
    {
        using var root = Prepare();
        var path = root.Resolve("resources.zip");
        ScribeResourcePack.Write(path, [ScribeResourcePackTests.Definition("First"), ScribeResourcePackTests.Definition("Second")]);
        var entries = ScribeResourcePackTests.ReadZip(path);
        var text = Encoding.UTF8.GetString(entries[0].Bytes);
        entries[0] = (entries[0].Name, Encoding.UTF8.GetBytes(change == "formatting" ? " " + text :
            text.Replace("\"type\":\"ScribeDocument\"", "\"type\":\"Unknown\"", StringComparison.Ordinal)));
        var index = entries.FindIndex(item => item.Name == "manifest.json");
        var manifest = JsonNode.Parse(entries[index].Bytes)!;
        manifest["entries"]![0]!["sha256"] = Convert.ToHexStringLower(SHA256.HashData(entries[0].Bytes));
        manifest["totalSha256"] = Convert.ToHexStringLower(SHA256.HashData(
            Encoding.UTF8.GetBytes(manifest["entries"]!.ToJsonString())));
        entries[index] = ("manifest.json", Encoding.UTF8.GetBytes(manifest.ToJsonString()));
        ScribeResourcePackTests.RewriteZip(path, entries);
        var error = new StringWriter();

        Assert.Equal(expectedExit, Run(root, ["resources", "verify", "--pack", path], TextWriter.Null, error));
        Assert.Contains(expectedReason, error.ToString(), StringComparison.Ordinal);
    }

    [Fact]
    public void PackThenVerifyUsesTheAssemblyDefinitionDiscoveryPath()
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
        Assert.Contains("entries=2 mismatches=0", output.ToString(), StringComparison.Ordinal);
        Assert.Empty(error.ToString());
        Assert.Equal(2, ScribeResourcePack.Open(root.Resolve("resources.zip")).ReadAll().Count());
    }

    private static TemporaryRoot Prepare()
    {
        var root = new TemporaryRoot();
        TemporaryFileSystem.File.WriteAllText(root.Resolve("global.json"), "{}");
        TemporaryFileSystem.Directory.CreateDirectory(root.Resolve("Blueprint"));
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
