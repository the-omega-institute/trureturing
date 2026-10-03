using System.Security.Cryptography;
using System.Text;
using System.Text.Json.Nodes;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeResourceInputContractTests
{
    private const string Pilot = "Golden/Projection/statement-projection-pilot-v1.json";
    private const string Expansion = "Golden/Projection/statement-projection-expansion-v1.json";
    private const string Shared = "Blueprint/D5/S0/Test/Shared.scribe.cs";

    [Theory]
    [InlineData("missing-inputs")]
    [InlineData("null-inputs")]
    [InlineData("duplicate")]
    [InlineData("unsorted")]
    [InlineData("absolute")]
    [InlineData("backslash")]
    [InlineData("parent")]
    [InlineData("digest")]
    [InlineData("extra-field")]
    public void ReaderRejectsMalformedInputs(string variant)
    {
        using var root = Prepare();
        var manifest = Pack(root);
        var entry = manifest["entries"]![0]!;
        var inputs = entry["inputs"]!.AsArray();
        switch (variant)
        {
            case "missing-inputs": entry.AsObject().Remove("inputs"); break;
            case "null-inputs": entry["inputs"] = null; break;
            case "duplicate": inputs.Add(inputs[0]!.DeepClone()); break;
            case "unsorted": (inputs[0], inputs[1]) = (inputs[1]!.DeepClone(), inputs[0]!.DeepClone()); break;
            case "absolute": inputs[0]!["path"] = "/input.cs"; break;
            case "backslash": inputs[0]!["path"] = "Blueprint\\input.cs"; break;
            case "parent": inputs[0]!["path"] = "Blueprint/../input.cs"; break;
            case "digest": inputs[0]!["sha256"] = "invalid"; break;
            case "extra-field": inputs[0]!["extra"] = true; break;
        }
        RewriteManifest(root, manifest);
        Assert.Equal(ScribeResourcePackErrorCode.InvalidManifest,
            Assert.Throws<ScribeResourcePackException>(() => ScribeResourcePack.Open(root.Resolve("resources.zip"))).ReasonCode);
    }

    [Fact]
    public void ReaderRejectsPreviousManifestVersionWithNamedError()
    {
        using var root = Prepare();
        var manifest = Pack(root);
        manifest["version"] = 1;
        foreach (var entry in manifest["entries"]!.AsArray()) entry!.AsObject().Remove("inputs");
        RewriteManifest(root, manifest);
        var exception = Assert.Throws<ScribeResourcePackException>(() => ScribeResourcePack.Open(root.Resolve("resources.zip")));
        Assert.Equal(ScribeResourcePackErrorCode.VersionMismatch, exception.ReasonCode);
    }

    [Fact]
    public void InputTamperingInvalidatesTheTotalDigest()
    {
        using var root = Prepare();
        var manifest = Pack(root);
        manifest["entries"]![0]!["inputs"]![0]!["sha256"] = new string('a', 64);
        RewriteManifest(root, manifest);
        Assert.Equal(ScribeResourcePackErrorCode.TotalDigestMismatch,
            Assert.Throws<ScribeResourcePackException>(() => ScribeResourcePack.Open(root.Resolve("resources.zip"))).ReasonCode);
    }

    [Fact]
    public void MissingProjectionReadIsRecordedOnTheFailedExecution()
    {
        using var root = Prepare();
        TemporaryFileSystem.File.Delete(root.Resolve(Pilot));
        var result = ScribeScriptHost.Execute(root.Path, PathFor("Alpha"));
        Assert.Equal(ScribeScriptFailureCode.CreateFailed, result.Failure?.Code);
        var property = result.GetType().GetProperty("Inputs");
        Assert.NotNull(property);
        var inputs = JsonNode.Parse(System.Text.Json.JsonSerializer.Serialize(property.GetValue(result)))!.AsArray();
        var input = Assert.Single(inputs, item => item!["Path"]!.GetValue<string>() == Pilot);
        Assert.Null(input!["Sha256"]);
        Assert.Contains(inputs, item => item!["Path"]!.GetValue<string>() == PathFor("Alpha"));
    }

    [Fact]
    public void EachExecutionRecordsSourcesAndProjectionBytesOnce()
    {
        using var root = Prepare();
        var manifest = Pack(root);
        Assert.Equal(2, manifest["version"]!.GetValue<int>());
        Assert.Equal(2, manifest["resourceVersion"]!.GetValue<int>());
        Assert.Equal(1, manifest["scriptVersion"]!.GetValue<int>());
        foreach (var name in new[] { "Alpha", "Beta" })
        {
            var inputs = Entry(manifest, name)["inputs"]!.AsArray();
            Assert.Equal(new[] { PathFor(name), Shared, Expansion, Pilot },
                inputs.Select(item => item!["path"]!.GetValue<string>()));
            foreach (var input in inputs)
            {
                var path = input!["path"]!.GetValue<string>();
                Assert.Equal(Digest(File.ReadAllBytes(root.Resolve(path))), input["sha256"]!.GetValue<string>());
            }
        }
        Assert.Single(Entry(manifest, "Shared")["inputs"]!.AsArray());
        Assert.Equal(0, Compare(root, out _, out _));
    }

    [Fact]
    public void EncodingIsDeterministicAndInputChangesAlterIdentityWithoutChangingResourceBytes()
    {
        using var root = Prepare();
        var first = Pack(root);
        var bytes = File.ReadAllBytes(root.Resolve("resources.zip"));
        Pack(root);
        Assert.Equal(bytes, File.ReadAllBytes(root.Resolve("resources.zip")));
        TemporaryFileSystem.File.AppendAllText(root.Resolve(Shared), "\n");
        var second = Pack(root);
        Assert.NotEqual(first["totalSha256"]!.GetValue<string>(), second["totalSha256"]!.GetValue<string>());
        Assert.Equal(Entry(first, "Alpha")["sha256"]!.GetValue<string>(), Entry(second, "Alpha")["sha256"]!.GetValue<string>());
    }

    [Theory]
    [InlineData("entry")]
    [InlineData("shared")]
    [InlineData("projection")]
    [InlineData("create-missing")]
    [InlineData("new-definition")]
    [InlineData("delete-definition")]
    public void CompareNamesTheDefinitionAndFirstChangedInput(string change)
    {
        using var root = Prepare();
        var manifest = Pack(root);
        if (change == "create-missing")
        {
            TemporaryFileSystem.File.Delete(root.Resolve(Pilot));
            foreach (var name in new[] { "Alpha", "Beta" }) Input(manifest, name, Pilot)["sha256"] = null;
            manifest["totalSha256"] = Digest(Encoding.UTF8.GetBytes(manifest["entries"]!.ToJsonString()));
            RewriteManifest(root, manifest);
        }
        var input = change switch
        {
            "entry" or "delete-definition" => PathFor("Alpha"),
            "shared" => Shared,
            "projection" or "create-missing" => Pilot,
            _ => PathFor("Gamma"),
        };
        if (change == "delete-definition") TemporaryFileSystem.File.Delete(root.Resolve(input));
        else if (change == "new-definition") WriteDefinition(root, "Gamma", read: false);
        else TemporaryFileSystem.File.AppendAllText(root.Resolve(input), "\n");
        Assert.Equal(1, Compare(root, out var output, out var error));
        Assert.Contains(change == "new-definition" ? PathFor("Gamma") : PathFor("Alpha"), error, StringComparison.Ordinal);
        Assert.Contains(input, error, StringComparison.Ordinal);
        Assert.Contains("recorded=", error, StringComparison.Ordinal);
        Assert.Contains("current=", error, StringComparison.Ordinal);
        Assert.Contains("entries=3", output, StringComparison.Ordinal);
        Assert.Contains("consistent=", output, StringComparison.Ordinal);
        Assert.Contains("inputsChanged=", output, StringComparison.Ordinal);
        Assert.Contains("packOnly=", output, StringComparison.Ordinal);
        Assert.Contains("diskOnly=", output, StringComparison.Ordinal);
    }

    [Fact]
    public void CompareIgnoresUnreadFilesAndNeverLoadsTheDocumentsAssembly()
    {
        using var root = Prepare();
        Pack(root);
        TemporaryFileSystem.File.WriteAllText(root.Resolve("Golden/unread.txt"), "data");
        var output = new StringWriter();
        var error = new StringWriter();
        Assert.Equal(0, ScribeCli.Run(() => throw new InvalidOperationException("assembly requested"),
            ["resources", "compare", "--pack", "resources.zip"], root.Path, output, error));
        Assert.Equal("resources compare: entries=3 consistent=3 inputsChanged=0 packOnly=0 diskOnly=0" + Environment.NewLine, output.ToString());
        Assert.Empty(error.ToString());
    }

    [Theory]
    [InlineData("resources", "compare")]
    [InlineData("resources", "compare", "--out", "resources.zip")]
    [InlineData("resources", "compare", "--pack", "")]
    [InlineData("resources", "compare", "--pack", "missing.zip")]
    [InlineData("resources", "compare", "--pack", "resources.zip", "extra")]
    public void CompareInputErrorsReturnTwo(params string[] arguments)
    {
        using var root = Prepare();
        Assert.Equal(2, ScribeCli.Run(typeof(ScribeResourcePack).Assembly, arguments, root.Path, TextWriter.Null, new StringWriter()));
    }

    private static TemporaryRoot Prepare()
    {
        var root = new TemporaryRoot();
        TemporaryFileSystem.File.WriteAllText(root.Resolve("global.json"), "{}");
        Fixture(root, Pilot, "pilot");
        Fixture(root, Expansion, "expansion");
        WriteDefinition(root, "Shared", read: false);
        WriteDefinition(root, "Alpha", read: true);
        WriteDefinition(root, "Beta", read: true);
        return root;
    }

    private static void Fixture(TemporaryRoot root, string path, string name) =>
        TemporaryFileSystem.File.WriteAllText(root.Resolve(path), new JsonObject
        {
            ["schema"] = "statement-projection-" + name + "-fixture-v1",
            ["declarations"] = new JsonArray(),
        }.ToJsonString());

    private static void WriteDefinition(TemporaryRoot root, string name, bool read)
    {
        var probe = read ? """
            for (var i = 0; i < 2; i++)
            {
                _ = Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create("D5/S0/Test/Alpha.claim"),
                        H("Claim"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("body"))), DescribeRole.Theorem);
            }
            """ : "";
        TemporaryFileSystem.File.WriteAllText(root.Resolve(PathFor(name)), $$"""
            using StrataLint.Scribe;
            using static StrataLint.Scribe.DefinitionDsl;
            {{(read ? "[ScribeSharedSource(\"" + Shared + "\")]" : "")}}
            internal sealed class {{name}} : IScribeDocumentDefinition
            {
                public DocumentDefinition Create()
                {
                    {{probe}}
                    return DocumentDefinition.Create(ScribeNode.Create("digest", H("title"), Blocks(Paragraph(Text("content")))));
                }
            }
            """);
    }

    private static JsonObject Pack(TemporaryRoot root)
    {
        var result = ScribeResourceScriptPacker.Write(root.Path, root.Resolve("resources.zip"));
        Assert.Empty(result.Failures);
        return JsonNode.Parse(ScribeResourcePackTests.ReadZip(root.Resolve("resources.zip"))
            .Single(item => item.Name == "manifest.json").Bytes)!.AsObject();
    }

    private static JsonNode Entry(JsonObject manifest, string name) => manifest["entries"]!.AsArray()
        .Single(item => item!["gid"]!.GetValue<string>() == "D5/S0/Test/" + name)!;
    private static JsonNode Input(JsonObject manifest, string name, string path) => Entry(manifest, name)["inputs"]!.AsArray()
        .Single(item => item!["path"]!.GetValue<string>() == path)!;
    private static string PathFor(string name) => "Blueprint/D5/S0/Test/" + name + ".scribe.cs";
    private static string Digest(byte[] bytes) => Convert.ToHexStringLower(SHA256.HashData(bytes));
    private static int Compare(TemporaryRoot root, out string output, out string error)
    {
        var writer = new StringWriter();
        var errors = new StringWriter();
        var exit = ScribeCli.Run(typeof(ScribeResourcePack).Assembly,
            ["resources", "compare", "--pack", "resources.zip"], root.Path, writer, errors);
        output = writer.ToString();
        error = errors.ToString();
        return exit;
    }
    private static void RewriteManifest(TemporaryRoot root, JsonObject manifest)
    {
        var path = root.Resolve("resources.zip");
        var entries = ScribeResourcePackTests.ReadZip(path);
        entries[entries.FindIndex(item => item.Name == "manifest.json")] = ("manifest.json", Encoding.UTF8.GetBytes(manifest.ToJsonString()));
        ScribeResourcePackTests.RewriteZip(path, entries);
    }
}
