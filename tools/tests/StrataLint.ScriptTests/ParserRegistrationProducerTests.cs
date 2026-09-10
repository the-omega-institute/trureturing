using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Current source compiler")]
public sealed class ParserRegistrationProducerTests(SourceCompilerFixture compiler)
{
    [Theory]
    [InlineData(false, "current")]
    [InlineData(true, "current")]
    [InlineData(false, "source")]
    [InlineData(true, "source")]
    public void CommandInRegistryMatchesCompiler(bool wrapped, string mode)
    {
        var output = Run("witness", wrapped.ToString(), mode);
        var source = output.GetProperty("source").GetString()!;
        var (snapshot, path, input) = Load(source, output.GetProperty("result"));
        var context = input.GetFile(snapshot, path, "current");
        var offset = Encoding.UTF8.GetByteCount(source[..source.LastIndexOf("example", StringComparison.Ordinal)]);
        var actual = context.EqualityAt(offset);
        Console.WriteLine("COMMAND_IN_LOADER " + JsonSerializer.Serialize(new {
            wrapped, mode, source_sha256 = LeanSourceContextInput.SourceHash(snapshot.Files[path]),
            offset, expected_equality = true, actual_equality = actual, malformed_rows = input.MalformedRows.Count,
        }));
        Assert.Empty(input.MalformedRows);
        Assert.True(actual, "Compiler registry retains the global token after the wrapper and namespace.");
        Assert.Empty(NativeDecideSourceRule.Inspect(snapshot, path, input));
    }

    [Theory]
    [InlineData("sepBy")]
    [InlineData("sepBy1")]
    public void SeparatorParserTokensMatchCompiler(string parser)
        => Run("separator", parser);

    [Theory]
    [InlineData("", false)]
    [InlineData("local ", false)]
    [InlineData("scoped ", false)]
    [InlineData("", true)]
    [InlineData("local ", true)]
    [InlineData("scoped ", true)]
    public void CommandInLocalityMatchesCompiler(string locality, bool secondCommand)
        => Run("locality", locality, secondCommand.ToString());

    [Fact]
    public void CommandInProjectionDoesNotExecuteProtectedBodies()
        => Run("nonexecution");

    [Fact]
    public void CommandInUnknownEffectIsLocated()
        => Run("unknown");

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CommandInDeclarationReachesSourceExtractor(bool wrapped)
    {
        var output = Run("extractor", wrapped.ToString());
        var source = output.GetProperty("source").GetString()!;
        var (snapshot, path, input) = Load(source, output.GetProperty("result"));
        var material = LeanSourceCatalog.Parse(snapshot, input).ExtractPropositionSource(path,
            [new FrozenDeclarationStatement("ns(ns(n0,12:Registration),4:kept)", "theorem",
                StatementId.Create(new string('a', 64)))]);
        var extracted = Encoding.UTF8.GetString(material.AsSpan());
        Assert.Contains("kept", extracted, StringComparison.Ordinal);
        if (wrapped) Assert.Contains("\u001fin\u001f", extracted, StringComparison.Ordinal);
        Assert.Empty(input.MalformedRows);
    }

    private JsonElement Run(params string[] arguments)
    {
        var run = TestProcessRunner.Run("python3", ["-c", ParserRegistrationContractScript.Source,
            compiler.Root, .. arguments], compiler.Root, BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
        var stdout = Encoding.UTF8.GetString(run.StandardOutput);
        Console.WriteLine(stdout);
        Assert.True(run.ExitCode == 0, stdout + Encoding.UTF8.GetString(run.StandardError));
        var result = stdout.Split('\n').Single(line => line.StartsWith("PARSER_REGISTRATION_RESULT ", StringComparison.Ordinal));
        using var document = JsonDocument.Parse(result["PARSER_REGISTRATION_RESULT ".Length..]);
        return document.RootElement.Clone();
    }

    private static (RepositorySnapshot, RepoPath, LeanSourceContextInput) Load(string source, JsonElement result)
    {
        var path = RepoPath.CreateKnown("D5/Query.lean");
        var file = new RepositoryFile(path, Encoding.UTF8.GetBytes(source).ToImmutableArray(), source);
        var snapshot = RepositorySnapshot.Create(ImmutableDictionary<RepoPath, RepositoryFile>.Empty.Add(path, file));
        var row = new JsonObject {
            ["side"] = "current", ["path"] = path.Value,
            ["sourceSha256"] = LeanSourceContextInput.SourceHash(file),
            ["producerSha256"] = LeanSourceContextInput.ProducerHash(snapshot),
            ["configurationSha256"] = LeanSourceContextInput.ConfigurationHash(snapshot),
            ["graphSha256"] = LeanSourceContextInput.GraphHash(snapshot, path),
            ["interfaces"] = new JsonArray(), ["result"] = JsonNode.Parse(result.GetRawText()),
        };
        var bundle = new JsonObject { ["schema"] = LeanSourceContextInput.Schema, ["files"] = new JsonArray(row) };
        return (snapshot, path, LeanSourceContextInput.Load(Encoding.UTF8.GetBytes(bundle.ToJsonString()), snapshot, snapshot));
    }
}
