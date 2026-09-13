using System.Collections.Immutable;
using System.Text;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class LeanSourceContextInputTests
{
    [Theory]
    [InlineData("source")]
    [InlineData("path")]
    [InlineData("side")]
    [InlineData("producer")]
    [InlineData("configuration")]
    [InlineData("graph")]
    [InlineData("duplicate")]
    [InlineData("utf8")]
    [InlineData("overlap")]
    [InlineData("missing-equality")]
    [InlineData("imports")]
    [InlineData("module")]
    [InlineData("interface")]
    [InlineData("missing-commands")]
    [InlineData("command-gap")]
    public void DemandedInputRejectsStaleOrMalformedBindings(string mutation)
    {
        var source = "import Init\n-- α\nexample : ')' =')' := by decide\n";
        var file = TextFile(PathFor("A"), source);
        var snapshot = Snapshot([file]);
        var row = Row(file, snapshot);
        var rows = new JsonArray(row);
        switch (mutation)
        {
            case "source": row["sourceSha256"] = new string('0', 64); break;
            case "path": row["path"] = PathFor("B"); break;
            case "side": row["side"] = "protected"; break;
            case "producer": row["producerSha256"] = new string('0', 64); break;
            case "configuration": row["configurationSha256"] = new string('0', 64); break;
            case "graph": row["graphSha256"] = new string('0', 64); break;
            case "duplicate": rows.Add(row.DeepClone()); break;
            case "utf8": row["result"]!["commands"]![0]!["start"] = 16; break;
            case "overlap": row["result"]!["commands"]!.AsArray().Add(
                row["result"]!["commands"]![0]!.DeepClone()); break;
            case "missing-equality": row["result"]!["commands"]![0]!.AsObject().Remove("equality"); break;
            case "imports": row["result"]!["imports"] = new JsonArray(); break;
            case "module": row["result"]!["isModule"] = true; break;
            case "interface": row["interfaces"]!.AsArray().Add(new JsonObject { ["path"] = "D5/Absent.lean", ["sourceSha256"] = "stale" }); break;
            case "missing-commands": row["result"]!["commands"] = new JsonArray(); break;
            case "command-gap": row["result"]!["commands"]![0]!["start"] =
                row["result"]!["commands"]![0]!["start"]!.GetValue<int>() + 8; break;
        }
        var input = LeanSourceContextInput.Load(Encoding.UTF8.GetBytes(
            new JsonObject { ["schema"] = LeanSourceContextInput.Schema, ["files"] = rows }.ToJsonString()),
            snapshot, Snapshot([]));
        Assert.Throws<LeanSourceExtractionException>(() => input.GetFile(snapshot, file.Path, "current"));
    }

    [Fact]
    public void MalformedUnusedBundleIsLazyButDemandedBundleFails()
    {
        var file = TextFile(PathFor("A"), "import Init\nexample : ')' =')' := by decide\n");
        var snapshot = Snapshot([file]);
        var input = LeanSourceContextInput.Load(Encoding.UTF8.GetBytes("{broken"), snapshot, Snapshot([]));
        Assert.Empty(input.MalformedRows);
        Assert.Throws<LeanSourceExtractionException>(() => input.GetFile(snapshot, file.Path, "current"));
        Assert.NotEmpty(input.MalformedRows);
    }

    [Fact]
    public void ExplicitFalseRemainsDifferentFromMissingContext()
    {
        var file = TextFile(PathFor("A"), "import Init\nexample : ')' =')' := by decide\n");
        var snapshot = Snapshot([file]);
        var row = Row(file, snapshot);
        var input = LeanSourceContextInput.Load(Encoding.UTF8.GetBytes(
            new JsonObject { ["schema"] = LeanSourceContextInput.Schema,
                ["files"] = new JsonArray(row) }.ToJsonString()), snapshot, Snapshot([]));
        Assert.False(input.GetFile(snapshot, file.Path, "current").EqualityAt(30));
        Assert.Throws<LeanSourceExtractionException>(() =>
            LeanSourceContextInput.Empty.GetFile(snapshot, file.Path, "current"));
    }

    [Theory]
    [InlineData("import D5.S0.Carrier.Helper\nexample : ')' =')' := by decide\n")]
    [InlineData("module\npublic import D5.S0.Carrier.Helper\nexample : ')' =')' := by decide\n")]
    [InlineData("module\nmeta import D5.S0.Carrier.Helper\nexample : ')' =')' := by decide\n")]
    [InlineData("module\nimport all D5.S0.Carrier.Helper\nexample : ')' =')' := by decide\n")]
    public void ImportAdjacencyIgnoresNotationSensitiveProofBody(string source)
    {
        var file = TextFile(PathFor("A"), source);
        Assert.Equal("D5.S0.Carrier.Helper", Assert.Single(LeanSourceCatalog.ParseFileImports(file)));
    }

    private static RepositoryFile TextFile(string path, string source) => new(
        RepoPath.TryCreate(path, out var parsed) ? parsed : throw new ArgumentException(path),
        ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(source)), source);
    private static RepositorySnapshot Snapshot(IEnumerable<RepositoryFile> files) =>
        RepositorySnapshot.Create(files.ToImmutableDictionary(file => file.Path));

    private static JsonObject Row(RepositoryFile file, RepositorySnapshot snapshot)
    {
        var start = Encoding.UTF8.GetByteCount(file.Text[..file.Text.IndexOf("example", StringComparison.Ordinal)]);
        return new JsonObject
        {
            ["side"] = "current", ["path"] = file.Path.Value,
            ["sourceSha256"] = LeanSourceContextInput.SourceHash(file),
            ["producerSha256"] = LeanSourceContextInput.ProducerHash(snapshot),
            ["configurationSha256"] = LeanSourceContextInput.ConfigurationHash(snapshot),
            ["graphSha256"] = LeanSourceContextInput.GraphHash(snapshot, file.Path),
            ["interfaces"] = new JsonArray(),
            ["result"] = new JsonObject
            {
                ["isModule"] = false,
                ["imports"] = System.Text.Json.JsonSerializer.SerializeToNode(LeanSourceHeader.Read(file.Text).Imports.Select(i =>
                    new { module = i.Module, importAll = i.ImportAll, isExported = i.IsExported, isMeta = i.IsMeta })),
                ["headerEnd"] = start, ["initialEquality"] = false, ["error"] = null,
                ["commands"] = new JsonArray(new JsonObject
                {
                    ["start"] = start, ["end"] = file.RawBytes.Length - 1,
                    ["kind"] = "Lean.Parser.Command.example", ["namespace"] = "",
                    ["equality"] = false, ["children"] = new JsonArray(),
                }),
            },
        };
    }
}
