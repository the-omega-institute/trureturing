using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class TruthExportJsonTests
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private const string Commit = "1111111111111111111111111111111111111111";
    private const string Tree = "2222222222222222222222222222222222222222";

    [Fact]
    public void WriteIsDeterministicCanonicalUtf8AndProjectsEveryFrozenField()
    {
        var nodes = ImmutableArray.Create(
            Material(
                "D5/S0/Carrier/Beta.lean",
                axioms: new[] { "propext", "Classical.choice" },
                declarations: new[] { ("nk-beta", "theorem", "sha256:beta1") }),
            Material(
                "D5/S0/Carrier/Alpha.lean",
                axioms: new[] { "Quot.sound" },
                declarations: new[]
                {
                    ("nk-two", "theorem", "sha256:a2"),
                    ("nk-one", "definition", "sha256:a1"),
                }));
        var model = TruthExportModel.Create(nodes, Commit, Tree);

        var first = TruthExportJsonWriter.Write(model);
        var second = TruthExportJsonWriter.Write(model);

        Assert.True(first.AsSpan().SequenceEqual(second.AsSpan()));
        Assert.False(first.AsSpan().StartsWith(new byte[] { 0xEF, 0xBB, 0xBF }));
        var text = StrictUtf8.GetString(first.AsSpan());
        Assert.DoesNotContain('\r', text);
        Assert.EndsWith("\n", text, StringComparison.Ordinal);
        Assert.False(text.EndsWith("\n\n", StringComparison.Ordinal));
        Assert.Equal(TruthExportModel.SchemaName, model.Schema);
        Assert.Equal(TruthExportModel.CanonicalDialect, model.Dialect);
        Assert.Equal("stratalint.truth-export.v1", model.Dialect);
        Assert.Equal("TruthExportCommand", model.Producer);
        Assert.Equal(Commit, model.SourceCommit);
        Assert.Equal(Tree, model.SourceTree);

        // Nodes sort by (repo_path, frozen_node_id); Alpha precedes Beta.
        Assert.Equal(
            new[] { "D5/S0/Carrier/Alpha.lean", "D5/S0/Carrier/Beta.lean" },
            model.Nodes.Select(static node => node.RepoPath));
        // node_axiom_closure is the node-level closure, sorted.
        Assert.Equal(new[] { "Classical.choice", "propext" }, model.Nodes[1].NodeAxiomClosure);
        // Declarations keep their own identity and sort by (name_key, statement_id).
        Assert.Equal(
            new[] { "nk-one", "nk-two" },
            model.Nodes[0].Declarations.Select(static declaration => declaration.DeclarationNameKey));
        Assert.Equal("sha256:a1", model.Nodes[0].Declarations[0].StatementId);
        Assert.Equal("definition", model.Nodes[0].Declarations[0].Kind);
    }

    [Fact]
    public void TwentyInputPermutationsProduceOneByteSequence()
    {
        var nodes = Enumerable.Range(0, 8)
            .Select(index => Material(
                $"D5/S0/Carrier/M{index}.lean",
                axioms: new[] { $"axiom{index}", "propext" },
                declarations: new[] { ($"nk-{index}", "theorem", $"sha256:{index}") }))
            .ToArray();
        var outputs = new HashSet<string>(StringComparer.Ordinal);
        for (var seed = 0; seed < 20; seed++)
        {
            var random = new Random(seed);
            var shuffled = nodes.OrderBy(_ => random.Next()).ToImmutableArray();
            outputs.Add(Convert.ToBase64String(
                TruthExportJsonWriter.Write(TruthExportModel.Create(shuffled, Commit, Tree)).AsSpan()));
        }

        Assert.Single(outputs);
    }

    [Fact]
    public void StrictReaderRoundTripsEveryCapabilityField()
    {
        var nodes = ImmutableArray.Create(
            Material("D5/S0/Carrier/A.lean", new[] { "propext" }, new[] { ("nk-a", "theorem", "sha256:a") }),
            Material("D5/S0/Carrier/B.lean", Array.Empty<string>(), new[] { ("nk-b", "definition", "sha256:b") }));
        var expected = TruthExportModel.Create(nodes, Commit, Tree);

        var bytes = TruthExportJsonWriter.Write(expected);
        var actual = TruthExportJsonReader.Read(bytes.AsSpan());

        Assert.Equal(expected.Schema, actual.Schema);
        Assert.Equal(expected.SchemaVersion, actual.SchemaVersion);
        Assert.Equal(expected.Dialect, actual.Dialect);
        Assert.Equal(expected.SourceCommit, actual.SourceCommit);
        Assert.Equal(expected.SourceTree, actual.SourceTree);
        Assert.Equal(expected.Producer, actual.Producer);
        Assert.Equal(expected.Nodes.Length, actual.Nodes.Length);
        for (var index = 0; index < expected.Nodes.Length; index++)
        {
            // ImmutableArray fields make TruthExportNode's record equality reference-based, so the
            // fields are compared by value (Assert.Equal enumerates the arrays element-wise).
            Assert.Equal(expected.Nodes[index].RepoPath, actual.Nodes[index].RepoPath);
            Assert.Equal(expected.Nodes[index].FrozenNodeId, actual.Nodes[index].FrozenNodeId);
            Assert.True(expected.Nodes[index].NodeAxiomClosure.SequenceEqual(actual.Nodes[index].NodeAxiomClosure));
            Assert.True(expected.Nodes[index].Declarations.SequenceEqual(actual.Nodes[index].Declarations));
        }

        Assert.True(TruthExportJsonWriter.Write(actual).AsSpan().SequenceEqual(bytes.AsSpan()));
    }

    [Fact]
    public void EmptyActiveSetRoundTrips()
    {
        var model = TruthExportModel.Create(ImmutableArray<FrozenNodeMaterial>.Empty, Commit, Tree);
        var bytes = TruthExportJsonWriter.Write(model);

        Assert.Empty(TruthExportJsonReader.Read(bytes.AsSpan()).Nodes);
    }

    [Fact]
    public void StrictReaderRejectsUnsortedNodes()
    {
        // Hand-craft bytes whose nodes descend by repo_path; the writer would never emit this order,
        // so only the reader's strict-order guard catches it.
        var descending =
            "{\"dialect\":\"stratalint.truth-export.v1\",\"nodes\":["
            + "{\"declarations\":[{\"declaration_name_key\":\"nk-b\",\"kind\":\"theorem\",\"statement_id\":\"sha256:b\"}],\"frozen_node_id\":\"sha256:fb\",\"node_axiom_closure\":[],\"repo_path\":\"D5/S0/Carrier/B.lean\"},"
            + "{\"declarations\":[{\"declaration_name_key\":\"nk-a\",\"kind\":\"theorem\",\"statement_id\":\"sha256:a\"}],\"frozen_node_id\":\"sha256:fa\",\"node_axiom_closure\":[],\"repo_path\":\"D5/S0/Carrier/A.lean\"}"
            + "],\"producer\":\"TruthExportCommand\",\"schema\":\"stratalint.truth-export\",\"schema_version\":1,"
            + "\"source_commit\":\"" + Commit + "\",\"source_tree\":\"" + Tree + "\"}\n";

        Assert.Throws<FormatException>(() =>
            TruthExportJsonReader.Read(Encoding.UTF8.GetBytes(descending)));
    }

    [Theory]
    [InlineData("{}\n")]
    [InlineData("{\"schema\":\"stratalint.truth-export\",\"schema_version\":1,\"dialect\":\"stratalint.truth-export.v1\",\"source_commit\":\"c\",\"source_tree\":\"t\",\"producer\":\"TruthExportCommand\",\"nodes\":[],\"extra\":true}\n")]
    [InlineData("{\"schema\":\"wrong\",\"schema_version\":1,\"dialect\":\"stratalint.truth-export.v1\",\"source_commit\":\"c\",\"source_tree\":\"t\",\"producer\":\"TruthExportCommand\",\"nodes\":[]}\n")]
    [InlineData("{\"schema\":\"stratalint.truth-export\",\"schema_version\":1,\"dialect\":\"stratalint.truth-export.v2\",\"source_commit\":\"c\",\"source_tree\":\"t\",\"producer\":\"TruthExportCommand\",\"nodes\":[]}\n")]
    [InlineData("{\"schema\":\"stratalint.truth-export\",\"schema_version\":1,\"dialect\":\"stratalint.truth-export.v1\",\"source_commit\":\"c\",\"source_tree\":\"t\",\"producer\":\"Impostor\",\"nodes\":[]}\n")]
    public void StrictReaderRejectsMalformedOrUnknownFields(string json) =>
        Assert.Throws<FormatException>(() => TruthExportJsonReader.Read(Encoding.UTF8.GetBytes(json)));

    [Fact]
    public void TheProjectionIsDeclaredInTheGeneratedArtifactInventory()
    {
        // FileMapPolicy cross-checks this inventory against Meta/FILEMAP.toml, so an artifact that
        // ships without an entry is an ungoverned generated file.
        var artifact = Assert.Single(
            GeneratedArtifactInventory.All.Where(static item => item.Path == TruthExportModel.RelativePath));

        Assert.Equal(TruthExportModel.ProducerName, artifact.Producer);
        Assert.Equal("A-TRUTHEXPORT", artifact.ArtifactId);
    }

    private static FrozenNodeMaterial Material(
        string repoPath,
        string[] axioms,
        (string NameKey, string Kind, string StatementId)[] declarations) =>
        new(
            RepoPath.CreateKnown(repoPath),
            declarations
                .Select(static declaration => new FrozenDeclarationStatement(
                    declaration.NameKey,
                    declaration.Kind,
                    StatementId.Create(declaration.StatementId)))
                .ToImmutableArray(),
            StatementId.Create(Sha("stmt:" + repoPath)),
            WitnessId.Create(Sha("wit:" + repoPath)),
            FrozenNodeId.Create(Sha("frozen:" + repoPath)),
            ImmutableArray<FrozenNodeId>.Empty,
            axioms.ToImmutableArray(),
            new FrozenModuleAttestation(RepoPath.CreateKnown(repoPath), "git-sha1:" + new string('a', 40)));

    private static string Sha(string text) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(text)));
}
