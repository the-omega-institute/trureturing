using System;
using System.Collections.Immutable;
using System.Linq;
using System.Text;
using Trureturing.Truth;
using Xunit;

namespace StrataLint.Tests;

public sealed class TruthExportJsonTests
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private const string Commit = "1111111111111111111111111111111111111111";
    private const string Tree = "2222222222222222222222222222222222222222";
    private const string LeanReportDigest =
        "sha256:3333333333333333333333333333333333333333333333333333333333333333";

    // Build a plain wire node directly. Trureturing.Truth owns the plain model + canonical reader/writer;
    // the Engine-dependent FrozenNodeMaterial -> plain projection stays in Scribe/base, so these tests
    // never touch StrataLint.Engine.
    private static TruthExportNode Node(
        string repoPath,
        string frozenId,
        string[] axioms,
        (string NameKey, string Kind, string StatementId)[] declarations,
        string[] prerequisites) =>
        new(
            repoPath,
            frozenId,
            axioms.ToImmutableArray(),
            declarations
                .Select(static declaration => new TruthExportDeclaration(
                    declaration.NameKey, declaration.Kind, declaration.StatementId))
                .ToImmutableArray(),
            prerequisites.ToImmutableArray());

    [Fact]
    public void CreateCanonicalizesAndWriteIsDeterministicUtf8()
    {
        var nodes = ImmutableArray.Create(
            Node(
                "D5/S0/Carrier/Beta.lean", "sha256:fb",
                axioms: new[] { "propext", "Classical.choice" },
                declarations: new[] { ("nk-beta", "theorem", "sha256:beta1") },
                prerequisites: Array.Empty<string>()),
            Node(
                "D5/S0/Carrier/Alpha.lean", "sha256:fa",
                axioms: new[] { "Quot.sound" },
                declarations: new[]
                {
                    ("nk-two", "theorem", "sha256:a2"),
                    ("nk-one", "definition", "sha256:a1"),
                },
                prerequisites: Array.Empty<string>()));
        var model = TruthExportModel.Create(nodes, Commit, Tree, LeanReportDigest);

        var first = TruthExportJsonWriter.Write(model);
        var second = TruthExportJsonWriter.Write(model);

        Assert.True(first.AsSpan().SequenceEqual(second.AsSpan()));
        Assert.False(first.AsSpan().StartsWith(new byte[] { 0xEF, 0xBB, 0xBF }));
        var text = StrictUtf8.GetString(first.AsSpan());
        Assert.DoesNotContain('\r', text);
        Assert.EndsWith("\n", text, StringComparison.Ordinal);
        Assert.False(text.EndsWith("\n\n", StringComparison.Ordinal));
        Assert.Equal("stratalint.truth-export", model.Schema);
        Assert.Equal("stratalint.truth-export.v1", model.Dialect);
        Assert.Equal("TruthExportCommand", model.Producer);
        Assert.Equal(Commit, model.SourceCommit);
        Assert.Equal(Tree, model.SourceTree);
        Assert.Equal(LeanReportDigest, model.LeanReportDigest);

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
    public void CreateProducesOneByteSequenceRegardlessOfInputOrder()
    {
        var nodes = Enumerable.Range(0, 8)
            .Select(index => Node(
                $"D5/S0/Carrier/M{index}.lean", $"sha256:f{index}",
                axioms: new[] { $"axiom{index}", "propext" },
                declarations: new[] { ($"nk-{index}", "theorem", $"sha256:{index}") },
                prerequisites: Array.Empty<string>()))
            .ToArray();
        var outputs = new HashSet<string>(StringComparer.Ordinal);
        for (var seed = 0; seed < 20; seed++)
        {
            var random = new Random(seed);
            var shuffled = nodes.OrderBy(_ => random.Next()).ToImmutableArray();
            outputs.Add(Convert.ToBase64String(
                TruthExportJsonWriter.Write(
                    TruthExportModel.Create(shuffled, Commit, Tree, LeanReportDigest)).AsSpan()));
        }

        Assert.Single(outputs);
    }

    [Fact]
    public void StrictReaderRoundTripsEveryField()
    {
        var nodes = ImmutableArray.Create(
            Node(
                "D5/S0/Carrier/A.lean", "sha256:fa", new[] { "propext" },
                new[] { ("nk-a", "theorem", "sha256:a") }, Array.Empty<string>()),
            Node(
                "D5/S0/Carrier/B.lean", "sha256:fb", Array.Empty<string>(),
                new[] { ("nk-b", "definition", "sha256:b") }, Array.Empty<string>()));
        var expected = TruthExportModel.Create(nodes, Commit, Tree, LeanReportDigest);

        var bytes = TruthExportJsonWriter.Write(expected);
        var actual = TruthExportJsonReader.Read(bytes.AsSpan());

        Assert.Equal(expected.Schema, actual.Schema);
        Assert.Equal(expected.SchemaVersion, actual.SchemaVersion);
        Assert.Equal(expected.Dialect, actual.Dialect);
        Assert.Equal(expected.SourceCommit, actual.SourceCommit);
        Assert.Equal(expected.SourceTree, actual.SourceTree);
        Assert.Equal(expected.LeanReportDigest, actual.LeanReportDigest);
        Assert.Equal(expected.Producer, actual.Producer);
        Assert.Equal(expected.Nodes.Length, actual.Nodes.Length);
        for (var index = 0; index < expected.Nodes.Length; index++)
        {
            Assert.Equal(expected.Nodes[index].RepoPath, actual.Nodes[index].RepoPath);
            Assert.Equal(expected.Nodes[index].FrozenNodeId, actual.Nodes[index].FrozenNodeId);
            Assert.True(expected.Nodes[index].NodeAxiomClosure.SequenceEqual(actual.Nodes[index].NodeAxiomClosure));
            Assert.True(expected.Nodes[index].Declarations.SequenceEqual(actual.Nodes[index].Declarations));
            Assert.True(expected.Nodes[index].PrerequisiteFrozenNodeIds.SequenceEqual(
                actual.Nodes[index].PrerequisiteFrozenNodeIds));
        }

        Assert.True(TruthExportJsonWriter.Write(actual).AsSpan().SequenceEqual(bytes.AsSpan()));
    }

    [Fact]
    public void PrerequisitesRoundTripThroughWriteAndRead()
    {
        var model = TruthExportModel.Create(
            ImmutableArray.Create(Node(
                "D5/S0/Carrier/A.lean",
                "sha256:fa",
                new[] { "propext" },
                new[] { ("nk-a", "theorem", "sha256:a") },
                new[] { "sha256:prerequisite-b", "sha256:prerequisite-a" })),
            Commit,
            Tree,
            LeanReportDigest);

        var actual = TruthExportJsonReader.Read(TruthExportJsonWriter.Write(model).AsSpan());

        Assert.Equal(
            new[] { "sha256:prerequisite-a", "sha256:prerequisite-b" },
            Assert.Single(actual.Nodes).PrerequisiteFrozenNodeIds);
    }

    [Fact]
    public void EmptyNodeSetRoundTrips()
    {
        var model = TruthExportModel.Create(
            ImmutableArray<TruthExportNode>.Empty,
            Commit,
            Tree,
            LeanReportDigest);
        var bytes = TruthExportJsonWriter.Write(model);

        Assert.Empty(TruthExportJsonReader.Read(bytes.AsSpan()).Nodes);
    }

    [Fact]
    public void StrictReaderRejectsUnsortedNodes()
    {
        // Hand-craft bytes whose nodes descend by repo_path; the writer would never emit this order,
        // so only the reader's strict-order guard catches it.
        var descending =
            "{\"dialect\":\"stratalint.truth-export.v1\",\"lean_report_digest\":\"" + LeanReportDigest + "\",\"nodes\":["
            + "{\"declarations\":[{\"declaration_name_key\":\"nk-b\",\"kind\":\"theorem\",\"statement_id\":\"sha256:b\"}],\"frozen_node_id\":\"sha256:fb\",\"node_axiom_closure\":[],\"prerequisite_frozen_node_ids\":[],\"repo_path\":\"D5/S0/Carrier/B.lean\"},"
            + "{\"declarations\":[{\"declaration_name_key\":\"nk-a\",\"kind\":\"theorem\",\"statement_id\":\"sha256:a\"}],\"frozen_node_id\":\"sha256:fa\",\"node_axiom_closure\":[],\"prerequisite_frozen_node_ids\":[],\"repo_path\":\"D5/S0/Carrier/A.lean\"}"
            + "],\"producer\":\"TruthExportCommand\",\"schema\":\"stratalint.truth-export\",\"schema_version\":1,"
            + "\"source_commit\":\"" + Commit + "\",\"source_tree\":\"" + Tree + "\"}\n";

        Assert.Throws<FormatException>(() => TruthExportJsonReader.Read(Encoding.UTF8.GetBytes(descending)));
    }

    [Fact]
    public void StrictReaderRejectsANodeWithNoDeclarations()
    {
        // Every exported node is invariantly Closed and carries at least one declaration; a node with an
        // empty declaration array is malformed even though its shape is otherwise valid.
        var noDeclarations =
            "{\"dialect\":\"stratalint.truth-export.v1\",\"lean_report_digest\":\"" + LeanReportDigest + "\",\"nodes\":["
            + "{\"declarations\":[],\"frozen_node_id\":\"sha256:fa\",\"node_axiom_closure\":[],\"prerequisite_frozen_node_ids\":[],\"repo_path\":\"D5/S0/Carrier/A.lean\"}"
            + "],\"producer\":\"TruthExportCommand\",\"schema\":\"stratalint.truth-export\",\"schema_version\":1,"
            + "\"source_commit\":\"" + Commit + "\",\"source_tree\":\"" + Tree + "\"}\n";

        Assert.Throws<FormatException>(() => TruthExportJsonReader.Read(Encoding.UTF8.GetBytes(noDeclarations)));
    }

    [Fact]
    public void StrictReaderRejectsUnsortedPrerequisiteFrozenNodeIds()
    {
        var unsortedPrerequisites =
            "{\"dialect\":\"stratalint.truth-export.v1\",\"lean_report_digest\":\"" + LeanReportDigest + "\",\"nodes\":["
            + "{\"declarations\":[{\"declaration_name_key\":\"nk-a\",\"kind\":\"theorem\",\"statement_id\":\"sha256:a\"}],\"frozen_node_id\":\"sha256:fa\",\"node_axiom_closure\":[],\"prerequisite_frozen_node_ids\":[\"sha256:b\",\"sha256:a\"],\"repo_path\":\"D5/S0/Carrier/A.lean\"}"
            + "],\"producer\":\"TruthExportCommand\",\"schema\":\"stratalint.truth-export\",\"schema_version\":1,"
            + "\"source_commit\":\"" + Commit + "\",\"source_tree\":\"" + Tree + "\"}\n";

        Assert.Throws<FormatException>(() =>
            TruthExportJsonReader.Read(Encoding.UTF8.GetBytes(unsortedPrerequisites)));
    }

    [Fact]
    public void StrictReaderRejectsMalformedLeanReportDigest()
    {
        var malformed =
            "{\"dialect\":\"stratalint.truth-export.v1\",\"lean_report_digest\":\"sha256:ABC\","
            + "\"nodes\":[],\"producer\":\"TruthExportCommand\","
            + "\"schema\":\"stratalint.truth-export\",\"schema_version\":1,"
            + "\"source_commit\":\"" + Commit + "\",\"source_tree\":\"" + Tree + "\"}\n";

        Assert.Throws<FormatException>(() =>
            TruthExportJsonReader.Read(Encoding.UTF8.GetBytes(malformed)));
    }

    [Theory]
    [InlineData("")]
    [InlineData("sha256:ABC")]
    [InlineData("sha256:333333333333333333333333333333333333333333333333333333333333333G")]
    public void CreateRejectsMalformedLeanReportDigest(string digest) =>
        Assert.Throws<ArgumentException>(() => TruthExportModel.Create(
            ImmutableArray<TruthExportNode>.Empty,
            Commit,
            Tree,
            digest));

    [Theory]
    [InlineData("{}\n")]
    [InlineData("{\"schema\":\"stratalint.truth-export\",\"schema_version\":1,\"dialect\":\"stratalint.truth-export.v1\",\"source_commit\":\"c\",\"source_tree\":\"t\",\"lean_report_digest\":\"sha256:3333333333333333333333333333333333333333333333333333333333333333\",\"producer\":\"TruthExportCommand\",\"nodes\":[],\"extra\":true}\n")]
    [InlineData("{\"schema\":\"wrong\",\"schema_version\":1,\"dialect\":\"stratalint.truth-export.v1\",\"source_commit\":\"c\",\"source_tree\":\"t\",\"lean_report_digest\":\"sha256:3333333333333333333333333333333333333333333333333333333333333333\",\"producer\":\"TruthExportCommand\",\"nodes\":[]}\n")]
    [InlineData("{\"schema\":\"stratalint.truth-export\",\"schema_version\":1,\"dialect\":\"stratalint.truth-export.v2\",\"source_commit\":\"c\",\"source_tree\":\"t\",\"lean_report_digest\":\"sha256:3333333333333333333333333333333333333333333333333333333333333333\",\"producer\":\"TruthExportCommand\",\"nodes\":[]}\n")]
    [InlineData("{\"schema\":\"stratalint.truth-export\",\"schema_version\":1,\"dialect\":\"stratalint.truth-export.v1\",\"source_commit\":\"c\",\"source_tree\":\"t\",\"lean_report_digest\":\"sha256:3333333333333333333333333333333333333333333333333333333333333333\",\"producer\":\"Impostor\",\"nodes\":[]}\n")]
    public void StrictReaderRejectsMalformedOrUnknownFields(string json) =>
        Assert.Throws<FormatException>(() => TruthExportJsonReader.Read(Encoding.UTF8.GetBytes(json)));
}
