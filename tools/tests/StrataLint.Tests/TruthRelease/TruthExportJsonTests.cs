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

    private static string Id(char value) => "sha256:" + new string(value, 64);

    // Build a plain wire node directly. Trureturing.Truth owns the plain model + canonical reader/writer;
    // the Engine-dependent FrozenNodeMaterial -> plain projection stays in Scribe/base, so these tests
    // never touch StrataLint.Engine.
    private static TruthExportNode Node(
        string repoPath,
        string frozenId,
        string[] axioms,
        (string NameKey, string Kind, string StatementId)[] declarations,
        string[]? prerequisites = null) =>
        new(
            repoPath,
            frozenId,
            axioms.ToImmutableArray(),
            declarations
                .Select(static declaration => new TruthExportDeclaration(
                    declaration.NameKey, declaration.Kind, declaration.StatementId))
                .ToImmutableArray(),
            (prerequisites ?? Array.Empty<string>()).ToImmutableArray());

    [Fact]
    public void CreateCanonicalizesAndWriteIsDeterministicUtf8()
    {
        var nodes = ImmutableArray.Create(
            Node(
                "D5/S0/Carrier/Beta.lean", Id('b'),
                axioms: new[] { "propext", "Classical.choice" },
                declarations: new[] { ("nk-beta", "theorem", Id('c')) }),
            Node(
                "D5/S0/Carrier/Alpha.lean", Id('a'),
                axioms: new[] { "Quot.sound" },
                declarations: new[]
                {
                    ("nk-two", "theorem", Id('2')),
                    ("nk-one", "def", Id('1')),
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
        Assert.Equal("stratalint.truth-export", model.Schema);
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
        Assert.Equal(Id('1'), model.Nodes[0].Declarations[0].StatementId);
        Assert.Equal("def", model.Nodes[0].Declarations[0].Kind);
    }

    [Fact]
    public void CreateProducesOneByteSequenceRegardlessOfInputOrder()
    {
        var nodes = Enumerable.Range(0, 8)
            .Select(index => Node(
                $"D5/S0/Carrier/M{index}.lean", Id((char)('0' + index)),
                axioms: new[] { $"axiom{index}", "propext" },
                declarations: new[] { ($"nk-{index}", "theorem", Id((char)('0' + index))) }))
            .ToArray();
        var outputs = new HashSet<string>(StringComparer.Ordinal);
        for (var permutation = 0; permutation < 20; permutation++)
        {
            var multiplier = (permutation % 4 * 2) + 1;
            var offset = permutation / 4;
            var shuffled = nodes
                .Select((node, index) => (Node: node, Key: (index * multiplier + offset) % nodes.Length))
                .OrderBy(static item => item.Key)
                .Select(static item => item.Node)
                .ToImmutableArray();
            outputs.Add(Convert.ToBase64String(
                TruthExportJsonWriter.Write(TruthExportModel.Create(shuffled, Commit, Tree)).AsSpan()));
        }

        Assert.Single(outputs);
    }

    [Fact]
    public void StrictReaderRoundTripsEveryField()
    {
        var nodes = ImmutableArray.Create(
            Node("D5/S0/Carrier/A.lean", Id('a'), new[] { "propext" }, new[] { ("nk-a", "theorem", Id('1')) }),
            Node("D5/S0/Carrier/B.lean", Id('b'), Array.Empty<string>(), new[] { ("nk-b", "def", Id('2')) }, new[] { Id('a') }));
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
    public void EmptyNodeSetRoundTrips()
    {
        var model = TruthExportModel.Create(ImmutableArray<TruthExportNode>.Empty, Commit, Tree);
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
            + "{\"declarations\":[{\"declaration_name_key\":\"nk-b\",\"kind\":\"theorem\",\"statement_id\":\"" + Id('2') + "\"}],\"frozen_node_id\":\"" + Id('b') + "\",\"node_axiom_closure\":[],\"prerequisite_frozen_node_ids\":[],\"repo_path\":\"D5/S0/Carrier/B.lean\"},"
            + "{\"declarations\":[{\"declaration_name_key\":\"nk-a\",\"kind\":\"theorem\",\"statement_id\":\"" + Id('1') + "\"}],\"frozen_node_id\":\"" + Id('a') + "\",\"node_axiom_closure\":[],\"prerequisite_frozen_node_ids\":[],\"repo_path\":\"D5/S0/Carrier/A.lean\"}"
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
            "{\"dialect\":\"stratalint.truth-export.v1\",\"nodes\":["
            + "{\"declarations\":[],\"frozen_node_id\":\"" + Id('a') + "\",\"node_axiom_closure\":[],\"prerequisite_frozen_node_ids\":[],\"repo_path\":\"D5/S0/Carrier/A.lean\"}"
            + "],\"producer\":\"TruthExportCommand\",\"schema\":\"stratalint.truth-export\",\"schema_version\":1,"
            + "\"source_commit\":\"" + Commit + "\",\"source_tree\":\"" + Tree + "\"}\n";

        Assert.Throws<FormatException>(() => TruthExportJsonReader.Read(Encoding.UTF8.GetBytes(noDeclarations)));
    }

    [Theory]
    [InlineData("{}\n")]
    [InlineData("{\"schema\":\"stratalint.truth-export\",\"schema_version\":1,\"dialect\":\"stratalint.truth-export.v1\",\"source_commit\":\"c\",\"source_tree\":\"t\",\"producer\":\"TruthExportCommand\",\"nodes\":[],\"extra\":true}\n")]
    [InlineData("{\"schema\":\"wrong\",\"schema_version\":1,\"dialect\":\"stratalint.truth-export.v1\",\"source_commit\":\"c\",\"source_tree\":\"t\",\"producer\":\"TruthExportCommand\",\"nodes\":[]}\n")]
    [InlineData("{\"schema\":\"stratalint.truth-export\",\"schema_version\":1,\"dialect\":\"stratalint.truth-export.v2\",\"source_commit\":\"c\",\"source_tree\":\"t\",\"producer\":\"TruthExportCommand\",\"nodes\":[]}\n")]
    [InlineData("{\"schema\":\"stratalint.truth-export\",\"schema_version\":1,\"dialect\":\"stratalint.truth-export.v1\",\"source_commit\":\"c\",\"source_tree\":\"t\",\"producer\":\"Impostor\",\"nodes\":[]}\n")]
    public void StrictReaderRejectsMalformedOrUnknownFields(string json) =>
        Assert.Throws<FormatException>(() => TruthExportJsonReader.Read(Encoding.UTF8.GetBytes(json)));
}
