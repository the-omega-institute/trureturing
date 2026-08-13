using System.Reflection;
using System.Runtime.CompilerServices;
using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class ScribeNodeTests
{
    [Fact]
    public void Create_supports_neither_edges_nor_anchors()
    {
        var document = Create("D5/S0/ScribeNode/Neither");
        var edgeControl = Create(
            "D5/S0/ScribeNode/NeitherEdgeControl",
            edges: [Edge("D5/S0/ScribeNode/NeitherEdgePayload")]);
        var anchorControl = Create(
            "D5/S0/ScribeNode/NeitherAnchorControl",
            anchors: [Anchor.ParseCanonical("lit/scribenode2026aneither")]);

        Assert.Empty(document.Edges);
        Assert.NotEmpty(edgeControl.Edges);
        Assert.Empty(document.Header.Anchors);
        Assert.NotEmpty(anchorControl.Header.Anchors);
    }

    [Fact]
    public void Create_supports_edges_only()
    {
        var expectedEdge = Edge("D5/S0/ScribeNode/EdgesOnlyPayload");
        var document = Create("D5/S0/ScribeNode/EdgesOnly", edges: [expectedEdge]);
        var anchorControl = Create(
            "D5/S0/ScribeNode/EdgesOnlyAnchorControl",
            anchors: [Anchor.ParseCanonical("lit/scribenode2026bedgescontrol")]);

        Assert.Collection(document.Edges, actual => Assert.Same(expectedEdge, actual));
        Assert.Empty(document.Header.Anchors);
        Assert.NotEmpty(anchorControl.Header.Anchors);
    }

    [Fact]
    public void Create_supports_anchors_only()
    {
        var expectedAnchor = Anchor.ParseCanonical("lit/scribenode2026canchorsonly");
        var document = Create("D5/S0/ScribeNode/AnchorsOnly", anchors: [expectedAnchor]);
        var edgeControl = Create(
            "D5/S0/ScribeNode/AnchorsOnlyEdgeControl",
            edges: [Edge("D5/S0/ScribeNode/AnchorsOnlyEdgeControlPayload")]);

        Assert.Empty(document.Edges);
        Assert.NotEmpty(edgeControl.Edges);
        Assert.Collection(document.Header.Anchors, actual => Assert.Equal(expectedAnchor, actual));
    }

    [Fact]
    public void Create_supports_both_edges_and_anchors()
    {
        var expectedEdge = Edge("D5/S0/ScribeNode/BothEdgePayload");
        var expectedAnchor = Anchor.ParseCanonical("lit/scribenode2026eboth");

        var document = Create(
            "D5/S0/ScribeNode/Both",
            edges: [expectedEdge],
            anchors: [expectedAnchor]);

        Assert.Collection(document.Edges, actual => Assert.Same(expectedEdge, actual));
        Assert.Collection(document.Header.Anchors, actual => Assert.Equal(expectedAnchor, actual));
    }

    [Fact]
    public void Create_signature_preserves_parameter_order_and_caller_file_path_contract()
    {
        var method = typeof(ScribeNode).GetMethod(nameof(ScribeNode.Create), BindingFlags.Public | BindingFlags.Static);

        Assert.NotNull(method);
        var parameters = method!.GetParameters();
        Assert.Equal(
            [typeof(string), typeof(Heading), typeof(BlockSequence), typeof(IEnumerable<DocumentEdge>),
             typeof(IEnumerable<Anchor>), typeof(string)],
            parameters.Select(static parameter => parameter.ParameterType));
        Assert.NotNull(parameters[^1].GetCustomAttribute<CallerFilePathAttribute>());
        Assert.True(parameters[^1].HasDefaultValue);
        Assert.Equal(string.Empty, parameters[^1].DefaultValue);
    }

    [Fact]
    public void Create_binds_a_fourth_position_document_edge_array_to_edges()
    {
        var edge = Edge("D5/S0/ScribeNode/PositionalEdgePayload");

        var document = ScribeNode.Create(
            "Digest",
            DefinitionDsl.H("Title"),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Content"))),
            new DocumentEdge[] { edge },
            null,
            "/repo/Blueprint/D5/S0/ScribeNode/PositionalBinding.scribe.cs");

        Assert.Equal("D5/S0/ScribeNode/PositionalBinding", document.Header.Gid.Value);
        Assert.Collection(document.Edges, actual => Assert.Same(edge, actual));
    }

    [Fact]
    public void Create_named_source_path_preserves_legacy_gid_semantics()
    {
        const string path = "/repo/Blueprint/D5/S0/ScribeNode/NamedSourcePath.scribe.cs";
        var expected = DefinitionDsl.Header("D5/S0/ScribeNode/NamedSourcePath", "Digest");

        var document = ScribeNode.Create(
            "Digest",
            DefinitionDsl.H("Title"),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Content"))),
            sourcePath: path);

        Assert.Equal(expected.Gid, document.Header.Gid);
    }

    private static ScribeDocument Create(
        string gid,
        IEnumerable<DocumentEdge>? edges = null,
        IEnumerable<Anchor>? anchors = null) =>
        ScribeNode.Create(
            "Digest-" + gid,
            DefinitionDsl.H("Title " + gid),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("Content " + gid))),
            edges: edges,
            anchors: anchors,
            sourcePath: "/repo/Blueprint/" + gid + ".scribe.cs");

    private static DocumentEdge Edge(string target) =>
        DocumentEdge.Dependency.Create(GidRef.Create(target));
}
