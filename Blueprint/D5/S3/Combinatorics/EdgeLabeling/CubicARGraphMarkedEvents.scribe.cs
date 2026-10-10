using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling;

internal sealed class CubicARGraphMarkedEventsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed-label sample space and collision events at marked edges.",
        H("Marked-edge bad events"),
        Blocks(
            Node("MarkedLabeling", "Labelings with two fixed edge labels",
                "The sample space consists of equivalences from the edge type to Fin m "
                + "whose values on the two marked edges are zero and one.", DescribeRole.Definition),
            Node("markLabel", "Positive labels",
                "The label of an edge is one plus its zero-based finite value.",
                DescribeRole.Definition),
            Node("AdditiveTriple", "An additive collision",
                "An additive collision means that one of three edge labels is the sum of "
                + "the other two.", DescribeRole.Definition),
            Node("card_markedLabeling", "Size of the marked sample space",
                "For m edges and two distinct marked edges, the sample space has (m-2)! "
                + "elements.", DescribeRole.Theorem),
            Node("card_bad_both_marked", "The event containing both marked edges",
                "The triple with marked labels one and two is bad exactly when the third "
                + "label is three. There are (m-3)! such labelings.", DescribeRole.Theorem),
            Node("card_bad_single_marked_le", "The event containing one marked edge",
                "For a fixed incident label delta equal to one or two, a bad triple's two "
                + "free labels differ by delta. Their smaller value has m-2-delta choices "
                + "and they have two edge orders. Each assignment leaves (m-4)! extensions, "
                + "giving an upper bound of 2*(m-2-delta)*(m-4)!.", DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphCounting"))]));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-ar-marked-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
