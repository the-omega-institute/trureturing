using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualPiecePrefixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualPiecePrefix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two retained start edges force a literal actual path prefix and an exact second-edge cut.",
        H("Cutting the Forced Prefix of an Actual Graph Path"),
        Blocks(
            Paragraph(Text("The vertex type and simple graph are arbitrary. A Piece records its actual walk and both actual endpoints. Full support lists retain every vertex; Sym2 edges forget orientation. These generic statements supply the local slicing and endpoint steps used in recursive native graph surgery. They do not themselves assert a recursively constructed Hamilton cycle for all orders.")),
            Describe.Lean(DescribeId.Create("actual-two-retained-edges-force-prefix"),
                DeclarationHandle.Create(Prefix + "actual_two_retained_edges_force_prefix"),
                H("Two Edges Force the Literal Prefix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let p be an actual simple path from a to b with edges {a,x} and {x,y}, and assume y differs from a. Then actual adjacencies a-x and x-y and a simple tail q from y to b exist, with p literally equal to their two cons steps followed by q. Its support equals a :: x :: support(q), and its edges equal {a,x} :: {x,y} :: edges(q). Starting-edge uniqueness is applied twice to the actual path; y differs from a to exclude identifying the two undirected edges."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-second-edge-cut-of-prefix"),
                DeclarationHandle.Create(Prefix + "actual_second_edge_cut_of_prefix"),
                H("Cut the Forced Second Edge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under those same hypotheses, actual simple paths p0 from a to x and p1 from y to b exist. The first has length one. Their full supports concatenate to the original support; their edges, with {x,y} inserted between them, equal the original edge list. Without that cut their edges equal the original list filtered to exclude {x,y}. Simplicity rules out any further occurrence of the cut."))), DescribeRole.Theorem))));
}
