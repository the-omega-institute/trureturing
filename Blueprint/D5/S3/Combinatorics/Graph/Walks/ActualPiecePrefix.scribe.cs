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
                Blocks(Paragraph(Text("Under those same hypotheses, actual simple paths p0 from a to x and p1 from y to b exist. The first has length one. Their full supports concatenate to the original support; their edges, with {x,y} inserted between them, equal the original edge list. Without that cut their edges equal the original list filtered to exclude {x,y}. Simplicity rules out any further occurrence of the cut."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-partition-incident-edge-owner"),
                DeclarationHandle.Create(Prefix + "actual_partition_incident_edge_owner"),
                H("An Incident Edge Belongs to the Unique Actual Piece"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In a list of pieces whose full supports contain no repeated vertex, an edge from the global inventory incident to a vertex of one supplied piece must belong to that same piece. This recovers local edge ownership from the actual global vertex partition."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-piece-prefix-from-retained-inventory"),
                DeclarationHandle.Create(Prefix + "actual_piece_prefix_from_retained_inventory"),
                H("Recover a Prefix from the Global Retained Inventory"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an actual simple piece in such a vertex partition, two retained global edges beginning at its literal start force its literal two-step prefix, provided the second endpoint differs from the start. Global ownership is proved before the local prefix construction is applied."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-piece-suffix-from-retained-inventory"),
                DeclarationHandle.Create(Prefix + "actual_piece_suffix_from_retained_inventory"),
                H("Recover the Actual Two-Step Suffix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The corresponding retained edges incident to the literal finish force a two-step suffix of the supplied piece. The proof reverses that actual path, recovers the prefix there and reverses the constructed walk; it keeps the original endpoints."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-retained-suffix-cut-position"),
                DeclarationHandle.Create(Prefix + "actual_retained_suffix_cut_position"),
                H("Locate the Directed Cut in the Actual Path"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given two distinct retained suffix edges of a supplied actual simple path, an actual edge index exists whose getVert values give the required directed cut. Its index lies within the original path length. This supplies a concrete cut position for the subsequent ordered slicing proof."))), DescribeRole.Theorem))));
}
