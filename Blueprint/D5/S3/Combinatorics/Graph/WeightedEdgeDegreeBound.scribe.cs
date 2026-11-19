using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class WeightedEdgeDegreeBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "WeightedEdgeDegreeBound",
        H("Weighted edge bounds for induced subgraphs"),
        Blocks(Describe.Lean(
            DescribeId.Create("weighted-edge-degree-cardinality"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/WeightedEdgeDegreeBound.card_le_of_weights"),
            H("Edge weights bound the size of an induced bounded-degree set"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "In a finite vertex region, assign nonnegative weights to vertices, edges, and vertex slack. "
                    + "Each edge weight is at most the sum of its endpoint weights. At each vertex the "
                    + "incident edge weights and slack cover one unit plus its vertex weight times the degree limit.")),
                Paragraph(Text(
                    "For a selected set with the stated induced degree limit, sum the covering inequalities "
                    + "over selected vertices. An edge with two selected endpoints contributes twice. Its second "
                    + "contribution is bounded by the two endpoint weights and charged to the induced degree "
                    + "at each endpoint. The remaining edge weights and slack bound the cardinality.")),
                Paragraph(Text(
                    "Integer scaling lets a solver propose rational weights and lets Lean verify their inequalities "
                    + "exactly. In the nine-cube, the region can exclude a fixed cubic component and its neighbors, "
                    + "so the certificate bounds the number of vertices that can extend the component."))),
            DescribeRole.Theorem))));
}
