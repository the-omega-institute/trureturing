using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9MinimumContactDirectionChartDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9MinimumContactDirectionChart.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A lower bound for closest endpoints without shared directions.",
        H("Eighteen endpoints with the same translated vertex"),
        Blocks(Describe.Lean(
            DescribeId.Create("q9-eighteen-near-fixed-direction-origin"),
            DeclarationHandle.Create(Owner + "eighteen_endpoints_of_fixed_direction_origin"),
            H("Eighteen endpoints when all closest pairs have disjoint directions"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Let both supports be balanced induced cubic sets in the nine-cube with "
                + "mutual separation at least three. Assume every cross-pair at distance "
                + "three has disjoint occupied direction triples. Each attained translation "
                + "value then has at least eighteen endpoints in the second support. "
                + "Translate each closest endpoint by its three occupied "
                + "directions. Within a fixed translation value, its direction triple determines "
                + "the vertex. An occurring pair of directions represents an occupied midpoint "
                + "with three neighbors. The two-step exchanges supply at least five neighboring "
                + "triples at each endpoint. The partition of the neighbor directions forces "
                + "their new axes to be distinct. These properties supply the face restrictions "
                + "of the eighteen-triple bound. "
                + "<https://arxiv.org/html/2610.09483v1#Thmproblem2>"))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "DistanceThreeTripleFamilyBound")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9DistanceThreeUnsharedDirections"))
        ]));
}
