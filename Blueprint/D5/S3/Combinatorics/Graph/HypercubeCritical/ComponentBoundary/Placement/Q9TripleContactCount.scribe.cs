using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9TripleContactCountDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9TripleContactCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fifteen-displacement bound for minimum contacts of length three in the nine-cube.",
        H("Minimum contacts at distance three"),
        Blocks(Describe.Lean(
            DescribeId.Create("q9-fifteen-minimum-displacements-distance-three"),
            DeclarationHandle.Create(Owner + "fifteen_minimum_displacements_at_distance_three"),
            H("At least fifteen displacements on an occupied parity"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Each occurring pair of axes in these three-axis displacements "
                + "has at least three extensions by signed coordinate cancellation. The "
                + "triple-system bound leaves only the complete family on five axes below "
                + "fifteen. The signed boundary at a tight contact cell excludes that "
                + "complete family when the initial support is balanced and cubic. "
                + "<https://arxiv.org/html/2610.09483v1#Thmproblem2>"))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9MinimumDistanceOperator")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9TightContactStar")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "TripleContactFamilyBound"))
        ]));
}
