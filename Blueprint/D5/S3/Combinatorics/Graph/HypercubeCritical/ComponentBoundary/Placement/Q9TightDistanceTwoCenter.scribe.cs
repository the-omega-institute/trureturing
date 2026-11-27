using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9TightDistanceTwoCenterDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9TightDistanceTwoCenter.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tight distance-two contact forces eight neighbors at each exterior star center.",
        H("Eight neighbors at each exterior star center"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tight-distance-two-cell"),
                DeclarationHandle.Create(Owner + "tight_distance_two_cell"),
                H("Eight neighbors at each exterior star center"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Four unit contributions from the star leaves have a common sign by negative square curvature and cancellation on the two-leaf rows. The exterior equation forces four more neighbors. Evenness and the nine available directions force equality and leave one missing exterior axis at each center."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9TightContactStar")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9ActualMinimumDisplacements"))
        ]));
}
