using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9DistanceTwoAperiodicDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9DistanceTwoAperiodic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual component pair at distance two realizes at least eight masks on each nonempty starting parity.",
        H("At least eight masks for an actual distance-two pair"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-actual-pair-with-eight-masks"),
                DeclarationHandle.Create(Owner + "exists_actual_pair_with_eight_masks"),
                H("At least eight masks for an actual distance-two pair"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose the actual pair by universal signed singularity. The distance-three and distance-four exclusions apply to the same components. Each axis in the contact graph belongs to three or more masks, so seven masks could use only four axes and there would be room for only six edges. The opposing-star refutations exclude six. This leaves at least eight masks on every nonempty starting parity of the chosen pair. <https://arxiv.org/html/2610.09483v1#Thmproblem2>"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9TightDistanceTwoReplay")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9DistanceThreeExclusion"))
        ]));
}
