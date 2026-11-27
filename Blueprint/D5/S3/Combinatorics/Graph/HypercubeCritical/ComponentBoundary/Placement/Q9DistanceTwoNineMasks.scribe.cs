using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9DistanceTwoNineMasksDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9DistanceTwoNineMasks.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual component pair at distance two realizes at least nine masks on each nonempty starting parity.",
        H("At least nine masks for an actual distance-two pair"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-actual-pair-with-nine-masks"),
                DeclarationHandle.Create(Owner + "exists_actual_pair_with_nine_masks"),
                H("At least nine masks for an actual distance-two pair"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The eight-mask exclusion applies to the same pair of actual components selected by universal signed singularity. Every parity that realizes a contact therefore needs at least nine displacement masks."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9EightMaskReplay")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9TightDistanceTwoReplay")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9DistanceThreeExclusion"))
        ]));
}
