using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9K33NormalizedRectangleDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33NormalizedRectangle.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Translating the missing labels fixes both rectangles and their contact axes.",
        H("Coordinate normalization of both contact rectangles"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalization-of-nine-masks-on-six-axes"),
                DeclarationHandle.Create(Owner + "normalization_of_nine_masks_on_six_axes"),
                H("Normalize a contact rectangle and all its masks"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each of the two parity triples has four labels and its rectangle occupies three. Translate the unique missing row and column and the exterior label to zero. In the normalized slice the left support has weight-two labels in both triples and the right support has weight-one labels in both. The same translation and permutation carry every contact on the chosen parity to one axis in each triple."))), DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33AlignedLayer")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TightDistanceTwoNormalized"))
        ]));
}
