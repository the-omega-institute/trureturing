using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9K33AlignedLayerDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9K33AlignedLayer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The six-axis antipode aligns contacting slices as three-by-three rectangles.",
        H("Three-by-three rectangles in the nine-mask branch"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("aligned-layers-eq-product"),
                DeclarationHandle.Create(Owner + "aligned_layers_eq_product"),
                H("The six-axis antipode aligns the two slices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("After the antipode in the six active coordinates, the simultaneous translations act by corner swaps in the two parity blocks. The two aligned sets coincide and are a product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("aligned-layer-three-by-three"),
                DeclarationHandle.Create(Owner + "aligned_layer_three_by_three"),
                H("Both projections have three points"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The shared midpoint rule supplies exactly two neighbors in each candidate triple. The remaining antipodal point fixes the size of each projection at three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nine-masks-on-six-axes-force-contact-rectangles"),
                DeclarationHandle.Create(Owner + "nine_masks_on_six_axes_force_contact_rectangles"),
                H("Every actual contact lies in a three-by-three rectangle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A single coordinate permutation, obtained from the two parts of the mask graph, works for every distance-two contact on the chosen parity. In its exterior slice the six-axis antipode aligns both supports as the same three-by-three rectangle. This restricts the six-axis branch in Hong–Wu–Xia Problem 2."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9DegreeThreeContactOrbit")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9K33ContactRectangles")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9SquareMaskGraph"))
        ]));
}
