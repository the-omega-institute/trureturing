using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9SaturatedContactCellsDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted saturation forces signed cancellation on orbits of contact-neighbour flips.",
        H("Signed contact cancellation from one-coordinate saturation"),
        Blocks(
            Paragraph(Text("Hong, Wu and Xia's Problem 2 asks whether the nine-cube has a 258-vertex induced support of maximum degree three. Consider separated Huang-balanced cubic supports C and D, with D connected. Give the second contact axis j weight t and give every other axis weight one. Assume the signed Gram defect of D on the false parity is singular for every positive t. https://arxiv.org/html/2610.09483v1#Thmproblem2")),
            Describe.Lean(
                DescribeId.Create("q9-saturated-contact-cell-zero"),
                DeclarationHandle.Create(Placement + "Q9SaturatedContactCells.signed_overlap_cell_zero"),
                H("The signed contact sum vanishes in each two-bit cell"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For either parity of D, Gram singularity gives a nonzero supported vector whose weighted Huang image stays in D. Separation and the signed-flip anticommutator show that the contact functional vanishes on this vector when t differs from one.")),
                    Paragraph(Text("Normalize the vectors to unit norm. The supported kernel equations and the contact functional are continuous, and the compact unit sphere makes the projection onto the weight parameter closed. At t equal to one there is therefore a nonzero annihilated vector. The unit-weight kernel on the chosen parity of connected D is spanned by its switching vector.")),
                    Paragraph(Text("The indicator fixing the two contact bits is invariant under the flips in the other contact neighbours. Applying the invariant-multiplier theorem to this indicator gives the cell sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-saturated-contact-fibre-cell-zero"),
                DeclarationHandle.Create(Placement + "Q9SaturatedContactCells.signed_overlap_fibre_cell_zero"),
                H("The signed contact sum vanishes in each inactive-coordinate fibre"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose an axis set containing all distance-two contact masks on the chosen parity. The indicator fixing both contact bits and all bits outside that set is invariant under the necessary flips."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-contact-invariant-multiplier"),
                DeclarationHandle.Create(Placement + "Q9SaturatedContactCells.signed_overlap_multiplier_zero"),
                H("The signed contact pairing annihilates invariant multipliers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In a row paired with the flip in direction i, a derivative in a different direction k can contribute only through a realized distance-two contact mask {k,i} on the chosen parity.")),
                    Paragraph(Text("Split the multiplier into its invariant and anti-invariant parts under the j flip. The invariant part uses the positive weight limit. The anti-invariant part uses a sign change of the j weight in the signed-flip identity. Both parts have zero pairing."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-endpoint-contact-fibre-zero"),
                DeclarationHandle.Create(Placement + "Q9SaturatedContactCells.signed_overlap_endpoint_fibre_zero"),
                H("The signed contact sum vanishes on each endpoint-neighbour orbit"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a contact in directions i and j, generate a translation subgroup with the contact neighbours of i other than j. The indicator of each orbit is an invariant multiplier. The signed contact sum on that orbit vanishes separately on either parity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-saturated-contact-cell-card-even"),
                DeclarationHandle.Create(Placement + "Q9SaturatedContactCells.signed_overlap_cell_card_even"),
                H("Each fixed two-bit cell has an even number of contacts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the contact cell each switch and each of the two Huang edge entries has absolute value one. The zero signed sum therefore gives the same number of positive and negative contributions. This supplies a parity constraint on the occupied endpoint pairs in each cell."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9ActualMinimumDisplacements")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells"))
        ]));
}
