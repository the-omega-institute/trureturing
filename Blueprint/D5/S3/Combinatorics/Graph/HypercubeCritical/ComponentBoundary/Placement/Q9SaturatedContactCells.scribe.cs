using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9SaturatedContactCellsDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted saturation forces signed cancellation within each two-bit contact cell.",
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
                    Paragraph(Text("The two coordinate sign changes give the three nonconstant Walsh coefficients. Together with the constant coefficient proved by the weight limit, they give cancellation on each fixed pair of bits. Each realized contact contributes a sign, so a nonempty cell contains equally many positive and negative contacts."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9ActualMinimumDisplacements")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells"))
        ]));
}
