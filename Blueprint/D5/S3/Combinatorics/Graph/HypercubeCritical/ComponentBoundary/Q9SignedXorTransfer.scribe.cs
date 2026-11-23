using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SignedXorTransferDocument : IScribeDocumentDefinition
{
    private const string Parent = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Module = Parent + "Q9SignedXorTransfer";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed XOR transfer for overlapping nine-cube masks",
        H("Parity coupling across opposite cells"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-overlapping-mask-signed-xor"),
                DeclarationHandle.Create(Module + ".overlapping_mask_signed_xor"),
                H("Exact transfer for overlapping four-axis eigenvectors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let B be the sum of the signed flips on the three common axes of two masks. "
                        + "Write A and D for their respective exclusive signed flips. Take ambient "
                        + "eigenvectors f and g for B + A and B + D at eigenvalue 2. The two exclusive "
                        + "bits specify the common-cell traces f₀ and g₀, and changing the respective "
                        + "exclusive bit gives f₁ and g₁.")),
                    Paragraph(Text(
                        "Projecting the eigenvector equations to the common cell gives "
                        + "f₁ = A(2I − B)f₀ and g₁ = D(2I − B)g₀. The two involutions cancel against "
                        + "the ordered signed action AD in the pairing. Self-adjointness and B² = 3I "
                        + "then give the total pairing ⟨f₁, AD g₁⟩ = ⟨f₀, (7I − 4B)g₀⟩.")),
                    Paragraph(Text(
                        "Let Sₜ be the pairing of the common-cell traces on parity t, Dₜ the signed XOR "
                        + "pairing of the opposite traces on that parity, and L = ⟨f₀, B g₀⟩. Each signed "
                        + "flip reverses parity, yielding D₀ = 3S₀ + 4S₁ − 2L and D₁ = 4S₀ + 3S₁ − 2L. "
                        + "In particular D₀ − D₁ = S₁ − S₀.")),
                    Paragraph(Text(
                        "For Hong, Wu and Xia's Problem 2, a four-axis face witness with the stated "
                        + "ambient eigenvector equation can be used as the corresponding input. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Parent + "Q9SignedContactCells")),
            DocumentEdge.Dependency.Create(GidRef.Create(Parent + "Q9MaskedSpectrum"))
        ]));
}
