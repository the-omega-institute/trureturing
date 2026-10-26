using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GroundRightCurrentTransport;

internal sealed class ResidueDocument : IScribeDocumentDefinition
{

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual-input finite residue fields",
        H("Actual-input finite residue fields"),
        Blocks(
            Paragraph(Text("For two ordinary physical slices A and B, R(A,B,r) is constructed coefficientwise from the two ordered residue sums. Each ordered sum has its own finite support on its actual input. Linearity is proved before the lower-truncated field is constructed. The lower bound uses the finite family of intermediate vectors A[j]x, not a vector-vacuum assumption.")),
            Paragraph(Text("Z(c,A) shifts modes by c. The inverse product Q(A,B,s,r,K) is the finite sum of choose(-s/2,ell) Z(ell,R(A,B,r+ell)) for ell in range((K-r).toNat). Valid(A,B,K) means that the complete residue vanishes at every signed order at least K. Two valid cutoffs give the same field; no ordered half is asserted to vanish solely because the complete residue does.")),
            Paragraph(Text("Finite convolution reuses the accepted CurrentBorcherds scalar theorem. Joint supports for the ordered triple compositions are computed on their actual intermediate inputs and justify the nested residue expansion and exchange of sums. These helpers are consumed by Interchange; they are not a compatibility endpoint.")))));
}
