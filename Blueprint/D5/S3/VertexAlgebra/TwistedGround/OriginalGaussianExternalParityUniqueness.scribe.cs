using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalParityUniquenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Gaussian Kernel Parity and Positive-Sector Uniqueness",
        H("Original Gaussian Kernel Parity and Positive-Sector Uniqueness"),
        Blocks(
            Paragraph(Text("The external columns and internal matrix entries have monomial sign factors. The remaining explicit odd-resolvent factors depend on z squared. Every internal sign occurs twice in the literal contractions, including the full square-resolvent identity contribution.")),
            Paragraph(Text("The coefficient equations are those of the positive-sector operators L_u-L_v and z partial_z-L_u-L_v, where L_u=u(1-u) partial_u+(1-3u)/2. They exclude precisely the odd-z diagonal resonance. Uniqueness is proved conditionally on Taylor extraction; existence of a common solution for arbitrary right-hand sides is not claimed.")),
            Paragraph(Text("The existing displacement_differential and radial_differential theorems act on the original kernelMode and full externalT. Their conversion to the coefficient hypotheses, with the actual negative-zero rows canceled, remains to be proved. A complete analytic candidate, normalized branches and removable singularities, verification of both equations and boundaries, and equality in every signed sector remain separate obligations. Literal parity and the coefficient induction alone do not identify the complete kernels.")),
            Describe.Lean(
                DescribeId.Create("externalj-neg"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.externalJ_neg"),
                H("externalJ_neg"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every literal external J mode is even for all signs, natural labels and complex z. The summands agree before any convergence hypothesis is imposed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("externalt-neg"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.externalT_neg"),
                H("externalT_neg"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every literal full T mode is even for all signs, natural labels and complex z. The proof treats both the direct identity pairing and the triple sum."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernelmode-neg"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.kernelMode_neg"),
                H("kernelMode_neg"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either J or T and every sign sector, the actual two-mode generator is even in z for all complex external variables."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-even-coefficients-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.positive_even_coefficients_zero"),
                H("positive_even_coefficients_zero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a complex array c(p,q,k), zero odd coefficients and the two displayed homogeneous frequency and radial recurrences force every coefficient to vanish. Negative external indices are represented by explicit zero branches. Strong induction on p+q uses p-q off the diagonal; on the diagonal, k-2p-1 cannot vanish at an even exponent."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("externalt-positive-germ-unique"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalParityUniqueness.externalT_positive_germ_unique"),
                H("externalT_positive_germ_unique"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let a candidate be even in z for every natural pair of output labels. If its difference from the literal full externalT has the stated scalar Taylor expansions at zero and those coefficients satisfy both homogeneous recurrences with zero negative-index boundaries, then each literal output/output mode equals the candidate on a neighborhood of zero. No equality is assumed, and no diagonal initial values are needed."))), DescribeRole.Theorem))));
}
