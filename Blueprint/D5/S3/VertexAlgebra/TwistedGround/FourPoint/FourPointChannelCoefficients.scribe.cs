using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class FourPointChannelCoefficientsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Laurent Coefficients of the Actual Four-Point Channels.",
        H("Laurent Coefficients of the Actual Four-Point Channels"),
        Blocks(
            Describe.Lean(DescribeId.Create("is-diagonal-numerator"),
                DeclarationHandle.Create(Prefix + "IsDiagonalNumerator"),
                H("Diagonal numerator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The numerator is holomorphic at zero and its coefficient of order E is the original coset kernel at the two signed modes H+K−E−1 and E+(s−H−K+1)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-diagonal-numerator"),
                DeclarationHandle.Create(Prefix + "actualDiagonalNumerator"),
                H("Canonical actual numerator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use the sum of the rescaled Taylor series of the original coset at right mode E+(s−H−K+1) in degree E."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-diagonal-numerator-spec"),
                DeclarationHandle.Create(Prefix + "actualDiagonalNumerator_spec"),
                H("Exact coefficients and sewn pullback"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact energy-coefficient formula identifies every Taylor coefficient with the native coset kernel. "
                    + "Uniqueness of the sum on the common disk transfers the negative-square pullback to the canonical numerator. "
                    + "The pullback equals the even part of the actual Laurent-projected sewn charge sum."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("has-principal-part-channel-a"),
                DeclarationHandle.Create(Prefix + "hasPrincipalPart_channelA"),
                H("Iterate residue"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Extract the coefficient of the simple pole after multiplying the Laurent germ by the signed power tʳ and the binomial factor (1+t)ᵐ."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("has-principal-part-channel-b"),
                DeclarationHandle.Create(Prefix + "hasPrincipalPart_channelB"),
                H("B-channel residue"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Apply the finite lowering sum to the permuted inputs Q, R, P and use the detector lowered ell times at summed mode m+n+r+ell. "
                    + "The weight is tⁿ(1−t)ʳ."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("has-principal-part-channel-d"),
                DeclarationHandle.Create(Prefix + "hasPrincipalPart_channelD"),
                H("D-channel residue"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use the permuted inputs P, R, Q and the lowered detector at summed mode m+n+r+ell. "
                    + "The weight tᵐ(t−1)ʳ yields the original D sign."))),
                DescribeRole.Theorem))));
}
