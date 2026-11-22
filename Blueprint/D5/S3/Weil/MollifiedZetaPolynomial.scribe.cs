using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class MollifiedZetaPolynomialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Möbius convolution for the zeta mollifier",
        H("Finite Möbius convolution for the zeta mollifier"),
        Blocks(Describe.Lean(
            DescribeId.Create("integral-norm-mollified-zeta-sub-one-sq-le"),
            DeclarationHandle.Create("D5/S3/Weil/MollifiedZetaPolynomial.integral_norm_mollifiedZeta_sub_one_sq_le"),
            H("Separate the finite convolution and the truncation error"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Multiplying the finite zeta sum by the Möbius polynomial cancels all nonconstant "
                + "coefficients through the Möbius cutoff. Above that cutoff the divisor count bounds the "
                + "convolution coefficients. The actual mollified second moment on a segment away from the "
                + "pole is controlled by the convolution tail and the zeta truncation error."))),
            DescribeRole.Theorem))));
}
