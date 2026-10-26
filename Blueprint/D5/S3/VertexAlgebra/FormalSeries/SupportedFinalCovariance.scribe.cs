using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class SupportedFinalCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed native monomial multiplication", H("Signed native monomial multiplication"), Blocks(
            Describe.Lean(DescribeId.Create("signed-extension"),
                DeclarationHandle.Create(Prefix + "signedExtension"),
                H("signedExtension"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Signed extension is a complex-linear map from native series to signed coefficient distributions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("signed-x-pow-mul"),
                DeclarationHandle.Create(Prefix + "signed_X_pow_mul"),
                H("signed_X_pow_mul"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplication of a native series by X_i^n subtracts n in signed coordinate i. This identity holds at every signed exponent, including the zero branches caused by a negative target or an insufficient monomial degree."))), DescribeRole.Theorem))));
}
