using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class SupportedFinalCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed native monomial multiplication", H("Signed native monomial multiplication"), Blocks(
            Describe.Lean(DescribeId.Create("supportedfinalcovariance-finalslice"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.finalSlice"),
                H("finalSlice"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix the signed third coefficient before the final bivariate native shear."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("supportedfinalcovariance-signed-final-transform"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.signed_final_transform"),
                H("signed_final_transform"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The final signed collision transform equals the native final shear. The common native coefficients imply the actual lower support used in the finite sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("supportedfinalcovariance-signed-extra-mul"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.signed_extra_mul"),
                H("signed_extra_mul"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplication by (X0+X1)^A X1^B is the finite signed binomial translation on every exponent."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("supportedfinalcovariance-remove-supported-extra"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/SupportedFinalCovariance.remove_supported_extra"),
                H("remove_supported_extra"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual uniform first-coordinate lower bound licenses the supported positive inverse and cancels the temporary extra factor. The third coordinate remains unrestricted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-extension"),
                DeclarationHandle.Create(Prefix + "signedExtension"),
                H("signedExtension"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Signed extension is a complex-linear map from native series to signed coefficient distributions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("signed-x-pow-mul"),
                DeclarationHandle.Create(Prefix + "signed_X_pow_mul"),
                H("signed_X_pow_mul"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplication of a native series by X_i^n subtracts n in signed coordinate i. This identity holds at every signed exponent, including the zero branches caused by a negative target or an insufficient monomial degree."))), DescribeRole.Theorem))));
}
