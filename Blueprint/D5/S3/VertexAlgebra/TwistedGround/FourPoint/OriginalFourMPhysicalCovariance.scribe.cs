using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMPhysicalCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance.";

    private static DocumentBlock Result(string id, string declaration, string heading, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Covariance and marked Gaussian coefficients in the four-point charts",
        H("Physical Four-Point Covariance Transport"),
        Blocks(
            Result("fourm-signed-physical-covariance-transport", "signed_physical_covariance_transport",
                "Covariance in the physical coordinates",
                "The elliptic kernel transports between all three charts after removing the native "
                + "same-puncture Cauchy correction and retaining the mixed free block. The "
                + "identity extends across coincident positions by regularity of the two kernels."),
            Result("fourm-marked-gaussian-jet", "marked_gaussian_jet", "Marked Gaussian coefficient",
                "Differentiation in an independent variable for each marked oscillator gives the "
                + "native affine coefficient times the product of the occupation factorials. "
                + "The oscillator label map can have repeated colours and modes."))));
}
