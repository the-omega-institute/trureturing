using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianPeriodIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Gaussian Determinant Period Identity",
        H("Original Gaussian Determinant Period Identity"),
        Blocks(
            Paragraph(Text("The original finite logarithms vanish at the zero operator, fixing the infinite logarithm and determinant constants at zero. Equality of radial logarithmic derivatives is integrated on the interior and extended continuously to zero. The principal complex logarithm is legal throughout the disk because the real part of one minus z squared is positive. The analytic identity principle extends the real formula to the whole complex unit disk. Nonvanishing of the existing period follows from that identity and the original exponential determinant, with no nonvanishing premise.")),
            Paragraph(Text("These are analytic identities for the original coefficient model on its infinite carrier. Physical vertex operator algebras, conformal field theory, anomaly and fusion structures, string theory and AdS/CFT realization remain open.")),
            Describe.Lean(
                DescribeId.Create("gaussian-log-det-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianLogDet_zero"),
                H("gaussianLogDet_zero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original infinite-cycle logarithm is zero at the zero operator, by the actual finite cutoff limit."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-det-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianDet_zero"),
                H("gaussianDet_zero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original exponential determinant equals one at zero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-log-det-real-normalization"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianLogDet_real_normalization"),
                H("gaussianLogDet_real_normalization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real r with zero less than or equal to r and r less than one, the original logarithm at sqrt r equals the real logarithm of F r plus one quarter of the real logarithm of one minus r."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-det-real-period-identity"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianDet_real_period_identity"),
                H("gaussianDet_real_period_identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real r from zero inclusive to one exclusive, the original determinant at sqrt r equals one minus r to the real power one quarter, multiplied by the existing F r, embedded into the complex numbers."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-det-complex-period-identity"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.gaussianDet_complex_period_identity"),
                H("gaussianDet_complex_period_identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex z of norm less than one, the original determinant equals exp of one quarter times the principal log of one minus z squared, multiplied by the existing OriginalHalfBinomialPeriod.period at z squared."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("period-ne-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity.period_ne_zero"),
                H("period_ne_zero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing OriginalHalfBinomialPeriod.period is nonzero at every complex argument of norm less than one."))), DescribeRole.Theorem))));
}
