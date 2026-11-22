using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMSlitCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native signed covariance on the Euler slit",
        H("Same-leg and opposite-leg kernels"),
        Blocks(
            Describe.Lean(DescribeId.Create("fourm-slit-j"),
                DeclarationHandle.Create(Prefix + "slitJ"),
                H("Regularized same-leg kernel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiply the two slit means by r/4 minus the slit period correction "
                    + "plus the regularized rational term. Its denominator contains the square of the sum "
                    + "of the two means weighted by their respective h factors."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fourm-slit-t"),
                DeclarationHandle.Create(Prefix + "slitT"),
                H("Opposite-leg kernel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiply the two slit means by the signed opposite-leg rational "
                    + "kernel minus the slit period correction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fourm-slit-covariance"),
                DeclarationHandle.Create(Prefix + "slitCovariance"),
                H("Signed slit covariance generator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For equal legs use the same-leg kernel with the free Cauchy term "
                    + "included for unequal external signs. For distinct legs use the negative "
                    + "of the opposite-leg kernel."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fourm-slit-covariance-native"),
                DeclarationHandle.Create(Prefix + "slitCovariance_eq_native"),
                H("Agreement with the native covariance"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every pair of legs and signs, if ‖u‖ + ‖r‖ < 1 and "
                    + "‖v‖ + ‖r‖ < 1, the slit covariance equals the native signed covariance generator."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-slit-covariance-analytic"),
                DeclarationHandle.Create(Prefix + "slitCovariance_joint_analytic"),
                H("Joint holomorphic covariance germ"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every point r of the Euler slit, the covariance is jointly analytic "
                        + "at (0,0,r) in both external variables and the radial parameter.")),
                    Paragraph(Text("At the Taylor centre the two weighted means have positive real parts. "
                        + "Their sum and the opposite-leg rational denominator are nonzero there, "
                        + "and the mixed-sign free term is analytic there."))),
                DescribeRole.Theorem))));
}
