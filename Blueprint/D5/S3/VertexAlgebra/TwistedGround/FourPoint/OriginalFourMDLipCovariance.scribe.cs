using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMDLipCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native signed covariance at the D-channel boundary",
        H("Boundary germ and slit agreement"),
        Blocks(
            Describe.Lean(DescribeId.Create("fourm-d-lip-covariance"),
                DeclarationHandle.Create(Prefix + "dLipCovariance"),
                H("D-lip covariance generator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the two D-lip means and the correction of the D period in the "
                    + "signed covariance. The equal-leg branch uses the weighted means in the regularized "
                    + "denominator and keeps the mixed-sign free term. The unequal-leg branch uses the "
                    + "negative of the corrected opposite-leg kernel times the two means."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fourm-d-lip-covariance-agreement"),
                DeclarationHandle.Create(Prefix + "dLipCovariance_eq_of_means"),
                H("Covariance agreement on the open lip"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a parameter on the designated open D lip, equality of the D-lip "
                    + "and slit means at both external arguments gives equality of the covariances. "
                    + "The period correction agrees there because the two periods and their derivatives agree."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-d-lip-covariance-analytic"),
                DeclarationHandle.Create(Prefix + "dLipCovariance_joint_analytic"),
                H("Joint holomorphic covariance germ at the D boundary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each real t > 1, all choices of lip, legs and external signs give "
                    + "an analytic covariance at (0,0,t) in both external variables and the radial parameter. "
                    + "The D period and the weighted same-leg denominator are nonzero at the centre."))),
                DescribeRole.Theorem))));
}
