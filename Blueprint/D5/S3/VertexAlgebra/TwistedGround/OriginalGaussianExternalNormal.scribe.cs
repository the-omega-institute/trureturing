using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalNormalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint Normal Bounds for the Literal Kernels",
        H("Joint Normal Bounds for the Literal Kernels"),
        Blocks(
            Paragraph(Text("The finite antidiagonal binomial theorem reduces every polynomial frequency majorant to a polynomial times (delta+rho)^n. The smaller joint disk delta+rho<1 suffices; no uniform external radius at the whole radial disk boundary is asserted. These estimates do not by themselves establish differentiation of every generated equation.")),
            Describe.Lean(
                DescribeId.Create("external-binomial-joint-summable"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.external_binomial_joint_summable"),
                H("external_binomial_joint_summable"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either sign, every natural polynomial degree d and nonnegative delta,rho with delta+rho<1, the double sum of (p+s+1)^d delta^p rho^s times the norm of the actual external binomial is summable."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("externalcolumn-joint-summable"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.externalColumn_joint_summable"),
                H("externalColumn_joint_summable"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either sign and complex u,z with norm(u)+norm(z)<1, the joint sum of norm(u)^p times the norm of the original externalColumn at n is summable."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("externalvector-mode-summable"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.externalVector_mode_summable"),
                H("externalVector_mode_summable"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either sign and norm(u)+norm(z)<1, the norms of the actual Hilbert-space mode vectors u^p externalVector are summable."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("external-kernel-mode-summable"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.external_kernel_mode_summable"),
                H("external_kernel_mode_summable"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For both signs and complex u,v,z with norm(u)+norm(z)<1 and norm(v)+norm(z)<1, the full actual J and full actual T external mode double series are norm summable."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourceamplitude-joint-summable"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalNormal.sourceAmplitude_joint_summable"),
                H("sourceAmplitude_joint_summable"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either sign and norm(u)+norm(x)<1, the joint absolute series of the evaluated A coefficients times x^n u^p is summable."))), DescribeRole.Theorem))));
}
