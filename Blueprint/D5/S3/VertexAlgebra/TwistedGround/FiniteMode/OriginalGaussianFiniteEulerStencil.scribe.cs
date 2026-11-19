using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FiniteMode;

internal sealed class OriginalGaussianFiniteEulerStencilDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Original Gaussian Polynomial Euler Stencil",
        H("Finite Original Gaussian Polynomial Euler Stencil"),
        Blocks(
            Describe.Lean(DescribeId.Create("p-euler-stencil"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFiniteEulerStencil.P_euler_stencil"), H("P_euler_stencil"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For all natural p,q and complex r, r*PPrime-(p+1/2)*(P-XP)=r*a(p)*a(q)/4-(1-r)*(a(p)-Xa(p))*(r*aPrime(q))/2. The proof applies E twice to the actual residual, retaining the derivative of 1-r, and reduces the resulting finite shift polynomial to 2*(Q-(1-r)*YQ)+r*YA=0. Triangular injectivity of E includes both zero axes. No division by r or 1-r occurs. P retains its direct r squared XY L_h2 term. The guarded predecessor here is an auxiliary polynomial shift; the genuine signed boundary and literal original/candidate identification are separate obligations."))), DescribeRole.Theorem))));
}
