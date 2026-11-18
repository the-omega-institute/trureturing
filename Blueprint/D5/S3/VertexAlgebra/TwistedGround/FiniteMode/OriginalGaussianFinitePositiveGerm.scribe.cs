using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FiniteMode;

internal sealed class OriginalGaussianFinitePositiveGermDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Original Gaussian Positive Source Equations and T Germ",
        H("Finite Original Gaussian Positive Source Equations and T Germ"),
        Blocks(
            Describe.Lean(DescribeId.Create("positive-t-mode-equations"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFinitePositiveGerm.positive_t_mode_equations"), H("positive_t_mode_equations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every natural p,q and real 0<r<1, the complete t=P-k*a(p)*a(q) satisfies L-R=(1-r)*(U(p)*V(q)-V(p)*U(q))/2 and 2*r*tPrime-L-R=(1-r)*(V(p)*V(q)-U(p)*U(q))/2. U and V are exactly the original signed source-frequency and source-jet expressions. L and R use negativeZeroT on their zero-index predecessors. The proof restores the actual Picard-Fuchs period term to P_euler_stencil and uses the genuine sqrt(1-r) source normalization. Symmetry supplies the second direction; no zero-boundary substitution is made."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("externalt-positive-finite-germ"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFinitePositiveGerm.externalT_positive_finite_germ"), H("externalT_positive_finite_germ"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For each natural p,q, the literal full externalT(true,p,true,q,z) equals candidateT(p,q,z) for all complex z in some neighborhood of zero. The candidate is the actual finite P minus the actual logarithmic period term, composed with z squared. Literal differentiability supplies actual analytic scalar expansions. The concrete original and candidate equations have identical signed crossing boundaries; only after their subtraction do the guarded positive differences have zero predecessors. The existing coefficient nonresonance theorem then proves this unconditional germ equality. No common mode radius, disk-wide equality, negative sign sector, or J identification is claimed."))), DescribeRole.Theorem))));
}
