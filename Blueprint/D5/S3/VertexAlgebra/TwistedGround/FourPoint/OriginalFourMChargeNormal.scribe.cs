using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMChargeNormalDocument : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeNormal.fourM_scalar_sewnTaylor";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Taylor coefficients of the original four-point sewn charge sums",
        H("The original four-point sewn Taylor coefficient"),
        Blocks(Describe.Lean(
            DescribeId.Create("original-fourm-scalar-sewn-taylor"),
            DeclarationHandle.Create(Gid),
            H("The actual fourM scalar"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let D be a rank-24 lattice datum with positive definite real Gram matrix "
                    + "and unit Gram determinant. Take H, K, E in ℕ and t in ℤ. Let u = P ⊗ x and v = Q ⊗ y "
                    + "belong to the actual minus-one parity space and satisfy L₀u = Hu and L₀v = Kv. "
                    + "Here P, Q, R, S are oscillator polynomials and x, y, z, d are actual ground vectors.")),
                Paragraph(Text("The scalar fourMScalar at modes H + K − E − 1 and t on "
                    + "u, v, R ⊗ z, S ⊗ d is the sum over a in ModTwoCharge D of "
                    + "((−1)^E · cosetSewnTaylor(D,H,K,E,t,P,Q,R,S,a)) "
                    + "· groundForm(D,y,Cₐx) · groundForm(D,d,Cₐz). "
                    + "The operator Cₐ is chargeOperator for the actual ground representation, "
                    + "and each ground form uses the given unit determinant.")),
                Paragraph(Text("For each fixed occupation, cosetSewnTaylor uses the ordinary Taylor coefficient "
                    + "of order 2E at zero of the sewn sum restricted to charge class a. The term at charge q "
                    + "has both charge scalars, for q and −q, the sewing variable to power 2·chargeEnergy(D,q), "
                    + "and the fixed-occupation sewn Gaussian. The finite projection includes both original "
                    + "lowerings with their factorials and sign, the four occupation factorials, and both "
                    + "Laurent selectors. The outer sign (−1)^E accounts for the negative square coordinate."))),
            DescribeRole.Theorem))));
}
