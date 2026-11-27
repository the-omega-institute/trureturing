using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMPhysicalCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed covariance in physical four-point coordinates",
        H("Regularized covariance transport"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-fourm-physical-covariance"),
                DeclarationHandle.Create(Prefix + "physicalCovariance"),
                H("Normal covariance in the physical coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either upperA, any chart c, real x, punctures p and q, and complex "
                    + "u and v, evaluate chartCovariance at the two inverse coordinates using the native "
                    + "flags of p and q. If p = q, subtract η(1 + βγ)/(2βγ(β + γ)²), where η is the lowering "
                    + "parameter of p and β and γ are the inverse roots at the two arguments of that "
                    + "puncture. The correction is zero for distinct punctures. Where the quotient is "
                    + "defined, divide the resulting covariance by the product of the two halfJacobian "
                    + "factors, each given by scaleRoot/β³ at its argument. For 0 < x < 1 and u near zero, "
                    + "this factor at p is the derivative of the lift t ↦ scaleRoot·t/β(t) with respect "
                    + "to the native half-coordinate t, evaluated at t² = rawLocal(c,x,p,u). "
                    + "Here λ is the lowering parameter of p and β(t)² = 1 − λt² with β(0) = 1. "
                    + "The second factor uses q and v in the same way."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-fourm-signed-physical-covariance-transport"),
                DeclarationHandle.Create(Prefix + "signed_physical_covariance_transport"),
                H("Signed covariance germs with the period discrepancy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take lattice data D with unit Gram determinant, either upperA, real "
                        + "0 < x < 1, a chart c and any punctures p and q. Let σ_c be 1 in A, (−i√x)⁻¹ "
                        + "in B and i⁻¹ in D. The puncture signs ρ_c are all +1 in A. In the order (P,Q,R,S), "
                        + "they are (+1,+1,+1,−1) in B and (+1,−1,−1,+1) in D. Write "
                        + "P_A = slitPeriod(1 − 1/x), P_B = slitPeriod(x), P_f = slitPeriod(1 − x) and "
                        + "P_D = dPeriod(upperA,1/x). The spatial source uses the chosen lower D root. The D "
                        + "period uses the lower radial lip for upperA = true and the upper lip for false.")),
                    Paragraph(Text("Set δ_A = 0, δ_B = 1/(π P_f P_B) and δ_D = 1/(π P_A P_D). Write C_c "
                        + "for physicalCovariance and M_A for physicalSource in A. On a neighborhood of "
                        + "(u,v) = (0,0), C_A(p,q,u,v) − δ_c (σ_c M_A(p,u))(σ_c M_A(q,v)) "
                        + "= ρ_c(p)ρ_c(q) C_c(p,q,u,v)."),
                    Text("For repeated punctures, the native Cauchy term plus its regular lowering correction, "
                        + "divided by the product of the half-Jacobians, equals (u+v)/(2(u−v)²) off the diagonal. "
                        + "Thus the two chart subtractions differ by exactly the difference of the normalized "
                        + "lowering corrections. Both regularized sides are analytic. Density and continuity "
                        + "extend the identity to the product neighborhood, including coincident evaluations "
                        + "and the center."))),
                DescribeRole.Theorem))));
}
