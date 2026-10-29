using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class AsymptoticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/Asymptotic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The inverse-coordinate forward adjoint has an exact triangular main coefficient and a uniform C1 remainder.",
        H("The forward adjoint remainder"),
        Blocks(
            Paragraph(Text(
                "Use x(t,z) determined by t=x+z*x^(4/5), "
                + "J(t,z)=1/(1+(4/5)*z*x(t,z)^(-1/5)), "
                + "A(x,u)=w(x+u*x^(4/5))/w(x), and "
                + "P(t,z,s)=exp((-s-1/2)*log(x(t,z)/t)). The normalized "
                + "coefficient is the integral of P*A*J on the fixed triangle "
                + "0<=z<=u<=1. The area of that triangle is exactly 1/2.")),
            Describe.Lean(
                DescribeId.Create("forward-normalized-body-c1"),
                DeclarationHandle.Create(Prefix + "normalizedBody_C1_estimate"),
                H("Correlated control of the integrand and its derivative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For t>=8 and z,u in [0,1], the coefficient P*A*J is "
                    + "differentiable in t. With p=-s-1/2 and "
                    + "C(s)=(2*|p|+50)*exp(2*|p|)+10, its difference from "
                    + "one has norm at most C(s)*t^(-1/5), and its time "
                    + "derivative has norm at most C(s)*t^(-6/5). "
                    + "The derivative of the ratio A uses the same moving "
                    + "center in numerator and denominator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-inverse-adjoint-iterated"),
                DeclarationHandle.Create(Prefix + "inverseAdjoint_eq_iterated"),
                H("The exact inverse-coordinate integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The inverse-coordinate adjoint is t^(-s-1/2) times "
                    + "the normalized triangular coefficient. Fubini and the "
                    + "identity t^(-s-1/2)*P=x(t,z)^(-s-1/2) identify it "
                    + "with the integral over 0<=z<=1 of "
                    + "x(t,z)^(-s-1/2)*integral_z^1 A(x(t,z),u) du "
                    + "divided by 1+(4/5)*z*x(t,z)^(-1/5)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-inverse-adjoint-c1"),
                DeclarationHandle.Create(Prefix + "inverseAdjoint_uniform_C1_remainder"),
                H("Uniform C1 control after subtracting the principal term"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let r_s(t)=t^(-s-1/2)*(normalizedAdjoint(t,s)-1/2). "
                        + "For every compact K in the complex plane there is "
                        + "C_K>0 such that, for s in K and t>8, "
                        + "|r_s(t)|<=C_K*t^(-Re(s)-1/2)*t^(-1/5) and "
                        + "|d_t r_s(t)|<=C_K*t^(-Re(s)-3/2)*t^(-1/5).")),
                    Paragraph(Text(
                        "The derivative passes under an integral on a fixed "
                        + "compact triangle. Both the normalized coefficient "
                        + "and its derivative have uniform bounds there. "
                        + "The product rule is applied only after subtracting "
                        + "the exact coefficient 1/2. Local boundedness of the "
                        + "explicit parameter constants then gives the compact "
                        + "uniform estimates."))),
                DescribeRole.Theorem))));
}
