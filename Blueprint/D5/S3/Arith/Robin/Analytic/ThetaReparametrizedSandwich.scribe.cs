using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

internal sealed class ThetaReparametrizedSandwichDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual theta tail traps arithmetic B at the original and theta-reparametrized endpoints.",
        H("Actual theta-reparametrized sandwich"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-theta-reparametrized-sandwich"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/Analytic/ThetaReparametrizedSandwich.actual_theta_reparametrized_sandwich"),
                H("The full pointwise sandwich with its finite correction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real x with 2<x and 2<Chebyshev.theta(x), put "
                        + "K(x)=-ActualThetaTailLaplace.F(x) and H(x)=Mertens.E₃(x)+Mertens.E₂p(x). "
                        + "Then K(Chebyshev.theta(x))+H(x)<=RHSharpArithmeticEnvelope.B(x), and "
                        + "RHSharpArithmeticEnvelope.B(x)<=K(x)+H(x). The two endpoints may occur "
                        + "in either order or coincide. The finite correction H is retained literally.")),
                    Paragraph(Text(
                        "Here w(t)=(log(t)+1)/(t²*log(t)²) is ActualRobinClockCovariance.activationDensity, "
                        + "g(t)=1/(t*log(t)), and K(x)=integral_(t>x) (Chebyshev.theta(t)-t)*w(t). "
                        + "The arithmetic quantity is B(x)=Mertens.E₃(x)+log(log(Chebyshev.theta(x))) "
                        + "-log(log(x)). With N(x)=log(log(Chebyshev.theta(x)))-log(log(x)) "
                        + "-(Chebyshev.theta(x)-x)/(x*log(x)), the actual Mertens identity gives "
                        + "B(x)=K(x)+H(x)+N(x).")),
                    Paragraph(Text(
                        "For a,b>1, the derivative of (b-t)*g(t)+log(log(t)) is -(b-t)*w(t). "
                        + "The original derivative g'=-w and the oriented fundamental theorem of "
                        + "calculus therefore give log(log(b))-log(log(a))-(b-a)/(a*log(a)) "
                        + "=-integral_(a..b) (b-t)*w(t). Apply this with a=x and b=Chebyshev.theta(x), "
                        + "and subtract the two integrable actual tails. The exact telescope is "
                        + "K(x)+N(x)-K(Chebyshev.theta(x))="
                        + "integral_(x..Chebyshev.theta(x)) (Chebyshev.theta(t)-Chebyshev.theta(x))*w(t).")),
                    Paragraph(Text(
                        "If x<=Chebyshev.theta(x), theta monotonicity makes the integrand nonnegative "
                        + "on the forward interval. If Chebyshev.theta(x)<=x, the integrand is "
                        + "nonpositive on the reversed interval, and reversing orientation changes "
                        + "its sign. Thus the telescope is nonnegative in both orders. The original "
                        + "loglog_tangent_gap_quadratic supplies N(x)<=0. These two signs and the "
                        + "literal B decomposition give the lower and upper inequalities respectively. "
                        + "No derivative or continuity of theta at a prime is used. This is a pointwise "
                        + "statement and asserts no limiting theorem or RH conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-theta-tail-local-modulus"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/ThetaReparametrizedSandwich.actual_theta_tail_local_modulus"),
                H("Local displacement of the actual theta tail"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all sufficiently large u and every v≥u, the absolute "
                    + "change of the signed weighted tail is at most 2(v−u)/(u log(u))."))),
                DescribeRole.Theorem))));
}
