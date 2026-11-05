using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class ActualThetaTailLaplaceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/ActualThetaTailLaplace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual theta error gives an absolutely integrable activation-weighted signed tail.",
        H("Actual theta signed tails"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-theta-tail-laplace-ode"),
                DeclarationHandle.Create(Prefix + "actual_theta_tail_laplace_ode"),
                H("Absolute convergence, complex moments and the cutoff Laplace equation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Put u0=log(2). The function q(u)=exp(-u)*(theta(exp(u))-exp(u)) "
                        + "is the actual Chebyshev theta error in logarithmic coordinates. "
                        + "Its absolute integral on u>u0 is finite. To prove this, the unconditional "
                        + "integrability of (psi(t)-t)/t^2 is combined with the nonnegative "
                        + "prime-power difference psi(t)-theta(t)<=C*sqrt(t). Dividing this "
                        + "difference by t^2 gives an integrable t^(-3/2) majorant on t>1. "
                        + "The exponential change of variables, with Jacobian exp(u), then "
                        + "proves the asserted zero-frequency absolute convergence of q.")),
                    Paragraph(Text(
                        "Define k(u)=q(u)*(u+1)/u^2 and f(u)=-integral(k(v),v>u). "
                        + "The factor (u+1)/u^2 is nonnegative and bounded on u>=u0 by "
                        + "(u0+1)/u0^2, so k is absolutely integrable there. In the original "
                        + "variable let F(x)=-integral((theta(t)-t)*activationDensity(t),t>x), "
                        + "with the exact activationDensity(t)=(log(t)+1)/(t^2*log(t)^2). "
                        + "For every U>=u0 this original integrand is absolutely integrable "
                        + "on t>exp(U). The identity f(u)=F(exp(u)) follows from the genuine "
                        + "Lebesgue exponential substitution, including its Jacobian. "
                        + "No regularity of the arithmetic step function at primes is assumed.")),
                    Paragraph(Text(
                        "Fubini applies to k(v) times the indicator of u0<u<=v. Integrating in u "
                        + "gives (v-u0)*abs(k(v))<=(1+1/u0)*abs(q(v)), proving f is absolutely "
                        + "integrable. Its absolute value is bounded by the absolute integral of k, "
                        + "and f tends to zero at infinity. On every [a,b] with u0<=a<=b, "
                        + "splitting convergent tails gives f(u)=f(a)+integral(k(v),v=a..u). "
                        + "Thus f is locally absolutely continuous, and Lebesgue differentiation "
                        + "gives f-prime(u)=k(u) almost everywhere above u0.")),
                    Paragraph(Text(
                        "For every U>=u0 the actual complex transform L(U,s) is analytic on "
                        + "Re(s)>0. Every polynomial moment of exp(-s*u)*f(u) is absolutely "
                        + "integrable on u>U. A positive exponential margin dominates derivatives "
                        + "in a complex neighborhood: L-prime is minus the first moment and "
                        + "the derivative of L-prime is the positive second moment. "
                        + "These are complex derivatives on the full open half-plane.")),
                    Paragraph(Text(
                        "Almost everywhere u^2*f-prime(u)=(u+1)*q(u). For Re(s)>0, integrate "
                        + "u^2*exp(-s*u)*f-prime(u) by parts on [U,T], using absolute "
                        + "continuity of f and the smooth complex factor. Real and imaginary "
                        + "parts satisfy the real absolute-continuity formula. The derivative "
                        + "of u^2*exp(-s*u) is (2*u-s*u^2)*exp(-s*u). Boundedness of f "
                        + "and polynomial-exponential decay make the endpoint at T vanish "
                        + "as T tends to infinity. The convergent actual Q and its first moment "
                        + "are the theta transform and derivative from ThetaLaplaceContinuation.")),
                    Paragraph(Text(
                        "Consequently, for every U>=log(2) and every complex s with Re(s)>0, "
                        + "s*L-second(U,s)+2*L-prime(U,s)=-Q-prime(U,s)+Q(U,s)"
                        + "+U^2*f(U)*exp(-s*U). The cutoff term has a positive sign on the "
                        + "right side. No vanishing of f(U) is asserted or needed. All integrals "
                        + "and derivatives refer to the actual theta function and the exact "
                        + "activation density. The equation is on the convergence half-plane; "
                        + "continuation of L to a negative half-plane and the Riemann hypothesis "
                        + "are separate questions."))),
                DescribeRole.Theorem))));
}
