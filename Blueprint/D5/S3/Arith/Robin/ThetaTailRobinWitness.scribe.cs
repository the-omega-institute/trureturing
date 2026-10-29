using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ThetaTailRobinWitnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual weighted Chebyshev theta tail equals the normalized second Mertens error and gives an explicit prefix-lcm Robin response.",
        H("The actual theta tail and a strict Robin response"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("theta-tail-mertens-robin"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ThetaTailRobinWitness.theta_tail_mertens_robin"),
                H("The improper integral and its arithmetic consequence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real x>=2 the actual function (theta(t)-t)*w(t), where "
                        + "w(t)=(log(t)+1)/(t²*log(t)²), is Lebesgue integrable on (x,infinity). "
                        + "Its negative integral is E₂p(x)-(theta(x)-x)/(x*log(x)). "
                        + "Here theta is the Chebyshev prime sum and E₂p is the second Mertens error "
                        + "with Mertens.M as its constant.")),
                    Paragraph(Text(
                        "Write I(x)=(theta(x)-x)/(x*log(x))-E₂p(x). Classical finite Abel summation "
                        + "gives I(u)=I(x)-integral_x^u (theta(t)-t)*w(t) dt. The finite calculation "
                        + "reuses the canonical ThetaTailPartialSummation.theta_tail_finite supplier "
                        + "from MertensCumulativePeak; its reciprocal logarithmic weight and "
                        + "prime-cutoff identities provide the finite bridge. "
                        + "The elementary bound 0<=theta(u)<=u*log(4), together with "
                        + "|E₂p(u)|<=(log(4)+6+Mertens.E₁)/log(u), proves I(u) tends to zero. "
                        + "ActualThetaTailLaplace supplies unconditional integrability of the same actual kernel. "
                        + "Taking the upper limit to infinity therefore fixes the normalization and proves the equality.")),
                    Paragraph(Text(
                        "For x>=10000, suppose this negative integral exceeds 7/sqrt(x). "
                        + "The Mertens correction E₃(x)+E₂p(x) has absolute value at most 4/x<=1/sqrt(x), "
                        + "and (psi(x)-theta(x))/(x*log(x))<=2/sqrt(x). These bounds give "
                        + "E₃(x)<-4/sqrt(x)-(psi(x)-x)/(x*log(x)). The common prefix-lcm response "
                        + "in LcmRobinResponse applies at this same real x.")),
                    Paragraph(Text(
                        "The resulting integer is exactly D=lcm(1,...,floor(x)). It satisfies "
                        + "D>5040, sigma(D)/D>exp(gamma)*log(log(D)), log(D)=psi(x), and "
                        + "D<=exp(x*log(x)), where gamma is the real Euler constant. "
                        + "The implication requires the stated actual tail peak; no existence of such a peak "
                        + "or conclusion about zeros of the zeta function is asserted."))),
                DescribeRole.Theorem))));
}
