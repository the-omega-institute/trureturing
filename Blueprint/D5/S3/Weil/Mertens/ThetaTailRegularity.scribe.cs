using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class ThetaTailRegularityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/ThetaTailRegularity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual activation-weighted theta tail has a uniform modulus and quantitative L1 peak control.",
        H("Quantitative regularity of the actual theta tail"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("theta-tail-lipschitz"),
                DeclarationHandle.Create(Prefix + "theta_tail_lipschitz"),
                H("A uniform modulus on the closed half-line"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use the actual functions q(u)=exp(-u)*(theta(exp(u))-exp(u)), "
                    + "k(u)=q(u)*(u+1)/u^2 and f(u)=-integral(k(v),v>u) from "
                    + "ActualThetaTailLaplace. Pinned Mathlib supplies theta(x)>=0 and "
                    + "theta(x)<=log(4)*x for x>=0. Since log(4)=2*log(2)<=2, "
                    + "these imply abs(q(u))<=1. On u>=1, the nonnegative factor "
                    + "(u+1)/u^2 is at most 2, hence abs(k(u))<=2. Absolute "
                    + "integrability of k comes from the existing actual-tail theorem. "
                    + "Subtracting its convergent tails and bounding the interval integral "
                    + "therefore proves abs(f(u)-f(v))<=2*abs(u-v) for all u,v>=1, "
                    + "including the endpoint 1. This implies the constant 4 modulus "
                    + "required for the quantitative Hankel localizer. No differentiability "
                    + "of the arithmetic step function at primes is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("theta-tail-peak-mass"),
                DeclarationHandle.Create(Prefix + "theta_tail_peak_sq_le_mass"),
                H("A right-hand triangle below each positive peak"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For U>=1 and a>=U put F=f(a)>0 and M_U=integral(abs(f(u)),u>U). "
                    + "The existing actual-tail theorem supplies finiteness of M_U. "
                    + "On [a,a+F/2] the modulus gives f(u)>=F-2*(u-a), "
                    + "so abs(f(u)) is at least this affine function. Its interval "
                    + "integral is F^2/4. The interval (a,a+F/2] lies in (U,infinity) "
                    + "even when a=U, and monotonicity of the nonnegative integral "
                    + "gives F^2<=4*M_U. Thus F^2<=8*M_U and F<=sqrt(8*M_U) "
                    + "follow as well. No sign condition away from this interval is used. "
                    + "This is an unconditional analytic prerequisite; it asserts neither "
                    + "existence of a positive tail peak nor the Riemann hypothesis."))),
                DescribeRole.Theorem))));
}
