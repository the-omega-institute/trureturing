using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualFactorialRobinHighSignDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual full odd high q-component has a natural limit with a strictly negative prime-three margin.",
        H("Strict Sign of the Actual Odd High Component"),
        Blocks(
            Paragraph(Text(
                "Keep the original signed factorial residual eta and its cumulative mass "
                + "C(y)=integral from 1 to y of eta(z)/z^2. Keep h(r) as the literal "
                + "highRemainder(r) and q(r)=h(r)-h(r+log(2))/2. The high prefix is "
                + "exactly the natural exclusive sum over odd 3<=m<N of mu(m)*q(log(m))/m.")),
            Describe.Lean(
                DescribeId.Create("actual-factorial-robin-high-sign"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualFactorialRobinHighSign.result"),
                H("Natural convergence with a strict quantitative sign"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is a real Q to which these exact natural prefixes tend, "
                        + "and Q<=-q(log(3))/3<0. This is ordinary sequential convergence; "
                        + "the final real q-family is not asserted absolutely summable.")),
                    Paragraph(Text(
                        "The positive Laplace transport uses Ahat(t)=integral over y>1 "
                        + "of C(y)*exp(-t*log(y))/y. For every t>0, "
                        + "0<Ahat(t)<=2/t. Define nu(t)=t*(1+t)*(1-exp(-t*log(2))/2)*Ahat(t); "
                        + "then 0<nu(t)<=2*(1+t), and the literal q(r) equals "
                        + "the integral over t>0 of nu(t)*exp(-r*t) for each r>0. "
                        + "The Gamma kernel is t*(1+t), and the nonnegative joint integral "
                        + "is integrable before any signed arithmetic is introduced. "
                        + "The original positive_representation_y is applied at its owner; "
                        + "eta is never replaced by a positive envelope.")),
                    Paragraph(Text(
                        "C's original finite anchored Abel theorem includes its terminal term. "
                        + "Applied with lower anchor 2 and odd harmonic prefix equal to 1, "
                        + "it gives |S_N(t)|<=3*exp(-t*log(3)) for every natural N; "
                        + "N<=3 is the empty prefix. Thus nu(t)*S_N(t) is dominated by "
                        + "6*(1+t)*exp(-t*log(3)), integrable on the entire positive axis.")),
                    Paragraph(Text(
                        "For each fixed t>0 only, absolute Dirichlet convergence is used. "
                        + "The principal character modulo 2 has exactly the odd coefficients. "
                        + "Mathlib's LSeries.mul_mu_eq_one gives Z_o(1+t)*E_o(t)=1. "
                        + "Z_o contains every power 3^j, so its positive sum is at least "
                        + "1/(1-3^(-1-t)). This retains E_o(t)-1<=-3^(-1-t). "
                        + "Exact real-cast and cpow/rpow bridges connect the supplier "
                        + "to the natural finite exponential prefixes. Finite integral "
                        + "linearity and natural dominated convergence give the displayed "
                        + "bound on Q without signed absolute Fubini for the q-family.")),
                    Paragraph(Text(
                        "Suppliers: ActualFactorialCumulativePositivity, original "
                        + "ActualOddHarmonicMobiusTail and ActualFactorialRobinHighWeight; "
                        + "Mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d "
                        + "provides Gamma, Tonelli, DCT, Dirichlet inversion and geometric sums. "
                        + "These classical helpers are consumed, with no priority claim. "
                        + "The signed factorial suppliers retain their original Terence Tao "
                        + "and Apache 2.0 attribution at LogConvolutionMassExpansion. "
                        + "The local OpenAI/math revision adc7f1241b42e322a6451854ab7e4b4c146bf78a "
                        + "was searched; its right-half-plane character estimates do not "
                        + "supply this actual strict high sign.")),
                    Paragraph(Text(
                        "The full target Ipsi(log(n))+R(log(n))+d_n>0 for every n>5040 "
                        + "remains separate. The actual unit m=1, lowPrimitive, both "
                        + "clipping boundaries, finite terminal correction and pressure "
                        + "are not discharged by this high-component sign. In particular "
                        + "the finite cutoff correction must be retained when using it "
                        + "in the full pairing."))),
                DescribeRole.Theorem))));
}
