using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class LogarithmicLayerRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual distinct primes in shrinking relative windows supply growing finite exchanges.",
        H("Shrinking Prime Windows for Logarithmic Layer Rigidity"),
        Blocks(Describe.Lean(
            DescribeId.Create("logarithmic-layer-shrinking-prime-windows"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Robin/PriceRecord/LogarithmicLayerRigidity.shrinking_prime_windows"),
            H("Growing prime capacity"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For every fixed real C>0 there is a threshold T>1 such that, for every "
                        + "real x>=T and every natural N<=ceil(C*log(x)^3), both intervals "
                        + "(x*(1-1/log(x)^3),x] and (x,x*(1+1/log(x)^3)] contain finite "
                        + "sets of exactly N distinct primes. The threshold precedes both x "
                        + "and N. In particular, N may grow with x at this rate.")),
                Paragraph(Text(
                    "MediumPNT supplies the unconditional psi error with remainder "
                        + "x*exp(-c*log(x)^(1/10)), for some c>0. Combining it with "
                        + "Chebyshev.isBigO_psi_sub_theta_sqrt gives "
                        + "theta(x)-x=o(x/log(x)^8). The proof uses the actual exponent "
                        + "1/10, without a stronger remainder or a short-interval hypothesis.")),
                Paragraph(Text(
                    "For y between x/2 and 2*x, log(y)>=log(x)/2 once x>=4. The eventual "
                        + "theta error is therefore at most 512*x/log(x)^8 at either endpoint. "
                        + "The theta increment across either requested window is at least "
                        + "x/(2*log(x)^3). Each prime contributes at most 2*log(x), so "
                        + "the interval contains at least x/(4*log(x)^4) primes. This "
                        + "eventually exceeds ceil(C*log(x)^3). The proof identifies the "
                        + "interval with a difference of actual primesLE finite sets and "
                        + "extracts a subset of the requested cardinality.")),
                Paragraph(Text(
                    "This prime-capacity theorem is an input to logarithmic finite prime "
                        + "exchanges. It does not assert the second-order layer law. That "
                        + "law still requires simultaneous rounded cardinalities, strict "
                        + "product feasibility, two-sided gain reversal, and a uniform "
                        + "asymptotic extraction on the literal full predecessor-record "
                        + "family. The Riemann hypothesis, Robin's inequality beyond 5040, "
                        + "and the signed budget for the same original integer remain open. "
                        + "No claim of literature novelty is made.")),
                Paragraph(Text(
                    "The full target keeps j>=2 and epsilon>0 before the threshold, and "
                        + "keeps that threshold before every m>=2, lambda>0, and literal "
                        + "strict predecessor record. With P=largestPrime(m) and "
                        + "Q=layerPrime(m,j), its conclusion is "
                        + "abs(log(P)*(Q^j/(j*P)-1)+log(j))<epsilon. "
                        + "The existing first-order ratio theorem cannot supply this rate "
                        + "by choosing a tolerance that depends on P.")),
                Paragraph(Text(
                    "The intended finite exchange uses r growing as a cubic logarithm. "
                        + "For the lower direction, a count s below "
                        + "r*log(P_low)/log(Q_high) enforces product(U)<product(D). "
                        + "For the upper direction, a count s above "
                        + "r*log(P_high)/log(Q_low) enforces the reverse assignment's "
                        + "strict product budget. The natural choices ceil(z)-1 and "
                        + "floor(z)+1 remain strict when z is integral. These count "
                        + "constructions, the actual-record gain comparisons, and their "
                        + "uniform error bounds are not asserted by the prime-capacity "
                        + "theorem."))),
            DescribeRole.Theorem))));
}
