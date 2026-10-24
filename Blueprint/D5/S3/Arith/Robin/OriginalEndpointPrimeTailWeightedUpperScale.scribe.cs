using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalEndpointPrimeTailWeightedUpperScaleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted-price control and an explicit square-root logarithmic bound for the complete original endpoint tail.",
        H("The complete original endpoint tail has a matching upper scale"),
        Blocks(
            Paragraph(Text(
                "Keep any real q>0, either original endpoint N=strictInteger(q) or N=maximalInteger(q), "
                + "u=largestPrime(N), and the complete T=tail(N), including every original support prime, "
                + "all positive exponents and all activation ties.")),
            Describe.Lean(
                DescribeId.Create("actual-endpoint-complete-tail-weighted-upper-scale"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/OriginalEndpointPrimeTailWeightedUpperScale.endpoint_tail_le_nine_log4_sqrt_log"),
                H("An explicit upper bound on the square-root logarithmic scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For u>=4, T<=9log(4)/(sqrt(u)log(u)). The original sharp local price upper bound "
                        + "is at most 2qlog(p), by the nonnegative factorization "
                        + "(p-1)z^2-(pz-1)=(z-1)((p-1)z-1), z=exp(qlog(p)). The actual largest "
                        + "selected prime gives q<=1/(u log(u)). At r=2sqrt(u), the original small-prime "
                        + "sum is therefore at most 4log(4)/(sqrt(u)log(u)), using Chebyshev theta. "
                        + "Finite dyadic bands bound the remaining reciprocal-square sum; the existing "
                        + "complete-layer bound 5/(4p^2) pays at most another "
                        + "5log(4)/(sqrt(u)log(u)). Every boundary and final partial band is retained.")),
                    Paragraph(Text(
                        "Together with the existing positive complete-tail lower bound, this identifies "
                        + "the same endpoint tail's inverse square-root logarithmic scale. No density or "
                        + "PNT premise is supplied. The Mertens and logarithmic-clock terms in the exact "
                        + "original Robin residual still require joint sign control; this upper estimate "
                        + "does not prove the full Robin inequality or RH."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-higher-exponent-complete-tail-two-thirds-scale"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/OriginalEndpointPrimeTailWeightedUpperScale.endpoint_higher_tail_le_eight_log4_rpow"),
                H("The actual higher-exponent part decays on the two-thirds scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the same q>0, original endpoint and u>=4, sum the complete layerTail(N,p) "
                    + "over exactly the actual support primes with factorization exponent at least two. "
                    + "This sum is at most 8log(4)/(u^(2/3)log(u)). At r=2u^(1/3), weighted price "
                    + "and theta control pay at most 4log(4)/(u^(2/3)log(u)) for the small part. "
                    + "On the large part the existing elementary logarithm remainder gives "
                    + "layerTail<=9/(8p^3); since p>r, reuse the finite reciprocal-square band "
                    + "bound with one extra factor 1/r. This pays 27log(4)/(8u^(2/3)log(u)); "
                    + "the resulting coefficient 59/8 is at most eight. The subset is the endpoint's "
                    + "actual exponent classification, and each retained summand is its complete "
                    + "original local Euler tail. No exponent cap, density hypothesis, replaced "
                    + "integer or final Robin sign is supplied. The remaining Robin residual "
                    + "terms and RH remain open."))),
                DescribeRole.Theorem))));
}
