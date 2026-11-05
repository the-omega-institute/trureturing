using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalEndpointFirstLayerBandDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/OriginalEndpointFirstLayerBand.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First-layer prime bands and quantitative lower bounds for the complete original endpoint tail.",
        H("Original endpoint first-layer bands"),
        Blocks(
            Paragraph(Text(
                "For each real q>0, retain either original endpoint N=strictInteger(q) or N=maximalInteger(q). "
                + "Write u=largestPrime(N), a_p=N.factorization(p), m(p,k)=goldenLayerMarginal(p,k), "
                + "and T=tail(N)=sum over every p in N.primeFactors of -log(1-p^(-(a_p+1))). "
                + "The integer, complete support, higher layers and all simultaneous activation ties are retained. "
                + "Every lower bound below concerns this same complete T.")),
            Describe.Lean(
                DescribeId.Create("actual-endpoint-omitted-prime-price-lower"),
                DeclarationHandle.Create(Prefix + "endpoint_price_lower_of_largest"),
                H("The endpoint's own omitted prime bounds its price"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For either actual endpoint, q>0 and u>=2 imply "
                    + "1/((2u+1)log(2u))<=q. Bertrand supplies a prime v with u<v<=2u, "
                    + "so v is absent from this endpoint and its omitted first layer satisfies m(v,1)<=q. "
                    + "The existing lower logarithm estimate gives "
                    + "m(v,1)>=1/((v+1)log(v)); positive-factor monotonicity pays the displayed bound. "
                    + "No price cutoff is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-endpoint-exact-first-layer-band"),
                DeclarationHandle.Create(Prefix + "endpoint_first_layer_band"),
                H("Every prime from twice the square root to the largest prime has one layer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For q>0, either original endpoint, u>=2 and every prime p with 2sqrt(u)<=p<=u, "
                    + "the theorem gives p in N.primeFactors and a_p=1. "
                    + "The actual endpoint classifiers and first-layer prime antitonicity supply the support inclusion. "
                    + "The omitted-prime price bound and the existing second-marginal estimate give "
                    + "m(p,2)<=1/(p^2 log(p))<q. The denominator gap is strict even at p=2sqrt(u), "
                    + "so the second layer is excluded under both strict and maximal tie conventions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-endpoint-bertrand-complete-tail-lower"),
                DeclarationHandle.Create(Prefix + "endpoint_tail_gt_inv_sixteen_mul_largest"),
                H("A Bertrand witness gives a strict lower bound for the complete tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For either actual endpoint at every q>0, u>=16 implies T>1/(16u). "
                    + "Bertrand applied at floor(2sqrt(u)) supplies a prime with "
                    + "2sqrt(u)<p<=4sqrt(u)<=u. Its actual exponent is one, hence its tail is "
                    + "-log(1-p^-2)>p^-2>=1/(16u). Every other prime and layer stays in T "
                    + "with a nonnegative contribution; the witness does not replace the original support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-endpoint-complete-tail-theta-band"),
                DeclarationHandle.Create(Prefix + "endpoint_tail_ge_theta_band"),
                H("The complete tail controls the actual theta mass of a first-layer band"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For q>0, either original endpoint and u>=2, every real band "
                    + "2sqrt(u)<=A<=B<=u satisfies T>=(theta(B)-theta(A))/(B^2 log(B)). "
                    + "The exact theta difference is the sum of log(p) over all actual primes A<p<=B. "
                    + "Every such prime has exponent one, and its tail is at least "
                    + "log(p)/(B^2 log(B)). The complete complementary tail remains nonnegative. "
                    + "An empty band is allowed; no prime-density or final-sign premise is supplied."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-endpoint-explicit-chebyshev-tail-lower"),
                DeclarationHandle.Create(Prefix + "endpoint_tail_ge_chebyshev"),
                H("Existing Chebyshev estimates supply an explicit bound from u>=64"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Put s=sqrt(u) and E(u)=(4s-1)log(2)-log(8s+2)-2sqrt(8s)log(8s). "
                    + "For either original endpoint at every q>0, u>=64 implies "
                    + "T>=max(0,E(u))/(64u log(8sqrt(u))). The threshold ensures "
                    + "(2sqrt(u),8sqrt(u)] lies inside the actual first-layer support band. "
                    + "The existing Chebyshev lower bound at 8sqrt(u), upper bound at 2sqrt(u), "
                    + "and theta monotonicity pay the numerator. The maximum with zero "
                    + "does not assume that the explicit expression is positive at small u."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-endpoint-square-root-logarithmic-tail-lower"),
                DeclarationHandle.Create(Prefix + "endpoint_tail_ge_sqrt_log"),
                H("A positive lower bound on the square-root logarithmic scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For either original endpoint at every q>0, u>=2^22 implies "
                        + "T>=log(2)/(32sqrt(u)log(8sqrt(u))). The constants are paid "
                        + "by proving E(u)>=2sqrt(u)log(2), using only elementary logarithm "
                        + "bounds and square-root identities. This consumes the preceding explicit "
                        + "Chebyshev bound and supplies the positive 1/(sqrt(u)log(u)) scale "
                        + "for this same integer's complete Euler tail.")),
                    Paragraph(Text(
                        "The original residual remains margin(N)=E3(u)+T+log(log(log(N)))-log(log(u)). "
                        + "A positive quantitative lower bound for T does not establish the joint "
                        + "sign of these terms. The full all-price original Robin endpoint sign "
                        + "and the corresponding RH conclusion remain unpaid; none is a premise "
                        + "or a conclusion of the tail estimates."))),
                DescribeRole.Theorem))));
}
