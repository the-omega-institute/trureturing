using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualBalancedExtremizerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/ActualBalancedExtremizer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An original Robin failure yields an attained minimum and a unique optimizer at the same integer's internal price.",
        H("An attained Robin minimum at its own price"),
        Blocks(
            Paragraph(Text("Retain the existing original margin S(n)=gamma+log(log(log(n)))-log(sigma(n)/n), the actual price lambda=1/(log(N)*log(log(N))), and the original objective Phi_lambda(m)=log(sigma(m)/m)-lambda*log(m). The latter is exactly goldenResourceObjective on every positive integer by golden_resource_sigma_identity. No proxy integer or independently optimized price is substituted.")),
            Describe.Lean(
                DescribeId.Create("actual-failure-unique-internal-optimizer"),
                DeclarationHandle.Create(Prefix + "failure_has_unique_internal_optimizer"),
                H("The same attained failure uniquely optimizes over all positive integers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The only hypothesis is an actual natural n>5040 with S(n)<=0. The conclusion gives an actual N>55440 with S(N)<=0 and S(N)<=S(m) for all m>5040. At its own positive price lambda, below the existing boundaryPrice, this same N is globally optimal and strictly beats every other positive integer. It equals both strictInteger(lambda) and maximalInteger(lambda); lambda differs from every goldenLayerMarginal(p,k) for prime p and k>=1.")),
                    Paragraph(Text("Attainment uses gronwall_upper_envelope with epsilon=exp(-b)-1>0 for b<0, ratio positivity, and robin_log_margin_eq_neg_log to get a genuine eventual bound S(n)>=b. If c<0 is witnessed, b=c/2 excludes the tail and a nonempty finite initial segment supplies the global minimum. If no negative value exists, the given nonpositive witness itself is a minimum. No inference from a bare real-valued liminf and no boundedness premise is used.")),
                    Paragraph(Text("For m>5040 different from N, the existing RestrictedDivisorStrictInventory.loglog_tangent from LogarithmBounds gives strict tangent support at log(N); its kernel ActualRobinClockCovariance.g is definitionally the same as price. Combining it with margin minimality gives Phi_lambda(m)<Phi_lambda(N), including distinct equal-margin integers. FewDistinctPrimes.robin_lt_223092870 and the existing margin/ratio bridge exclude 5040<N<=55440. The existing boundaryCap_eq_55440 proof is reused through its original proof, without copying its arithmetic into this proof. Neither log-log concavity nor its tangent inequality is reproved.")),
                    Paragraph(Text("Let B=boundaryCap=maximalInteger(boundaryPrice). Its existing positive-price global optimizer specification, strict support at B, and log(B)<log(N) imply lambda<boundaryPrice. For 1<=m<=5040<B, boundary optimality and (boundaryPrice-lambda)*(log(m)-log(B))<0 give Phi_lambda(m)<Phi_lambda(B)<Phi_lambda(N). This includes m=1 and uses no iterated logarithm at a small integer. Full-domain uniqueness then identifies the existing strict and maximal inventories; their exact layer membership equivalences exclude all equality layers, including simultaneous ties.")),
                    Paragraph(Text("The classical minimum-to-CA mechanism overlaps Caveney--Nicolas--Sondow, On SA, CA, and GA numbers, arXiv:1112.6010v2, section 2; no novelty claim is made. No endpoint Robin signs, divisible-GA2 witness, signed-integral estimate, or RH conclusion is supplied by this reduction."))),
                DescribeRole.Theorem))));
}
