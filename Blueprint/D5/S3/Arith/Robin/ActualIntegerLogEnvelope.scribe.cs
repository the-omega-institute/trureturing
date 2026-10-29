using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualIntegerLogEnvelopeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ActualIntegerLogEnvelope.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed-price integer comparator removes the large-prime split error in the actual Robin objective.",
        H("Actual Integer Logarithmic Envelope"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("supported-sigma-bound"),
                DeclarationHandle.Create(Prefix + "supported_sigma_bound"),
                H("A finite prime-support bound for the actual sigma ratio"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive natural integer U and every real x, if each prime "
                        + "factor p of U satisfies p<=x, then sigma(1,U)/U is at most the product "
                        + "of (1-1/p)^(-1) over primes in the natural interval (0,floor(x)]. "
                        + "Prime-power reconstruction and the multiplicative sigma formula "
                        + "express the ratio as finite geometric factors. Each factor is bounded "
                        + "by (1-1/p)^(-1); GronwallUpperEnvelope.small_prime_product_le pads "
                        + "the product to the full prime interval.")),
                    Paragraph(Text(
                        "The coefficient-two envelope applies this bound to its positive "
                        + "fixed-price comparator U. AbundancyRecord5040.large_prime_of_abundancy "
                        + "applies it directly with U=m and x=30: if every prime factor is at "
                        + "most thirty, padding further to all integers from two through thirty "
                        + "telescopes to thirty, contradicting sigma(1,m)/m>30."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-integer-arbitrary-error-envelope"),
                DeclarationHandle.Create(Prefix + "eventual_actual_integer_envelope_epsilon"),
                H("An arbitrary positive inventory error"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every epsilon>0 there is A>=286 such that every positive actual "
                    + "integer n with log(n)>=A satisfies F(n)-gamma<=(19/10+epsilon)/log(log(n)). "
                    + "The comparator has strict layer counts at price 1/(X*log(X)), X=log(n). "
                    + "Its uniform inventory growth gives 1-log(U)/X<=epsilon. The exact "
                    + "fixed-price cost difference is (1-log(U)/X)/log(X). Combining this with "
                    + "the effective prime-product coefficient 19/10 proves the bound. Only U "
                    + "has smooth support. The coefficient-two theorem takes epsilon=1/10; "
                    + "ActualLeastCrossingPriceRecord takes epsilon=1/20 directly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-integer-small-error-envelope"),
                DeclarationHandle.Create(Prefix + "eventual_actual_integer_envelope_small_error"),
                H("An arbitrarily small coefficient for every sufficiently large actual integer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real epsilon>0 there exists a real A>=286 such that every "
                        + "positive natural integer n with A<=log(n) satisfies "
                        + "originalObjective(n)-gamma<=epsilon/log(log(n)). The threshold A "
                        + "is chosen before n. The original objective and actual integer n are "
                        + "unchanged, and n has no support or optimizer hypothesis.")),
                    Paragraph(Text(
                        "CenteredTail.E2p_isLittleO_inv_log bounds E₂p(X) above by "
                        + "(epsilon/2)/log(X) eventually. The original inequality -E₂p(X)<=E₃(X) "
                        + "and exact prime-product identity then bound the reciprocal product by "
                        + "exp(gamma)*log(X)*exp((epsilon/2)/log(X)). Set X=log(n). At price "
                        + "1/(X*log(X)), the strict comparator U has all prime support below X "
                        + "and uniform inventory growth gives 1-log(U)/X<=epsilon/2.")),
                    Paragraph(Text(
                        "The same private fixed-price transfer used by the existing "
                        + "19/10+epsilon theorem bounds the comparator's logarithmic sigma ratio "
                        + "and transfers it to n, adding at most (epsilon/2)/log(X). The two "
                        + "halves sum to epsilon/log(X). This is an unconditional vanishing "
                        + "upper coefficient, with no rate asserted for the threshold; it proves "
                        + "neither a signed nonpositive bound, Robin's inequality, nor RH."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-integer-coefficient-two-envelope"),
                DeclarationHandle.Create(Prefix + "eventual_actual_integer_envelope"),
                H("An unconditional coefficient-two bound for every sufficiently large integer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is a real A>=286 such that every positive natural integer n "
                        + "with A<=log(n) satisfies originalObjective(n)-gamma<=2/log(log(n)). "
                        + "Here originalObjective(n)=log(sigma(1,n)/n)-log(log(log(n))) "
                        + "and gamma is the Euler-Mascheroni constant. The integer n is arbitrary; "
                        + "no smoothness or optimality assumption is imposed on it.")),
                    Paragraph(Text(
                        "Put X=log(n) and lambda=1/(X*log(X)). The actual positive integer U "
                        + "from GoldenResourceOptimalLayerCount.optimal_layer_count_spec has "
                        + "the strict exponent counts at lambda and maximizes W(k)-lambda*log(k) "
                        + "over all positive natural integers k, where W(k)=log(sigma(1,k)/k). "
                        + "EulerLayerInventoryGrowth.active_power_bound, at the first layer, "
                        + "implies every prime factor of U is less than X. Only this comparator "
                        + "uses the support bound. The full finite geometric Euler factors, "
                        + "padded by GronwallUpperEnvelope.small_prime_product_le, then give "
                        + "sigma(1,U)/U at most the reciprocal prime product up to X.")),
                    Paragraph(Text(
                        "MertensExplicitEnvelope.prime_product_upper_effective supplies "
                        + "W(U)<=gamma+log(log(X))+19/(10*log(X)). The uniform strict-inventory "
                        + "growth theorem with epsilon=1/10 gives 1-log(U)/X<=1/10. Global "
                        + "fixed-price comparison transfers the bound to n and adds at most "
                        + "1/(10*log(X)), yielding coefficient two. All prime powers in U are "
                        + "retained. This deduction combines the existing arithmetic inputs "
                        + "without a literature priority claim. In ActualIntegerHeightJump the "
                        + "bound is applied at the actual divisor m/q, after proving its size.")),
                    Paragraph(Text(
                        "The estimate is unconditional and uses the existing unconditional "
                        + "MediumPNT through strict-inventory growth. It proves neither Robin's "
                        + "inequality nor RH, and supplies no signed upper bound or bounded-height "
                        + "cofinal envelope."))),
                DescribeRole.Theorem))));
}
