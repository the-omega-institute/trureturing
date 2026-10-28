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
