using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class RestrictedDivisorStrictInventoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/RestrictedDivisorStrictInventory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual nonlinear maxima on a forced divisor domain have strict own-clock layer counts.",
        H("Restricted Integer Maxima and the Terminal Inventory Chain"),
        Blocks(
            Paragraph(Text(
                "The objective is exactly log(sigma(n)/n)-log(log(log(n))). "
                + "The prime layer marginal is the existing goldenLayerMarginal, and "
                + "price(t)=1/(t*log(t)). Equal-price layers are excluded by "
                + "optimalLayerCount. The core remains a positive natural integer; "
                + "a real clock is never substituted for an original prime label.")),
            Describe.Lean(
                DescribeId.Create("restricted-divisor-own-clock-inventory"),
                DeclarationHandle.Create(Prefix + "restricted_divisor_maximum_strict_inventory"),
                H("Classification of every constrained nonlinear maximum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be prime, m and V positive, and let W be a positive "
                        + "multiple of m dividing V. Assume p does not divide V, "
                        + "log(p*m)>1, and log(p*V)<a. At the parent clock a, every "
                        + "prime's first layer above its V exponent has marginal "
                        + "at most price(a). Every occupied mandatory m layer is "
                        + "strictly active already at log(p*m). If p*W maximizes "
                        + "the literal original objective over all positive p*U "
                        + "with m dividing U and U dividing V, then every natural "
                        + "direction q has W.factorization(q) equal to "
                        + "optimalLayerCount(price(log(p*W)),q). Nonprime directions "
                        + "and zero exponent stacks are included.")),
                    Paragraph(Text(
                        "When a stack is below the V exponent, inserting its next "
                        + "layer is legal. The actual single-prime objective delta "
                        + "and a strict log-log tangent inequality put its marginal "
                        + "strictly below the own-clock price. In a saturated stack, "
                        + "the weak inactive bound at the larger parent clock "
                        + "becomes strict because the literal price decreases. "
                        + "A layer can be deleted only above the mandatory m floor; "
                        + "deleting the top occupied layer then puts its marginal "
                        + "strictly above the own-clock price. Mandatory layers "
                        + "are handled by their stated earlier-clock activation. "
                        + "The existing active-layer interval theorem identifies "
                        + "the complete strict count. No deletion of an internal "
                        + "prime layer is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("terminal-5040-divisor-certificate-reduction"),
                DeclarationHandle.Create(Prefix + "strict_5040_divisor_comparison_iff_inventory"),
                H("An exact reduction of the strict divisor certificate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be prime with p<P, let V be positive, "
                        + "and suppose p does not divide V. Assume "
                        + "log(p*5040)>=243 and every prime's next layer above "
                        + "its V exponent is inactive at log(P*V). Then p*V "
                        + "strictly beats every p*U with positive proper divisor "
                        + "U of V divisible by 5040 if and only if it strictly "
                        + "beats those same proper divisors whose exponents obey "
                        + "the strict inventory law at their own log(p*U). "
                        + "The certificate compares actual integer objective values.")),
                    Paragraph(Text(
                        "The comparison family itself requires 5040 dividing "
                        + "every competitor U. A separate 5040-divisibility "
                        + "premise on V is unnecessary for this equivalence; "
                        + "it holds even for an empty proper-competitor family. "
                        + "The actual terminal application has 5040 dividing V.")),
                    Paragraph(Text(
                        "If any proper divisor ties or beats V, choose a maximum "
                        + "over the finite proper-divisor domain. Its value also "
                        + "beats V, so it maximizes over the complete divisor domain. "
                        + "The classification theorem puts this proper maximum "
                        + "in the inventory family and contradicts the proposed "
                        + "strict comparisons. This retains exact ties without "
                        + "assuming a least full-domain maximizer. The mandatory "
                        + "5040 activation is derived from the existing global "
                        + "fixed-price optimum at 1/25 and the earlier clock "
                        + "at least 243; its bottom layers are never deleted.")),
                    Paragraph(Text(
                        "For the actual terminal source P*V, a strict inventory "
                        + "law for V at log(P*V) supplies the displayed inactive "
                        + "next-layer premise. Taking p to be the immediate "
                        + "previous complete label gives the finite certificate "
                        + "family used in the ordinary terminal comparison. The "
                        + "identity F(p*V)-F(p*U)=beta(U)-J(U) still requires "
                        + "strictly positive margins. Neither this reduction "
                        + "nor the classification proves those margins, a heat-scale "
                        + "upper gap between a_good and a_full, a fixed positive "
                        + "terminal reserve, the complete signed prime budget, "
                        + "Robin's inequality or the Riemann hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-full-domain-forced-prime-inventory"),
                DeclarationHandle.Create(Prefix + "original_maximum_strict_inventory"),
                H("Every original maximizing tie has the residual strict inventory"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be prime and let N satisfy the literal "
                        + "OriginalFirstClockTransport.originalMaximizes(p,N): "
                        + "N is positive, 5040*p divides N, and N maximizes "
                        + "originalObjective over every positive multiple of "
                        + "5040*p. Assume exactly 243<=log(N)<p. Then "
                        + "N.factorization(p)=1, and there is a positive natural "
                        + "integer U with N=p*U, 5040 dividing U, p not dividing "
                        + "U, and U.factorization(q)=optimalLayerCount("
                        + "ActualRobinClockCovariance.g(log(N)),q) for every "
                        + "natural q. The clock remains log(N), rather than "
                        + "log(U). The result applies to every maximizing tie; "
                        + "no least-source choice or attainment supplier is assumed.")),
                    Paragraph(Text(
                        "For every prime q, N*q is again a positive multiple "
                        + "of 5040*p. Its exact prime_delta and the existing "
                        + "strict loglog_tangent inequality force the next "
                        + "N layer strictly below the price at log(N). To "
                        + "delete a top q layer, its exponent must exceed "
                        + "the factorization of the entire mandatory floor "
                        + "5040*p. Factorization subtraction then proves "
                        + "5040*p divides N/q, so this is an actual legal "
                        + "competitor. Its floor also keeps log(N/q)>1. The "
                        + "same strict tangent, taken at log(N), forces the "
                        + "removed layer strictly above that same price. "
                        + "Weak maximality is sufficient for both strict "
                        + "comparisons, including objective ties.")),
                    Paragraph(Text(
                        "Since p>log(N)>=243, the prime p is not a divisor "
                        + "of 5040, and its mandatory floor exponent is one. "
                        + "The existing reciprocal-power marginal bound and "
                        + "strict price decrease put even its first layer "
                        + "below the own-clock price. Strict marginal decrease "
                        + "therefore makes every higher p layer inactive. "
                        + "A p exponent at least two would permit deleting "
                        + "its top layer and contradict the strict deletion "
                        + "comparison. Hence precisely one p is removed "
                        + "to construct U, preserving every mandatory 5040 layer.")),
                    Paragraph(Text(
                        "For q different from p, N and U have identical "
                        + "q exponents. Their next residual layer is strictly "
                        + "inactive by legal insertion into N. An occupied "
                        + "residual top layer above the 5040 floor is strictly "
                        + "active by legal deletion from N. At the floor it "
                        + "is active by the existing forced_5040_active "
                        + "argument at log(N)>=243. For q=p the residual "
                        + "stack is empty and its first layer is inactive. "
                        + "The strict active-layer interval identifies each "
                        + "count, including absent prime stacks. Nonprime "
                        + "directions have zero factorization and zero "
                        + "optimalLayerCount by their definitions; no "
                        + "prime-power stack or equality endpoint is omitted.")),
                    Paragraph(Text(
                        "This bridge derives the inventory from original "
                        + "nonlinear maximality. It assumes no inventory law, "
                        + "forced exponent-one premise, fixed-price optimality, "
                        + "analytic supplier or MAIN upper bound. Existence "
                        + "of such an original maximizer and the displayed "
                        + "clock window remain separate obligations. The "
                        + "bridge alone supplies neither the JC18 initial "
                        + "arithmetic-height payment nor the complete signed "
                        + "prime budget, strict Robin inequality or RH."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Repository derivation reuses the original integer objective, "
                + "the single-prime objective delta, the strict active-layer "
                + "count interval and literal price monotonicity. A search of "
                + "the repository, pinned Mathlib and the public Robin1984 "
                + "CAProfile/CAReduction sources found fixed-price Euler "
                + "thresholds and Robin reduction, but no matching constrained "
                + "nonlinear divisor-maximum classification. No literature "
                + "priority claim is made.")))));
}
