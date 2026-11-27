using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class AllSupportRobinCostDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact decomposition of the Robin margin for arbitrary prime support.",
        H("Robin margin for arbitrary prime support"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("all-support-robin-cost"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/AllSupportRobinCost.robin_margin_eq_all_support_ledger"),
                H("Exact prime-cost and correction identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive integer n with log n at least 2, the Robin log margin is "
                    + "the sum of the prime cost at log n, the signed theta tail and three "
                    + "nonnegative corrections. The valuation defect uses the union of the "
                    + "occupied primes and the primes up to log n. A missing prime has valuation "
                    + "zero, so it can still supply a positive contribution to the cost. "
                    + "The other terms account for the logarithmic remainder and omitted Euler factors."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("all-support-robin-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/AllSupportRobinCost.robin_margin_ge_prime_cost_add_theta_tail"),
                H("A lower bound for the Robin margin"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The prime cost and signed theta tail give a lower bound for the log margin "
                    + "at the literal height log n. The bound applies to every integer in the "
                    + "stated range, including supports with gaps."))),
                DescribeRole.Theorem))));
}
