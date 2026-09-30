using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciRankBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite rank-closed odd valuation support bounds the entire Fibonacci index.",
        H("Complete Fibonacci Rank Budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-rank-budget"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/FibonacciRankBudget.fibonacci_rank_budget"),
                H("Every prime depth is bounded"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H be a finite set of primes containing two, three, and five. "
                            + "Assume that every prime factor of the first Fibonacci entry "
                            + "rank of a member of H also belongs to H, and let R be the "
                            + "least common multiple of those ranks. If every prime occurring "
                            + "to odd order in F_n belongs to H, for a positive index n, "
                            + "then n divides 5R. At every prime other than five the depth "
                            + "of n is at most its depth in R; at five one extra unit is allowed.")),
                    Paragraph(Text(
                        "Support descent first places every index prime in H. An excessive "
                            + "depth e at a prime q at least seven produces an odd-order "
                            + "factor p of the nonsquare quotient F_(q^e)/F_(q^(e-1)). "
                            + "Its exact entry rank q^e excludes it from H and from the index. "
                            + "The original-rank valuation law preserves its odd order in F_n, "
                            + "contradicting the support condition. The two-, three-, and "
                            + "five-adic budgets supply the remaining cases.")),
                    Paragraph(Text(
                        "The support assumption concerns odd valuations, so primes of even "
                            + "positive depth in F_n may lie outside H. The conclusion bounds "
                            + "indices for this fixed support set; it does not assert that "
                            + "every Fibonacci value has its prime support in a fixed finite set."))),
                DescribeRole.Theorem))));
}
