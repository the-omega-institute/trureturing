using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciTernaryRankBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd Fibonacci support bounds the ternary depth of an index by ranks in its finite prime support.",
        H("Ternary Fibonacci rank budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-ternary-rank-budget"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/FibonacciTernaryRankBudget.fibonacci_ternary_rank_budget"),
                H("Ternary rank budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let H be a finite set of primes containing two, and let R be "
                    + "the least common multiple of their first Fibonacci entry ranks. "
                    + "If every prime dividing a positive index n belongs to H and "
                    + "every prime occurring to odd order in F_n belongs to H, then "
                    + "the exponent of three in n is at most the exponent of three in R. "
                    + "At a larger exponent, a cubic Fibonacci block is two modulo five "
                    + "and yields an odd-order prime of exact rank 3^e. Its original "
                    + "valuation is transported to F_n through the prime-to-index theorem."))),
                DescribeRole.Theorem))));
}
