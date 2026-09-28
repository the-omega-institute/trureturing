using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciDyadicRankBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd Fibonacci support bounds the dyadic depth of an index by the ranks in its finite prime support.",
        H("Dyadic Fibonacci rank budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-dyadic-rank-budget"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/FibonacciDyadicRankBudget.fibonacci_dyadic_rank_budget"),
                H("Dyadic rank budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let H be a finite set of primes containing three, and let R be "
                    + "the least common multiple of their first Fibonacci entry ranks. "
                    + "If every prime dividing a positive index n belongs to H and "
                    + "every prime occurring to odd order in F_n belongs to H, then "
                    + "the exponent of two in n is at most the exponent of two in R. "
                    + "A nonsquare dyadic Fibonacci quotient yields an odd-order prime "
                    + "at the first rank 2^e; its valuation is transported to F_n using "
                    + "the prime-to-index valuation theorem."))),
                DescribeRole.Theorem))));
}
