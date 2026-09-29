using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciFiveAdicRankBudgetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd Fibonacci support bounds five-adic index depth by the rank budget plus one.",
        H("Five-Adic Fibonacci Rank Budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-five-adic-rank-budget"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/FibonacciFiveAdicRankBudget.fibonacci_five_adic_rank_budget"),
                H("Five-adic rank budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let H be a finite set of primes containing five, and let R be "
                    + "the least common multiple of their first Fibonacci entry ranks. "
                    + "If every prime dividing a positive index n belongs to H and "
                    + "every prime occurring to odd order in F_n belongs to H, then "
                    + "the exponent of five in n is at most one more than the exponent "
                    + "of five in R. A nonsquare normalized quotient at the odd index "
                    + "5^a has an odd-order prime whose entry rank exceeds 5^a. "
                    + "The prime-to-index valuation law carries that odd order to F_n, "
                    + "contradicting the support assumption when the index is too deep."))),
                DescribeRole.Theorem))));
}
