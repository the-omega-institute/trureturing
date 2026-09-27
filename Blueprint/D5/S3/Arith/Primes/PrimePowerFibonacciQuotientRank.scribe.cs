using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class PrimePowerFibonacciQuotientRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consecutive prime-power Fibonacci indices have fresh prime support.",
        H("Prime-Power Fibonacci Quotient Rank"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-power-fibonacci-quotient-rank"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/PrimePowerFibonacciQuotientRank.prime_power_fibonacci_quotient_rank"),
                H("First-entry rank of quotient prime factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let p be a prime greater than five. The quotient of "
                    + "F_(p^(k+1)) by F_(p^k) exceeds one for every k at least zero. "
                    + "Every prime dividing this quotient has first Fibonacci "
                    + "zero index exactly p^(k+1). The proof first excludes p "
                    + "from F_(p^(k+1)) using the prime rank bound. Any other "
                    + "prime with an earlier rank would divide both Fibonacci "
                    + "values. Its prime-to-index valuations would then be equal, "
                    + "contradicting its additional occurrence in the quotient."))),
                DescribeRole.Theorem))));
}
