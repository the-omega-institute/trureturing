using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenLargestPrimePeriodIterationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The largest prime above five loses exactly its original Fibonacci depth at each period iteration.",
        H("Largest-prime period iteration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-largest-prime-period-iteration"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenLargestPrimePeriodIteration.golden_largest_prime_period_iteration"),
                H("Exact depth loss for every positive modulus"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let m be positive and let P greater than five be its largest "
                    + "prime divisor. Write a for the P-adic valuation of m and h_P "
                    + "for the P-adic valuation of the Fibonacci number at the first "
                    + "positive index divisible by P. For every n at least zero, the "
                    + "P-adic valuation of the n-th iterate of the Fibonacci matrix "
                    + "period is a minus n times h_P, truncated at zero. The prime P "
                    + "divides that iterate exactly when n is less than the ceiling "
                    + "of a divided by h_P. Thus P first disappears at that ceiling "
                    + "and never returns. Every positive fixed point of the period "
                    + "function has no prime divisor greater than five. If the "
                    + "periods of m and m squared agree, then h_P is at least twice a. "
                    + "The theorem does not classify the remaining fixed points or "
                    + "bound the total time until an iterate becomes fixed."))),
                DescribeRole.Theorem))));
}
