using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciPrimeToIndexValuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/FibonacciPrimeToIndexValuation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At a prime absent from the index, Fibonacci valuation equals the depth at its first zero.",
        H("Prime-to-index Fibonacci valuation"),
        Blocks(
            Paragraph(Text(
                "Let p be prime and p divide F_n while p does not divide n. Its original "
                    + "entry rank is the least positive r for which p divides F_r.")),
            Describe.Lean(
                DescribeId.Create("original-rank-valuation"),
                DeclarationHandle.Create(Prefix + "fibonacci_original_rank_valuation"),
                H("Original rank valuation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The p-adic valuations of F_n and F_r agree. The proof factors the "
                        + "golden-power Fibonacci coordinate into F_r and an integral "
                        + "quotient. Modulo p that quotient is the index multiplier times "
                        + "a power of the adjacent Fibonacci coordinate, so p does not "
                        + "divide it when p divides neither the multiplier nor that "
                        + "adjacent coordinate."))),
                DescribeRole.Theorem)),
        []));
}
