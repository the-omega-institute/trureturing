using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class PowerfulFibonacciSupportBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/PowerfulFibonacciSupportBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite original odd-depth support bounds powerful Fibonacci indices.",
        H("Powerful Fibonacci support bound"),
        Blocks(
            Paragraph(Text(
                "Fix a finite set S of primes greater than five and its least Fibonacci "
                    + "rank closure H(S). The theorem establishes the count using "
                    + "the prime-index nonsquare theorem, the five-adic depth law, "
                    + "prime-to-index valuation, and Fibonacci square-class rigidity. "
                    + "Its only parameter condition is that S consists of primes "
                    + "greater than five.")),
            Describe.Lean(
                DescribeId.Create("odd-prime-support"),
                DeclarationHandle.Create(Prefix + "oddPrimeSupport"),
                H("Odd prime support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The distinct prime factors of the original Fibonacci value F_n "
                        + "whose valuations in F_n are odd."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("supported-powerful-index"),
                DeclarationHandle.Create(Prefix + "supportedPowerfulIndex"),
                H("Supported powerful index"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A positive index n belongs when F_n is powerful and every prime "
                        + "factor of F_n with odd original depth at least three belongs "
                        + "to S. The condition uses the first Fibonacci zero rank of "
                        + "each prime, not the depth at a multiplied index."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("powerful-fibonacci-support-bound"),
                DeclarationHandle.Create(Prefix + "powerful_fibonacci_support_bound"),
                H("Finite count with four exceptions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There is a finite set "
                        + "containing exactly the supported powerful indices, with "
                        + "cardinality at most two to the size of H(S) minus four. "
                        + "The proof places every odd prime support inside H(S), "
                        + "uses the index-support descent to reduce small odd support "
                        + "to five-smooth indices, proves their powerful-value "
                        + "classification, and injects all remaining indices "
                        + "into the subsets of H(S) outside the eight small supports. "
                        + "The small group contributes at most four indices."))),
                DescribeRole.Theorem)),
        []));
}
