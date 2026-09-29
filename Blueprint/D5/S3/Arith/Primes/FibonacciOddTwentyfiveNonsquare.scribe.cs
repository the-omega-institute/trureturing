using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciOddTwentyfiveNonsquareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd-index normalized twenty-five-fold Fibonacci quotients are nonsquares modulo seven.",
        H("Odd-Index Fibonacci Quotients Modulo Seven"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-odd-twentyfive-nonsquare"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/FibonacciOddTwentyfiveNonsquare.fibonacci_odd_twentyfive_normalized_nonsquare"),
                H("The normalized twenty-five-fold quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each positive odd index n, the Fibonacci number F_(25n) equals "
                    + "25 times F_n times a natural number d. This d is five modulo seven "
                    + "and therefore is not a square. An eight-step sign change of the "
                    + "Fibonacci sequence modulo seven supplies the residue; the exact "
                    + "five-adic depth supplies the factor of twenty-five."))),
                DescribeRole.Theorem))));
}
