using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciDyadicQuotientNonsquareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyadic Fibonacci quotients from k = 1 have nonsquare residues modulo five.",
        H("Dyadic Fibonacci Quotients from k = 1"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-dyadic-quotient-nonsquare"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/FibonacciDyadicQuotientNonsquare.fibonacci_dyadic_quotient_nonsquare"),
                H("Nonsquare quotients for k at least one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every k at least one, the integer quotient of F_(2^(k+1)) "
                    + "by F_(2^k) is 3 modulo five when k is one, and 2 modulo "
                    + "five at every later layer. Hence none of these quotients "
                    + "is a square. Fibonacci-Lucas doubling identifies each "
                    + "quotient with L_(2^k); Lucas doubling makes residue two "
                    + "a fixed point along the later powers of two."))),
                DescribeRole.Theorem))));
}
