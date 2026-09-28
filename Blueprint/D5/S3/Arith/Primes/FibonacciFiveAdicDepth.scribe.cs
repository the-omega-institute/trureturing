using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciFiveAdicDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive index, the five-adic Fibonacci depth equals the index depth.",
        H("Five-adic Fibonacci depth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-five-adic-depth"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/FibonacciFiveAdicDepth.fibonacci_five_adic_depth"),
                H("Exact five-adic depth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive n, the exponent of five in F_n equals the "
                    + "exponent of five in n. The proof computes the fifth power of "
                    + "the golden integer phi^n: its Fibonacci coordinate gains one "
                    + "factor of five, while the remaining factor is a unit modulo "
                    + "five by the norm equation. The Fibonacci entry point at five "
                    + "starts the induction."))),
                DescribeRole.Theorem))));
}
