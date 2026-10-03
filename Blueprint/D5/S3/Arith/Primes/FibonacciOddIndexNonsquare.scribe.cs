using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciOddIndexNonsquareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Lucas modulus supplies a quadratic obstruction for every nontrivial odd Fibonacci index.",
        H("Odd-Index Fibonacci Nonsquares"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-odd-index-nonsquare"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/FibonacciOddIndexNonsquare.fibonacci_odd_index_nonsquare"),
                H("Every odd index at least three is excluded"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every odd natural number m at least three, F_m is not a square. "
                            + "Write m as 4t plus or minus one and factor t as 2^r times an odd s. "
                            + "The Lucas modulus L_(2^(r+1)) is positive and is three modulo four.")),
                    Paragraph(Text(
                        "In the golden integer ring, the trace and norm of phi^(2^(r+1)) "
                            + "give phi^(2^(r+2)) equal to minus one modulo this modulus. "
                            + "The odd factor s preserves that sign. The golden coordinate "
                            + "in the plus case, or the constant coordinate after multiplication "
                            + "by phi in the minus case, gives F_m equal to minus one modulo "
                            + "the same Lucas number.")),
                    Paragraph(Text(
                        "The Jacobi symbol of minus one is minus one for a modulus equal "
                            + "to three modulo four. Therefore F_m cannot be a square. "
                            + "This applies to initial odd prime indices; it does not assert "
                            + "a classification of squares at even indices or a nonsquare "
                            + "criterion for arbitrary ratios of Fibonacci numbers."))),
                DescribeRole.Theorem))));
}
