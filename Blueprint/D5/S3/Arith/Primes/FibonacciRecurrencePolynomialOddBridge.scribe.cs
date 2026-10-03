using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciRecurrencePolynomialOddBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The odd-index Fibonacci quotient bridge for the recurrence polynomial.",
        H("Odd-Index Fibonacci Recurrence Bridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-recurrence-polynomial-odd-bridge"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/FibonacciRecurrencePolynomialOddBridge.odd_fibonacci_recurrence_bridge"),
                H("Odd-index recurrence bridge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an odd positive index n and every natural m, "
                    + "the Fibonacci recurrence polynomial U_m evaluated at "
                    + "the Lucas number L_n satisfies F_n U_m(L_n) = F_(mn), "
                    + "and the rational quotient F_(mn)/F_n equals the same "
                    + "polynomial value. The identity follows from the "
                    + "quadratic relation for the nth power of the golden "
                    + "generator and its Fibonacci coordinate recurrence."))),
                DescribeRole.Theorem))));
}
