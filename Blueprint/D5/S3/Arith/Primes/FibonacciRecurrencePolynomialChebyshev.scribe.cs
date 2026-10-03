using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciRecurrencePolynomialChebyshevDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The plus-recurrence polynomial is represented by a complex-scaled Chebyshev polynomial of the second kind.",
        H("Chebyshev Representation of the Recurrence Polynomial"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-recurrence-polynomial-chebyshev"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/FibonacciRecurrencePolynomialChebyshev.fibonacci_recurrence_polynomial_chebyshev"),
                H("Complex Chebyshev bridge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural k, mapping the integer recurrence polynomial at index k+1 into the complex polynomial ring gives "
                    + "(-i)^k times the Chebyshev U polynomial at index k, composed with the variable iX/2."))),
                DescribeRole.Theorem))));
}
