using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciRecurrencePolynomialOddParityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd-index plus-recurrence polynomials are even after complexification.",
        H("Opposite-Root Symmetry at Odd Order"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-recurrence-polynomial-odd-parity"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/FibonacciRecurrencePolynomialOddParity.odd_recurrence_polynomial_even"),
                H("Odd-index parity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural r and complex z, evaluating the complexification of the "
                    + "recurrence polynomial at index 2r+1 at -z gives the same value as evaluating it at z. "
                    + "Thus complex roots occur in opposite pairs."))),
                DescribeRole.Theorem))));
}
