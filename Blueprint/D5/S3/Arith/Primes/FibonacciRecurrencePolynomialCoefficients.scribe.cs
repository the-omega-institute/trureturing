using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciRecurrencePolynomialCoefficientsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first two nonzero coefficient layers of the Fibonacci recurrence polynomial.",
        H("Fibonacci Recurrence Polynomial Coefficients"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-recurrence-polynomial-coefficients"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/FibonacciRecurrencePolynomialCoefficients.fibonacci_recurrence_polynomial_coefficients"),
                H("Near-leading coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Define U_0=0 and U_1=1, with U_(m+2)=X U_(m+1)+U_m. "
                    + "For every m at least one, U_m has degree m-1 and leading "
                    + "coefficient one. For every m at least three, the coefficient "
                    + "at X^(m-3) equals m-2. Thus at each odd index q=2r+1 "
                    + "with r at least one, this coefficient is the odd number q-2."))),
                DescribeRole.Theorem))));
}
