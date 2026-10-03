using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciRecurrencePolynomialThirdCoefficientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The third near-leading coefficient of the Fibonacci recurrence polynomial.",
        H("Fibonacci Recurrence Polynomial Third Coefficient"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-recurrence-polynomial-third-coefficient"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/FibonacciRecurrencePolynomialThirdCoefficient.fibonacci_recurrence_polynomial_third_coefficient"),
                H("Third near-leading coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the recurrence U_0=0, U_1=1, and "
                    + "U_(m+2)=X U_(m+1)+U_m, the coefficient of X^n in "
                    + "U_(n+5) is the binomial coefficient choose(n+2,2). "
                    + "Equivalently, for m at least five this is the third "
                    + "near-leading coefficient at degree m-5, equal to "
                    + "(m-3)(m-4)/2."))),
                DescribeRole.Theorem))));
}
