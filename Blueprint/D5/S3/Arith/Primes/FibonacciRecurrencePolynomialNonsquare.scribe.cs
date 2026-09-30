using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciRecurrencePolynomialNonsquareDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All higher odd prime-power Fibonacci quotients are positive nonsquares beyond an explicit prime threshold.",
        H("Nonsquares in Higher Odd Prime-Power Layers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-recurrence-polynomial-nonsquare"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/FibonacciRecurrencePolynomialNonsquare.fibonacci_recurrence_polynomial_nonsquare"),
                H("An analytic obstruction for recurrence polynomials and Fibonacci quotients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For r at least 119, the recurrence polynomial U_(2r+1) takes a nonsquare value at every "
                    + "integer x greater than two satisfying x^2 - 4 > 128 times 6^r. Pairing its complex "
                    + "roots yields factors X^2 + lambda_i with 0 at most lambda_i less than four. Reversing "
                    + "and contracting the recurrence polynomial produces an integral polynomial whose linear "
                    + "coefficient is odd. The half-binomial expansion then has odd dyadic coefficient "
                    + "numerators; its analytic square-root branch obeys a Cauchy coefficient bound. The "
                    + "dyadic analytic integer obstruction excludes an integer square root. For every odd n at "
                    + "least 2r+1, the Fibonacci quotient F_((2r+1)n)/F_n is positive and nonsquare. In "
                    + "particular, for every prime q at least 239 and every k at least one, "
                    + "F_(q^(k+1))/F_(q^k) is positive and nonsquare."))),
                DescribeRole.Theorem))));
}
