using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciPrimeStepLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An odd prime divisor of a Fibonacci value gains exactly one valuation digit when it multiplies the positive index.",
        H("Fibonacci valuation at an odd-prime index step"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-prime-step-binomial-remainder"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/FibonacciPrimeStepLift.prime_first_order"),
                H("Binomial expansion with a divisible quadratic remainder"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Over any commutative ring, expand the p-th power of a plus b times z, "
                    + "where p is an odd prime and its image divides b. After removing the "
                    + "constant and linear terms, the remainder is divisible by p times b squared. "
                    + "The intermediate binomial coefficients provide the prime factor; in the "
                    + "last term, the factor comes from b."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fibonacci-native-odd-prime-step"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/FibonacciPrimeStepLift.fibonacci_valuation_prime_step"),
                H("One additional digit in the native Fibonacci valuation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If an odd prime p divides the Fibonacci value at positive index r, then "
                    + "its valuation at index p times r is exactly one more. In the golden "
                    + "integer ring, the quotient of the new Fibonacci coordinate by p times "
                    + "the old coordinate reduces to a nonzero power of the preceding Fibonacci "
                    + "value modulo p. This uses no split-prime hypothesis and does not determine "
                    + "the valuation at the first zero index."))),
                DescribeRole.Theorem))));
}
