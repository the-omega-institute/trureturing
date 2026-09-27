using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class PrimePowerFibonacciQuotientPeriodDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fresh prime factors of prime-power Fibonacci quotients have exact matrix periods.",
        H("Prime-Power Fibonacci Quotient Period"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-power-fibonacci-quotient-period"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/PrimePowerFibonacciQuotientPeriod.prime_power_fibonacci_quotient_period"),
                H("Exact fourfold period of a fresh prime factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let p be a prime greater than five and let q be any prime "
                    + "factor of F_(p^(k+1))/F_(p^k). The Fibonacci matrix modulo q "
                    + "has multiplicative order exactly 4p^(k+1). Its first zero "
                    + "index is p^(k+1), so every return time is a multiple of "
                    + "that index. Cassini's identity makes the matrix at that "
                    + "index square to minus one, excluding the shorter returns "
                    + "while its fourth power is one."))),
                DescribeRole.Theorem))));
}
