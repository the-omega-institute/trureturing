using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicBlockPrimePeriodsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime factors of the two golden cubic blocks have exact Fibonacci matrix periods.",
        H("Golden Cubic Block Prime Periods"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-b-prime-period"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicBlockPrimePeriods.cubic_block_b_prime_period"),
                H("The Lucas block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For j at least one, every prime factor p of L_(3^j)^2 + 3 "
                    + "has Fibonacci matrix period exactly 2 times 3^(j+1). "
                    + "The Lucas value at 3^(j+1) vanishes modulo p. The "
                    + "quadratic trace and norm identity then makes the golden "
                    + "generator return at twice that index; its first Fibonacci "
                    + "zero rules out an earlier return."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-c-prime-period"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicBlockPrimePeriods.cubic_block_c_prime_period"),
                H("The Fibonacci block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For j at least one, every prime factor p of L_(3^j)^2 + 1 "
                    + "has Fibonacci matrix period exactly 4 times 3^(j+1). "
                    + "At the first Fibonacci zero, the golden generator squares "
                    + "to minus one by Cassini's identity. The block is odd, so "
                    + "minus one is not one modulo p; its residual order is four."))),
                DescribeRole.Theorem))));
}
