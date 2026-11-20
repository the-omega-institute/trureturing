using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicPrimitiveTernaryPrimeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime divisors of a third cyclotomic factor supply exact ternary orders for the Lucas residue clock.",
        H("Primitive ternary primes for the Lucas residue clock"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lucas-primitive-ternary-prime-for-nine"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/GoldenCubicPrimitiveTernaryPrime.exists_prime_orderOf_nine"),
                H("Every positive power of three is the exact order of nine at some prime"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose a prime factor of the third cyclotomic polynomial evaluated at "
                    + "the preceding ternary power of nine. The geometric-sum identity bounds "
                    + "the order; collapsing to the preceding power would force the prime "
                    + "to divide three. The witness prime is outside two, three, and five."))),
                DescribeRole.Theorem))));
}
