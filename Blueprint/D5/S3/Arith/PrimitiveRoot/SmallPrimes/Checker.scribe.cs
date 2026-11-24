using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimitiveRoot.SmallPrimes;

internal sealed class SmallPrimeCheckerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/PrimitiveRoot/SmallPrimes/Checker.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kernel certificates for small prime primitive roots",
        H("Kernel certificates for small prime primitive roots"), Blocks(
            Describe.Lean(DescribeId.Create("small-prime-slot-soundness"),
                DeclarationHandle.Create(Prefix + "checkPrime_sound"),
                H("Soundness of a primitive-root slot"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "A successful checkPrime certificate supplies a prime q below p whose " +
                    "multiplicative order in ZMod p is exactly p−1. Primality proofs for q " +
                    "and the supplied factors are shared kernel-checked constants. No " +
                    "primality assumption on p is needed for this order statement.")),
                Paragraph(Text(
                    "Repeated division ending at one proves that every prime divisor of " +
                    "p−1 occurs among the supplied prime factors. Modular repeated squaring " +
                    "computes a returning power and excludes the exponent (p−1)/l for every " +
                    "such factor l. Mathlib orderOf_eq_of_pow_and_pow_div_prime then gives " +
                    "the exact order. The modular exponentiation recursion is structural; " +
                    "its residual branch preserves exactness even when fuel is exhausted. " +
                    "The supplied literals are checked inside Lean; their external " +
                    "generator and transport files are outside the proof boundary."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("small-prime-lucas-primality"),
                DeclarationHandle.Create(Prefix + "checkPrime_prime"),
                H("A successful slot also certifies primality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A successful checkPrime certificate also proves p prime. The full " +
                    "returning power and the prime-divisor power exclusions meet " +
                    "Mathlib's Lucas primality criterion. This conclusion supplies " +
                    "primality proofs for larger shared literal prime constants from " +
                    "already certified smaller factors, so each factor's primality " +
                    "need not be checked again at every occurrence."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("small-prime-block-append"),
                DeclarationHandle.Create(Prefix + "checkBlock_append"),
                H("Concatenation preserves certified coverage"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A checked block of n slots starting at start concatenates with " +
                    "a checked block of m slots starting at start+2n to give a checked " +
                    "block of n+m slots. Both lengths and the second block's precise " +
                    "offset are retained. Shared sub-block proofs therefore establish " +
                    "the full literal block without repeating their kernel computation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("small-prime-block-soundness"),
                DeclarationHandle.Create(Prefix + "checkBlock_sound"),
                H("Coverage of every checked odd slot"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "If checkBlock start count rows succeeds, then every prime at " +
                    "start+2k for k<count has a smaller prime primitive root. The checker " +
                    "verifies the list length as well as every consecutive slot. A " +
                    "composite slot contains a divisor strictly between one and the slot " +
                    "value, so primality excludes that alternative. A prime slot applies " +
                    "the preceding order theorem. Consequently neither a missing suffix " +
                    "nor an empty list can certify a positive-length interval.")),
                Paragraph(Text(
                    "The independent obligation is the finite premise of Erdős #985: " +
                    "every prime between three and 3483482 has a smaller prime primitive " +
                    "root. Literal block-success theorems are checking-success proofs, " +
                    "and their conclusions are consumed by the finite-range theorem, " +
                    "which is in turn consumed by erdos985_of_finiteHeight. They are checker " +
                    "instances, rather than independent positive enumeration claims."))),
                DescribeRole.Theorem))));
}
