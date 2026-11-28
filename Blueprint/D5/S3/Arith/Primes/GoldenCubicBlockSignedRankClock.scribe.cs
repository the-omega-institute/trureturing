using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenCubicBlockSignedRankClockDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native cubic Lucas orbit has a sharp transient and period at every positive modulus.",
        H("Exact native cubic Lucas orbits modulo every integer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-cubic-canonical-odd-prime-period"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock.canonical_prime_power_period"),
                H("Fibonacci rank yields the exact signed period"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Away from two, three, and five the three-primary part of the Fibonacci rank "
                    + "sets the exact transient length. A single global sign modulo the rank "
                    + "core times a power of the prime gives the period."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-all-moduli-collision"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock.native_modulus_collision"),
                H("All collisions at every positive integer modulus"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The transient is the maximum of the prime-power transients. The period "
                    + "is the least common multiple of the prime-power periods. Distinct "
                    + "indices coincide if and only if the earlier index is past the transient "
                    + "and the period divides the lag."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-all-moduli-residue-count"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock.native_modulus_residue_count"),
                H("Exactly the transient plus one cycle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact number of attained residues is the transient length plus one "
                    + "period, including modulus one. The entire initial transient and first "
                    + "cycle are representatives with no repetition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-cubic-thirteen-precision-regression"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenCubicBlockSignedRankClock.native_thirteen_periods"),
                H("The period doubles at thirteen"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The native period is three modulo thirteen and six modulo one hundred "
                    + "sixty-nine. Squaring the sign test modulo the composite rank modulus "
                    + "would incorrectly keep period three."))),
                DescribeRole.Theorem))));
}
