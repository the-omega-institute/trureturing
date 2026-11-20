using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class ModularOrbitPrimePowerFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime-power rules at the canonical factorization determine the complete finite orbit at each positive modulus.",
        H("Exact orbit laws from canonical prime-power factors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("modular-orbit-canonical-collisions"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/ModularOrbitPrimePowerFactorization.canonical_modulus_collision"),
                H("Canonical exact collision law at every positive modulus"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use each support prime at its exact exponent in the modulus. "
                    + "The prime powers are pairwise coprime, and their product is the "
                    + "modulus. The result also covers modulus one via the empty list."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("modular-orbit-canonical-residue-count"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/ModularOrbitPrimePowerFactorization.canonical_modulus_residue_count"),
                H("Exact cardinality of the residue image at every positive modulus"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cardinality is exactly the maximum prime-power transient plus "
                    + "the least common multiple of the prime-power periods."))),
                DescribeRole.Theorem))));
}
