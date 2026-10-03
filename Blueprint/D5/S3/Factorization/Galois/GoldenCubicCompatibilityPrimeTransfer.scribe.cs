using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class GoldenCubicCompatibilityPrimeTransferDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual rational-prime Frobenius event matches the compositum Chebotarev event away from ramification.",
        H("Golden Cubic Prime Transfer"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-cubic-compatibility-prime-transfer"),
            DeclarationHandle.Create(
                "D5/S3/Factorization/Galois/GoldenCubicCompatibilityPrimeTransfer.actual_prime_transfer_data"),
            H("Forward and reverse arithmetic Frobenius transfer"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A rational prime in the specified unit residue class admits a prime of the "
                    + "cubic cyclotomic base and a prime of the actual radical field above it with "
                    + "the character-defined arithmetic Frobenius exactly when its prime ideal "
                    + "has the selected rational Frobenius class, away from ramification. The proof "
                    + "constructs lifts and transports arithmetic Frobenius in both directions "
                    + "through the rational, cubic-base, radical and compositum towers.")),
                Paragraph(Text(
                    "The rational-prime set and the Chebotarev prime-ideal set therefore agree "
                    + "after excluding ramified primes. The statement retains the same actual "
                    + "earlier support, roots, residue and automorphisms as the compositum."))),
            DescribeRole.Theorem))));
}
