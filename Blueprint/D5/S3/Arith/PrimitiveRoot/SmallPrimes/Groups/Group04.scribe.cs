using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Groups;

internal sealed class SmallPrimeGroup04Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consecutive odd-slot certificate group 4",
        H("Consecutive odd-slot certificate group 4"), Blocks(
            Describe.Lean(DescribeId.Create("small-prime-group-04-sound"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimitiveRoot/SmallPrimes/Groups/Group04.group04_sound"),
                H("Every prime in the group has a smaller prime primitive root"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every k<327680, if 2621443+2k is prime then it has a prime " +
                    "primitive root strictly below it. The exact multiplicative order " +
                    "is 2621443+2k−1. The proof concatenates the literal block-success " +
                    "certificates with their precise consecutive offsets and applies " +
                    "checkBlock_sound. These group conclusions jointly supply the " +
                    "complete finite range consumed by erdos985_of_GRH."))),
                DescribeRole.Theorem))));
}
