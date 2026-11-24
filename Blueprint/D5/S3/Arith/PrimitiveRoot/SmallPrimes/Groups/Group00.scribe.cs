using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Groups;

internal sealed class SmallPrimeGroup00Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consecutive odd-slot certificate group 0",
        H("Consecutive odd-slot certificate group 0"), Blocks(
            Describe.Lean(DescribeId.Create("small-prime-group-00-sound"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimitiveRoot/SmallPrimes/Groups/Group00.group00_sound"),
                H("Every prime in the group has a smaller prime primitive root"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every k<327680, if 3+2k is prime then it has a prime " +
                    "primitive root strictly below it. The exact multiplicative order " +
                    "is 3+2k−1. The proof uses the literal block-success " +
                    "certificate selected by the consecutive-slot index and applies " +
                    "checkBlock_sound. These group conclusions jointly supply the " +
                    "complete finite range consumed by erdos985_of_GRH."))),
                DescribeRole.Theorem))));
}
