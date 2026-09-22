using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.WeightedCapacity;

internal sealed class PrimeReciprocalCharacterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocal Prime Circle Character.",
        H("Reciprocal Prime Circle Character"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("primereciprocalcharacter-result"),
                DeclarationHandle.Create("D5/S3/Analytic/WeightedCapacity/PrimeReciprocalCharacter.result"),
                H("Separation of finite binary states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On finite support states with every capacity equal to one, the circle character "
                    + "whose coefficients are reciprocals of the increasing prime enumeration is injective. "
                    + "Its zero fibre consists exactly of the zero state. Every unit state is nonzero, "
                    + "and the constant half coefficient character sends it to the half circle class, "
                    + "outside the open ball of radius one quarter about zero. The initial topology "
                    + "of the golden coordinate phases and the reciprocal prime character is strictly "
                    + "coarser than the initial topology of the golden phases and all rational characters. "
                    + "Clearing the distinct prime denominators isolates each signed binary coefficient "
                    + "by divisibility. The unit states converge to zero in the former topology, "
                    + "whereas convergence in the latter topology requires eventual equality."))),
                DescribeRole.Theorem))));
}
