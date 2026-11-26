using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class PuncturedCircuitCoordinateCountDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/PuncturedCircuitCoordinateCount";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two coordinate counts after one pair is removed.",
        H("Counting after Omitting a Pair"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("card-after-omitting-pair"),
                DeclarationHandle.Create(Module + ".card_after_omitting_pair"),
                H("The remaining coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each subset containing the first distinguished element contains both distinguished "
                    + "elements or belongs to the first side of a pair. A subset omitting it contains neither "
                    + "or belongs to the second side. Removing one distinguished pair subtracts one from each "
                    + "count."))),
                DescribeRole.Theorem))));
}
