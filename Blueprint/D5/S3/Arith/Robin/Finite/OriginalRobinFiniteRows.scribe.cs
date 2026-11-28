using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Finite;

internal sealed class OriginalRobinFiniteRowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact certificates at the original Robin prices.",
        H("Pinned Robin rows through Row 04"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("robin-original-rows-04"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Finite/OriginalRobinFiniteRows.original_robin_through_pinned_row04"),
                H("Robin inequality through Row 04"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pinned rational certificate proves the original inequality for every natural n greater than 5040 with log n at most 146.801491."))),
                DescribeRole.Theorem))));
}
