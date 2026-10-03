using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class RowEntryHeightDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Arakelov height of a finite span is bounded by the product of its generators' heights.",
        H("Row Entry Height"),
        Blocks(Describe.Lean(
            DescribeId.Create("row-entry-height"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/RowEntryHeight.arakelovMulHeight_span_range_le_prod"),
            H("Row Entry Height"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The Arakelov height of a finite span is bounded by the product of its generators' heights."))),
            DescribeRole.Theorem))));
}
