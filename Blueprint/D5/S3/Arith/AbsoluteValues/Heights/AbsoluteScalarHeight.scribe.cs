using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class AbsoluteScalarHeightDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute scalar logarithmic height is relative logarithmic height normalized by field degree.",
        H("Absolute Scalar Height"),
        Blocks(Describe.Lean(
            DescribeId.Create("absolute-scalar-height"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/AbsoluteScalarHeight.scalar_absolute_log_height"),
            H("Absolute Scalar Height"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("For a number-field element, multiplying absolute logarithmic height by the field degree gives the relative scalar logarithmic height."))),
            DescribeRole.Theorem))));
}
