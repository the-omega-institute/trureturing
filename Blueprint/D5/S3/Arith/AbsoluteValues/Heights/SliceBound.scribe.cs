using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class SliceBoundDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The slice-bound condition controls integration along a linear subspace.",
        H("Slice Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("slice-bound"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/SliceBound.lintegral_le"),
            H("Slice Bound"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The slice-bound condition controls integration along a linear subspace."))),
            DescribeRole.Theorem))));
}
