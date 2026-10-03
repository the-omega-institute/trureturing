using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class RestrictScalarsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Restriction of scalars gives a power bound for Arakelov height of a subspace span.",
        H("Restrict Scalars"),
        Blocks(Describe.Lean(
            DescribeId.Create("restrict-scalars"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/RestrictScalars.arakelovMulHeight_span_restrictScalars_rpow_le"),
            H("Restrict Scalars"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("Restriction of scalars gives a power bound for Arakelov height of a subspace span."))),
            DescribeRole.Theorem))));
}
