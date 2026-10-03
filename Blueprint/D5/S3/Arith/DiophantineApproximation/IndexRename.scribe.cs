using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class IndexRenameDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Renaming and cardinality control the index of a multivariate polynomial.",
        H("Index Rename"),
        Blocks(Describe.Lean(
            DescribeId.Create("index-rename"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/IndexRename.index_le_card"),
            H("Index Rename"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("Renaming and cardinality control the index of a multivariate polynomial."))),
            DescribeRole.Theorem))));
}
