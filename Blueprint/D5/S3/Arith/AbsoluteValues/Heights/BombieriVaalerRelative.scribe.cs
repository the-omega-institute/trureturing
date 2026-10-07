using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class BombieriVaalerRelativeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "From numbers at least one, select a smaller subfamily with bounded geometric mean.",
        H("Bombieri Vaaler Relative"),
        Blocks(Describe.Lean(
            DescribeId.Create("bombieri-vaaler-relative"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/BombieriVaalerRelative.exists_injective_prod_pow_le"),
            H("Bombieri Vaaler Relative"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("From numbers at least one, select a smaller subfamily with bounded geometric mean."))),
            DescribeRole.Theorem))));
}
