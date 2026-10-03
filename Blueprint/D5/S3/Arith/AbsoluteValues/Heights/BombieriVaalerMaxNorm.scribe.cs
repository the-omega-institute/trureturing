using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class BombieriVaalerMaxNormDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integral basis of a matrix kernel has a discriminant and row-space height bound with an explicit complex-place factor.",
        H("Bombieri Vaaler Max Norm"),
        Blocks(Describe.Lean(
            DescribeId.Create("bombieri-vaaler-max-norm"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/BombieriVaalerMaxNorm.exists_basis_ker_prod_absMulHeight_le"),
            H("Bombieri Vaaler Max Norm"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("An integral basis of a matrix kernel has a discriminant and row-space height bound with an explicit complex-place factor."))),
            DescribeRole.Theorem))));
}
