using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class HadamardDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complex Pluecker row norm is bounded by a product of row norms.",
        H("Hadamard"),
        Blocks(Describe.Lean(
            DescribeId.Create("hadamard"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/Hadamard.sum_sq_norm_plucker_row_le_prod"),
            H("Hadamard"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("A complex Pluecker row norm is bounded by a product of row norms."))),
            DescribeRole.Theorem))));
}
