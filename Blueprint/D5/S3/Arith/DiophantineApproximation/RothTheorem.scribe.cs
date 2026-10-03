using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class RothTheoremDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selected-place approximants beyond exponent two form a finite set.",
        H("Roth Theorem"),
        Blocks(Describe.Lean(
            DescribeId.Create("roth-theorem"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/RothTheorem.finite_setOf_prod_min_one_le"),
            H("Roth Theorem"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("Selected-place approximants beyond exponent two form a finite set."))),
            DescribeRole.Theorem))));
}
