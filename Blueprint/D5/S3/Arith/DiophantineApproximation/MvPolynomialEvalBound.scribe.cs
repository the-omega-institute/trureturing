using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class MvPolynomialEvalBoundDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A polynomial evaluation admits a controlled local bound after subtraction.",
        H("Mv Polynomial Eval Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("mv-polynomial-eval-bound"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/MvPolynomialEvalBound.exists_apply_eval_le_of_sub"),
            H("Mv Polynomial Eval Bound"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("A polynomial evaluation admits a controlled local bound after subtraction."))),
            DescribeRole.Theorem))));
}
