using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class ThueEquationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonzero fiber of a binary form with three projective roots is finite.",
        H("Thue Equation"),
        Blocks(Describe.Lean(
            DescribeId.Create("thue-equation"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/ThueEquation.finite_setOf_eval_homogenize_eq"),
            H("Thue Equation"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("A nonzero fiber of a binary form with three projective roots is finite."))),
            DescribeRole.Theorem))));
}
