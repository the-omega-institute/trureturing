using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class PolynomialDeterminantHeightDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The determinant height of a polynomial matrix has an explicit product bound.",
        H("Polynomial Determinant Height"),
        Blocks(Describe.Lean(
            DescribeId.Create("polynomial-determinant-height"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/PolynomialDeterminantHeight.mulHeight_det_le"),
            H("Polynomial Determinant Height"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("The determinant height of a polynomial matrix has an explicit product bound."))),
            DescribeRole.Theorem))));
}
