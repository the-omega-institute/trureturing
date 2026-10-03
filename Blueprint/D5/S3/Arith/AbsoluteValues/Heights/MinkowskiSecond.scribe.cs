using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class MinkowskiSecondDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minkowski's second theorem bounds the product of successive minima times convex-body volume.",
        H("Minkowski Second"),
        Blocks(Describe.Lean(
            DescribeId.Create("minkowski-second"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/MinkowskiSecond.prod_successiveMinimum_mul_measure_le"),
            H("Minkowski Second"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("Minkowski's second theorem bounds the product of successive minima times convex-body volume."))),
            DescribeRole.Theorem))));
}
