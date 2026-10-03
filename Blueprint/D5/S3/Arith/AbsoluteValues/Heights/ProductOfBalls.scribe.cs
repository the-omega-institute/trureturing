using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AbsoluteValues.Heights;

internal sealed class ProductOfBallsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A product of Euclidean balls satisfies a slice bound.",
        H("Product Of Balls"),
        Blocks(Describe.Lean(
            DescribeId.Create("product-of-balls"),
            DeclarationHandle.Create("D5/S3/Arith/AbsoluteValues/Heights/ProductOfBalls.hasSliceBound_prodBall"),
            H("Product Of Balls"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("A product of Euclidean balls satisfies a slice bound."))),
            DescribeRole.Theorem))));
}
