using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class PlacesOverInfiniteDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An absolute value above an infinite place is an infinite place upstairs.",
        H("Places Over Infinite"),
        Blocks(Describe.Lean(
            DescribeId.Create("places-over-infinite"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/PlacesOverInfinite.isInfinitePlace_of_liesOver"),
            H("Places Over Infinite"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("An absolute value above an infinite place is an infinite place upstairs."))),
            DescribeRole.Theorem))));
}
