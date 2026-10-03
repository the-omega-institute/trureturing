using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class PlacesOverFiniteDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An absolute value above a finite place is a positive power of a finite place upstairs.",
        H("Places Over Finite"),
        Blocks(Describe.Lean(
            DescribeId.Create("places-over-finite"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/PlacesOverFinite.exists_finitePlace_rpow_inv_eq_of_liesOver"),
            H("Places Over Finite"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("An absolute value above a finite place is a positive power of a finite place upstairs."))),
            DescribeRole.Theorem))));
}
