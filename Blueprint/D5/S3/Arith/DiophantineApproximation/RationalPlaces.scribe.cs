using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class RationalPlacesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/ralfstephan2026subspacetheorems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every rational p-adic absolute value is exactly a finite place of the rational field.",
        H("Rational Places"),
        Blocks(Describe.Lean(
            DescribeId.Create("rational-places"),
            DeclarationHandle.Create("D5/S3/Arith/DiophantineApproximation/RationalPlaces.exists_finitePlace_val_eq_padic"),
            H("Rational Places"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text("Every rational p-adic absolute value is exactly a finite place of the rational field."))),
            DescribeRole.Theorem))));
}
