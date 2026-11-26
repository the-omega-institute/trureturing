using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class ColumnCoordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Column Coords", H("Column Coords"),
        Blocks(
            Paragraph(Text("Dictionary between adelic groups and frame coordinates; columns in orthonormal coordinates.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/ColumnCoords.columnCoords"),
                H("columnCoords"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The isomorphism from algebraic forms of weight (kw, 0) and level Kc on U(X₀) to ℓ²(classes × coordinates): evaluate at class representatives, then change coordinates by Filling.Fits.weylBesselEquiv.")))))));
}
