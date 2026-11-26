using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class RowDimensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Row Dimension", H("Row Dimension"),
        Blocks(
            Paragraph(Text("Dimension of rows at most group order times degree times mass.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/RowDimension.finrank_rows_le_mass"),
                H("finrank_rows_le_mass"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The complex dimension of the space of rows is at most |𝖦|·deg·mass_r, with 𝖦 = Data.G, deg the product of the local degrees of the Bessel systems, and mass_r the mass of the genus of O_E^r.")))))));
}
