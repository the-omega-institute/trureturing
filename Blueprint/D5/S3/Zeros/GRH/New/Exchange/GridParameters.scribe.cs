using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class GridParametersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Grid Parameters", H("Grid Parameters"),
        Blocks(
            Paragraph(Text("Index sets, signs, parameters of grids and triangles; gaps, interlacing and matching.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/GridParameters.paramsCorrespond_grid"),
                H("paramsCorrespond_grid"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Every step of either grid is an edge (ParamsCorrespond): from (i,j) to (i+1,j) with both parameters negated, or to (i,j+1) with them unchanged, provided the target indices i', j' are at most m and o = 0 or i' = 0.")))))));
}
