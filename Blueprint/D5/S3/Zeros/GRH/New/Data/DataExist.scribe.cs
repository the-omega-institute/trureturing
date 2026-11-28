using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Data;

internal sealed class DataExistDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Data Exist", H("Data Exist"),
        Blocks(
            Paragraph(Text("Admissible data exist for large x; Behrend sets and class-group pigeonhole as inputs.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Data/DataExist.exists_data"),
                H("exists_data"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let 0 < ε < 1/100. For all large x there are admissible data with scale x, log x₁ = x^{ε/6} ≥ (10⁶ log x)², log log b = ε log x, and at least 3^c 2^s / log b thick places.")))))));
}
