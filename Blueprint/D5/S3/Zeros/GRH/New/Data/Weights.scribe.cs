using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Data;

internal sealed class WeightsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weights", H("Weights"),
        Blocks(
            Paragraph(Text("Size comparisons among nominal weights and weights of the lifts.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Data/Weights.log_w_le"),
                H("log_w_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For j ≤ 2m and every infinite place σ of E, log w_j(σ) ≤ log w(σ) + 1/x, where w_j is the j-th weight and w = Data.nominalWeight is the nominal weight.")))))));
}
