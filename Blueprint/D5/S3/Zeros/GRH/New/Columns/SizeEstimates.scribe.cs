using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Columns;

internal sealed class SizeEstimatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Size Estimates", H("Size Estimates"),
        Blocks(
            Paragraph(Text("Size bookkeeping: row lengths, factorial sizes, class counts, sum of allowed losses.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Columns/SizeEstimates.sum_allowedLoss_mul_log_le"),
                H("sum_allowedLoss_mul_log_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For every finite set U of natural numbers, ∑_{p∈U} err(p) log p ≤ fa(log b)³, with err = Data.allowedLoss the allowed loss; the bound is Data.budget.")))))));
}
