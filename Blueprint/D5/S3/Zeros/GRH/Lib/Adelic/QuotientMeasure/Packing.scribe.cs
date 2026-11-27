using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.QuotientMeasure;

internal sealed class PackingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Packing", H("Packing"),
        Blocks(
            Paragraph(Text("Quotient integral via weights: independence of the weight and Weil's unfolding formula.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/QuotientMeasure/Packing.tsum_inv_pow_le_of_separated"),
                H("tsum_inv_pow_le_of_separated"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let points f_i of a real normed space of finite dimension d have norms and mutual distances at least m > 0. For an integer n ≥ d + 2, ∑ ‖f_i‖^(−n) converges and is at most (5/m)^n.")))))));
}
