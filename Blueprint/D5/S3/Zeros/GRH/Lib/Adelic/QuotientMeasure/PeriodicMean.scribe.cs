using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.QuotientMeasure;

internal sealed class PeriodicMeanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Periodic Mean", H("Periodic Mean"),
        Blocks(
            Paragraph(Text("Haar mean of periodic functions on a compact quotient; invariance, iteration, change of group.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/QuotientMeasure/PeriodicMean.quotMean_quotMean"),
                H("quotMean_quotMean"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let φ: A → B, φ′: A′ → B be continuous homomorphisms sending A₀, A₁ into B₀, with φ(A) + φ′(A′) = B, quotients compact, A second countable. For continuous B₀-periodic F, the iterated mean of F(φa + φ′a′) over A′/A₁, then A/A₀, is the mean of F over B/B₀.")))))));
}
