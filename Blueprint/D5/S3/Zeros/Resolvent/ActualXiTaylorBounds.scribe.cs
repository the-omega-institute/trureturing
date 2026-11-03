using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Resolvent;

internal sealed class ActualXiTaylorBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normal convergence and exact geometric Taylor remainder.",
        H("Normal convergence and exact geometric Taylor remainder"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actualxitaylorbounds"),
                DeclarationHandle.Create("D5/S3/Zeros/Resolvent/ActualXiTaylorBounds.actual_xi_taylor_remainder"),
                H("Normal convergence and exact geometric Taylor remainder"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Keep the same actual xi function, nodes, weights, moments, total absolute mass W, and node-norm supremum Lambda. For every nonnegative r less than one quarter, the folded resolvent and its odd Taylor series both have summable uniform majorants on the closed disk of radius r.")),
                    Paragraph(Text("The xi function is bounded there by W r divided by (1 minus Lambda r squared). After retaining the odd moment terms through index J, its remainder is at most W r times (Lambda r squared) to power J+1, divided by (1 minus Lambda r squared). The finite sum has exactly J+1 odd terms, and the complete infinite tail is retained in the proof.")),
                    Paragraph(Text("The bounds follow from the complex denominator reverse triangle inequality, moment estimates, and a genuinely summable geometric tail. No tail truncation is substituted for the original function, and neither positivity nor RH is used.")))))));
}
