using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Curve;

internal sealed class LiveSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Live Sum", H("Live Sum"),
        Blocks(
            Paragraph(Text("Names for asked divisibility, gain, loss, short and served primes. Coupling count and exponent of the jet divisibility theorem; weights of the data. The sum of p^{−e} over e ≥ 1, e odd or p = d, is (1/(p−1) − ρ_p)/ω_p for non-split p, ω_p = (1 − (p/d))/2, ρ_p = nonsplitWeight.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Curve/LiveSum.hasSum_live_inv_pow"),
                H("hasSum_live_inv_pow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If (p/d) ≠ 1, the sum of p^{−e} over the e ≥ 1 with e odd or p = d is (1/(p − 1) − ρ_p)/ω_p, where ω_p = (1 − (p/d))/2 and ρ_p is nonsplitWeight.")))))));
}
