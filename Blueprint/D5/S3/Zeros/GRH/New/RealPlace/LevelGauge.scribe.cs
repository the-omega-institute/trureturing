using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class LevelGaugeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Level Gauge", H("Level Gauge"),
        Blocks(
            Paragraph(Text("Invariant measure as a tower of big cells; definitions of level, gauge, weights, pairing kernels.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/LevelGauge.lintegral_stackMeasure_mul_left"),
                H("lintegral_stackMeasure_mul_left"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let 𝖬 be a Haar measure, j ≤ ϱ+2, and w_p the Weyl element of length j. For measurable left H_j-invariant Φ ≥ 0, ∫ Φ(w_p⁻¹g) d𝗆_j(g) = ∫ Φ(g) d𝗆_j(g).")))))));
}
