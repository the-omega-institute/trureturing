using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class ComplexShellsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex Shells", H("Complex Shells"),
        Blocks(
            Paragraph(Text("Summing the local theorem over shells at C; explicit band bound for forms.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/ComplexShells.norm_floorForm_le"),
                H("norm_floorForm_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a cut F, j ≤ ϱ, |ω| ≤ 1: if Level.formModulus² ≤ (π/|y|)^{2(k−1)}·Gauge.selfNormProduct at all positions in every gauge with head p, then |IsCutBessel.formConst·𝓘_j(p, q; ω)| ≤ Θ b^{2000n⁹} ℓ_{k−n⁷}(1/|y|) 𝗁(p)𝗁(q), with ℓ = dampedPower, 𝗁 = headWeight n⁶ j, n = ϱ+1.")))))));
}
