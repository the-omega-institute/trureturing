using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class FrameNormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frame Norm", H("Frame Norm"),
        Blocks(
            Paragraph(Text("Basic properties of frame vectors and the size function modulo the Bessel subgroup. Norm bounds for unitary elements from bounded frames and bounded dual frames.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/FrameNorm.besselSize_le_of_dual"),
                H("besselSize_le_of_dual"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let V_0, …, V_{2ϱ} have lengths at most M ≥ 1, with V_a = x⁻¹f_{a+1} for a ≤ ϱ, and h(V_a, V_b) = −1 if a+b = 2ϱ, 0 if a+b < 2ϱ. Then besselSize x ≤ 8(ϱ+1)M.")))))));
}
