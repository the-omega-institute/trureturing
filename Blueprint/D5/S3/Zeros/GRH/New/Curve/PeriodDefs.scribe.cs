using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Curve;

internal sealed class PeriodDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Period Defs", H("Period Defs"),
        Blocks(
            Paragraph(Text("The number s₀, an f-th root of chiFin(α)⁻¹, and its absolute value. Names for the curve, its period and the scale of derivatives.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Curve/PeriodDefs.norm_gal_vacuumRoot"),
                H("norm_gal_vacuumRoot"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Every automorphism σ of ℂ over K preserves the absolute value of s₀ = Parameters.vacuumRoot: |σ(s₀)|² = rootDiscr(E)/√d.")))))));
}
