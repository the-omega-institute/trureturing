using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class BandLimitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Band Limits", H("Band Limits"),
        Blocks(
            Paragraph(Text("Band limits and energy bound for cut Bessel function at a real place.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/BandLimits.hasBandLimits_of_isCutBessel"),
                H("hasBandLimits_of_isCutBessel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let W, F be a cut pair of Bessel functions with the numerical conditions of IsCutBessel. If W has Schur's bound with constant deg⁻¹|I|, where 0 < deg and deg·Θ ≤ b^{4r²} (Θ = Shape.bandConst), then F has the band limits HasBandLimits for some forms J.")))))));
}
