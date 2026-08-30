using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta.GoldenSpectrum;

internal sealed class GoldenSpectralPairUnitarityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Analytic/Zeta/GoldenSpectrum/GoldenSpectralPairUnitarity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden radial charge turns critical-line membership into pair isometry.",
        H("Golden Spectral-Pair Unitarity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-spectral-pair-isometry-iff-critical"),
                DeclarationHandle.Create(
                    Prefix + "golden_spectral_pair_isometry_iff"),
                H("Pair isometry is equivalent to criticality"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The positive radial charge of a spectral point defines a reciprocal "
                            + "two-channel transfer.")),
                    Paragraph(Text(
                        "The abstract pair-isometry theorem reduces isometry to radial charge "
                            + "one, and the golden coordinate theorem reduces that condition to "
                            + "real part one half.")),
                    Paragraph(Text(
                        "Every point remains determinant-balanced. Off-line points fail the "
                            + "stronger pointwise isometry condition."))),
                DescribeRole.Theorem))));
}
