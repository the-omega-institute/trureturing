using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Asymptotics;

internal sealed class StatLeanFourierCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/Asymptotics/StatLeanFourierCore.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/statlean2026fourier");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The tent and squared-sinc Fourier pair provides Fejer smoothing and Fourier representations of ramp differences.",
        H("Fejer smoothing and the tent Fourier pair"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fejer-unit-mass"),
                DeclarationHandle.Create(Prefix + "integral_fejerKernel"),
                H("The Fejer kernel has unit mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every positive bandwidth, the squared-sinc Fejer kernel is integrable and its integral is one. The tent function and its Fourier transform supply a probability smoothing kernel with compact Fourier support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tent-fourier-pair"),
                DeclarationHandle.Create(Prefix + "fourier_gTent"),
                H("A translated and rescaled Fourier pair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("A modulated squared-sinc function transforms into a translated and rescaled tent. Positive bandwidth fixes the support interval and the scaling factor."))),
                DescribeRole.Theorem))));
}
