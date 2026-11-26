using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class BandLimitedWindowVarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier variance of band-limited windows",
        H("Band-limited Schwartz windows with uniform variation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("band-limited-window-variance"),
                DeclarationHandle.Create("D5/S3/Analytic/Oscillation/BandLimitedWindowVariance.exists_windows_with_unbounded_spectral_variance"),
                H("Fourier variance of band-limited windows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There is a constant K greater than or equal to zero such that for each natural number n a real Schwartz function g has Fourier transform supported in the closed unit band, derivative integral at most K, and weighted Fourier energy at least n divided by four pi squared. The weight in the energy is the absolute value of frequency.")),
                    Paragraph(Text("Take the inverse Fourier transform of an even smooth bump which equals one on a neighborhood of zero. Integrating that real function over a sliding interval gives a Schwartz window. Its derivative is the difference of the two translates at the interval endpoints, so its integral of absolute derivative is at most twice the integral of the absolute value of the original function.")),
                    Paragraph(Text("The Fourier transform of the interval contributes a sine divided by frequency. On each interval between consecutive points of the form two to the power j times pi, the integral of sine squared divided by its argument is at least one quarter. A suitable window width places n of these intervals in the band where the smooth bump is one."))),
                DescribeRole.Theorem))));
}
