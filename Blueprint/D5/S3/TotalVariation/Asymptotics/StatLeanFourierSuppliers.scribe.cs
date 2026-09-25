using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Asymptotics;

internal sealed class StatLeanFourierSuppliersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/statlean2026fourier");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier inversion of the tent function and Gaussian Hermite integrals give signed density comparison bounds.",
        H("Fejer smoothing and Gaussian Hermite identities"),
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
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-fourier-cdf-bound"),
                DeclarationHandle.Create(Prefix + "abs_measure_Iic_sub_densityCDF_le_charFun"),
                H("A Fourier bound for a signed comparison density"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Compare the distribution function of a probability measure with the integral of an integrable real function. The comparison function may have either sign. A bound on its absolute integral over intervals controls the ramp approximation error; a weighted characteristic-function difference controls the smoothed error."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("edgeworth-density-integral"),
                DeclarationHandle.Create(Prefix + "densityCDF_edgeworthDensity"),
                H("Integrating the first Hermite correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The first Edgeworth density is the standard Gaussian density multiplied by one plus a cubic Hermite correction. Its integral over a lower half-line is the Gaussian distribution function plus the quadratic Hermite correction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("edgeworth-density-fourier"),
                DeclarationHandle.Create(Prefix + "charFunDensity_edgeworthDensity"),
                H("The characteristic function of the signed Edgeworth density"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Gaussian integration by parts evaluates the cubic Hermite Fourier integral. The result is the Gaussian characteristic function multiplied by its first cubic correction, with the same coefficient as in the density."))),
                DescribeRole.Theorem))));
}
