using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation.Asymptotics;

internal sealed class CompoundPoissonEdgeworthFoundationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/TotalVariation/Asymptotics/CompoundPoissonEdgeworthFoundation.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/statlean2026fourier");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite signed smoothing and a Gaussian envelope control the low-frequency error of two-jump Poisson laws.",
        H("Finite smoothing and low-frequency Poisson decay"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-signed-smoothing"),
                DeclarationHandle.Create(Prefix + "generic_finite_smoothing"),
                H("Finite-frequency smoothing for a signed density"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Let P be any probability measure on the real line, and let q be an integrable real comparison density bounded in absolute value by A. Assume its lower-half-line integral is Lipschitz with constant A. There is a universal positive H such that, for every positive bandwidth on whose frequency interval the weighted Fourier difference is integrable, the distribution-function error is bounded by twice that Fourier integral plus 4AH divided by the bandwidth.")),
                    Paragraph(Text("Convolution with a squared-sinc probability density cuts off Fourier frequencies. Monotonicity of the actual distribution function and the Lipschitz property of the signed comparison absorb the remaining tail discrepancy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("low-frequency-poisson-error"),
                DeclarationHandle.Create(Prefix + "low_frequency_integral_vanishes"),
                H("A Gaussian envelope on a growing frequency interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Write V for p times a squared plus q times b squared, and use the raw cubic and quartic jump moments. On a sufficiently small fixed raw-frequency interval, the cubic and quartic exponent terms are bounded by V times u squared divided by four, leaving Gaussian decay exp(-V u squared / 4).")),
                    Paragraph(Text("After rescaling by square-root time w, the error divided by frequency is bounded by a Gaussian times a polynomial of degrees three, five, and seven, divided by w squared. This integrable envelope makes w times the low-frequency integral tend to zero."))),
                DescribeRole.Theorem))));
}
