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
                    Paragraph(Text("Let p, q, a, b, and delta be real numbers. Assume p >= 0 and q >= 0; write V = p×a^2 + q×b^2 and assume V > 0. Assume delta >= 0, delta×abs(a) <= 1, delta×abs(b) <= 1, and abs(p×a^3 + q×b^3)×delta/6 + (p×a^4 + q×b^4)×delta^2 <= V/4. On the rescaled interval 0 <= u <= delta×w for w >= 1, these hypotheses bound the cubic and quartic exponent terms by V×u^2/4, leaving the Gaussian envelope exp(-V×u^2/4).")),
                    Paragraph(Text("After rescaling by square-root time w, the error divided by frequency is bounded by a Gaussian times a polynomial of degrees three, five, and seven, divided by w squared. This integrable envelope makes w times the low-frequency integral tend to zero."))),
                DescribeRole.Theorem))));
}
