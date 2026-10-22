using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.BesselRedheffer;

internal sealed class SeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Convergence and differential identities of the normalized Bessel series.",
        H("The normalized Bessel series"), Blocks(
            Entry("bessel-summable", "summable_nbessel", "Absolute convergence",
                "For order nu greater than -1 and every real argument x, the defining series converges absolutely. The ratio of successive coefficient magnitudes is 1/((nu+1+n)(n+1)); multiplying by any fixed argument still gives a sequence tending to zero."),
            Entry("bessel-zero", "nbessel_zero", "The value at the origin",
                "For every real order nu the value at zero is one, since only the constant term contributes."),
            Entry("bessel-derivative", "hasDerivAt_nbessel", "Differentiation raises the order",
                "For nu greater than -1, the derivative at every real x is -x/(2(nu+1)) times the normalized Bessel function of order nu+1. The auxiliary series in t=-x squared/4 has derivative equal to the series with its lower parameter raised by one, divided by the original lower parameter. On a bounded interval the differentiated series has an absolutely summable uniform majorant."),
            Entry("bessel-continuous", "continuous_nbessel", "Continuity",
                "For nu greater than -1, the normalized Bessel function is continuous on the real line."),
            Entry("bessel-near-zero", "nbessel_pos_near_zero", "Positivity near zero",
                "For nu greater than -1 the normalized series is positive in a neighbourhood of zero, since it is continuous and its value at zero is one."),
            Entry("bessel-contiguous", "nbessel_contiguous", "Three consecutive orders",
                "For nu greater than -1, the series of order nu equals the series of order nu+1 minus x squared divided by 4(nu+1)(nu+2) times the series of order nu+2. The rising factorial recurrence gives the coefficient identity and absolute convergence permits summation."),
            Entry("bessel-second-derivative", "hasDerivAt_nbessel_deriv", "A second derivative",
                "The derivative of -x/(2(nu+1)) times the series of order nu+1 is -1/(2(nu+1)) times that series plus x squared divided by 4(nu+1)(nu+2) times the series of order nu+2."),
            Entry("bessel-equation", "nbessel_ode", "The normalized Bessel equation",
                "The second derivative multiplied by x, plus the first derivative multiplied by 2nu+1, plus x times the normalized series, vanishes for every real x and every nu greater than -1. Substituting the shifted-series derivative formulas reduces the identity to the relation between three consecutive orders."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/BesselRedheffer/Series." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
