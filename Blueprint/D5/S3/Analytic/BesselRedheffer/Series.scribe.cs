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
                "For nu greater than -1, the normalized Bessel function is continuous on the real line."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/BesselRedheffer/Series." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
