using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder;

internal sealed class SpectralSamplingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local estimates for finite exponential sums",
        H("Gaussian energy and separated samples"),
        Blocks(
            Paragraph(Text("Group complex coefficients by the bins (k,k+1], using the sum of their norms in each bin. Frequencies may repeat.")),
            Paragraph(Text("Expand the Gaussian-weighted squared norm and evaluate the Fourier kernel. Summing the exponential majorant across bin differences gives a uniform bound on intervals of length two.")),
            Paragraph(Text("Separated samples admit disjoint intervals. The fundamental theorem of calculus bounds each sample by the interval average of the norm plus the integral of the derivative norm. A finite sum of adjacent parameter increments permits a variable coefficient at each sample.")))));
}
