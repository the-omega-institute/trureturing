using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder;

internal sealed class SpectralSamplingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local estimates for finite exponential sums",
        H("Gaussian energy and separated samples"),
        Blocks(
            Paragraph(Text("The coefficient of the local integral bound is proportional to the square root of the sum of squared bin masses. If the squared mass is zero, the estimate follows by applying the positive bound with arbitrarily small regularization.")),
            Paragraph(Text("Group complex coefficients by the bins (k,k+1], using the sum of their norms in each bin. Frequencies may repeat.")),
            Paragraph(Text("Expand the Gaussian-weighted squared norm and evaluate the Fourier kernel. Summing the exponential majorant across bin differences gives a uniform bound on intervals of length two.")),
            Paragraph(Text("Separated samples admit disjoint intervals. The fundamental theorem of calculus bounds each sample by the interval average of the norm plus the integral of the derivative norm. A finite sum of adjacent parameter increments permits a variable coefficient at each sample.")),
            Paragraph(Text("For actual reciprocal coordinates u/n up to degree q, use separation "
                + "min(1,u/q²). Interpolating the derivative weight between q and 1+|k| "
                + "preserves square summability with bin exponent −5/8 and costs q^(7/8). "
                + "The total of the adjacent increments has the same order as the initial "
                + "derivative bound.")))));
}
