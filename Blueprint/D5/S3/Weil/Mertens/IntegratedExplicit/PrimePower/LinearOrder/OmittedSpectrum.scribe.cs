using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder;

internal sealed class OmittedSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The omitted root spectra under RH",
        H("Sampling at the actual root coordinates"),
        Blocks(
            Paragraph(Text("To obtain sublinear order for u≥Lq, retain finitely many frequency bins. Their bounded amplitudes multiply a geometric weight sum at most 1+q²/u. The complementary bins have arbitrarily small squared mass and satisfy the local Gaussian estimate with its square-root coefficient. The finite decomposition passes to the full occurrence series at the original sample coordinates.")),
            Paragraph(Text("Count all nontrivial zeros in signed unit bins with their analytic multiplicities. The reciprocal norm of each occurrence is bounded by a constant divided by one plus the absolute bin index. The logarithmic unit count gives a square-summable bin majorant.")),
            Paragraph(Text("At degree n the coefficient is −n/[ρ(n−ρ)]. Its adjacent difference is 1/[(n−ρ)(n+1−ρ)]. The finite sampling bound applies to the coefficients and their increments, and hence to the sum at varying degrees.")),
            Paragraph(Text("For q=m+1 and u≥q, group by the unit bands of 2u/q−u/n and sum their geometric weights. The first omitted degree can have zero exponent slack. Absolute convergence at each sample gives the bound for the actual omitted root densities.")))));
}
