using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class OmittedPrefixSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The damped degree prefix for the omitted zero spectrum",
        H("Signed degree cancellation in the low bins"),
        Blocks(
            Paragraph(Text("For p≤n≤m use v(n)=u/n−2u/q≤0. Since u≥0, the v(n) decrease with n. The indices with "
                + "t≤v(n) form an initial interval of degrees whose signed coefficient sum is a "
                + "difference of two ordinary prefixes.")),
            Paragraph(Text("Under RH the root coefficient is −1/ρ−1/(n−ρ). After the common unit phase exp(2iu "
                + "Im(ρ)/q), the first term is the damped reciprocal sum. Count all actual occurrences "
                + "in each low frequency bin. The local logarithmic count bounds the square bin mass by "
                + "a square-root power of the number of bins with arbitrary slack.")),
            Paragraph(Text("The second coefficient has modulus at most 3/q. Summing over at most q degrees costs "
                + "a constant times the number of low occurrences. The high side uses the existing "
                + "weighted sampling estimate.")),
            Paragraph(Text("The finite-to-infinite transfer keeps the analytic multiplicities and every omitted "
                + "degree with m+1≤2n. Both frequency parts share the normalization exp(−(1/2−1/q)u).")))));
}
