using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder;

internal sealed class TrivialResponseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed sums of trivial-zero root responses",
        H("Möbius cancellation in the degree sum"),
        Blocks(
            Paragraph(Text("For the sublinear estimate, use the signed floor identity to subtract floor(N/n) from ψ(N/n). On n≤N/L the difference is bounded by a sublinear power of N/n. On the remaining interval all three weights have bounded variation for fixed L. After letting N grow and then choosing L large, the Möbius partial sum times log N is little-o of N, uniformly in the shorter prefix. The same signed summation proves the required sublinear trivial-root response.")),
            Paragraph(Text("The convolution identity for μ(n) log n and the Chebyshev bound under RH imply that the Möbius partial sum times log N is bounded by a constant times N. Split the shorter prefixes at the square root of N to obtain the same bound uniformly.")),
            Paragraph(Text("At log cutoff u≥0 the jth trivial zero contributes n/[2j(n+2j)] times exp(−2ju/n). This response is nonnegative, increases with n, and is at most half of one plus log n. Abel summation uses the shorter-prefix bound and controls the signed weighted sum.")),
            Paragraph(Text("The exact centered root formula includes the constant −log(2π). Its contribution and the summed response are bounded by a constant times m exp(−u/2).")))));
}
