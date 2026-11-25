using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.LinearOrder;

internal sealed class MoebiusPrefixesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform logarithmic bounds for Möbius prefixes",
        H("Cancellation in the logarithmically weighted sum"),
        Blocks(
            Paragraph(Text("The convolution for μ(n) log n and the Chebyshev estimate under RH bound the Möbius partial sum times log N by a constant times N. Splitting at the square root of N gives the same order uniformly over shorter prefixes.")),
            Paragraph(Text("For the little-o estimate consider the weight floor(N/n) − ψ(N/n) + log(N/n). On n≤N/L the signed floor and Chebyshev terms differ by a sublinear power of N/n. On n>N/L all three weights have bounded variation at fixed L, so Abel summation gives an error of order N/log N with a constant depending on L. First choose L large to make the first coefficient small, then let N grow. Splitting the prefix again at the square root of N yields the uniform little-o bound.")))));
}
