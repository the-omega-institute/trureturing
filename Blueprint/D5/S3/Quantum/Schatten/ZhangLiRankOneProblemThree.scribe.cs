using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class ZhangLiRankOneProblemThreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rank-one norm product inequality.", H("ZhangLiRankOneProblemThree"), Blocks(
            Paragraph(Text("The assertion concerns a complex square matrix G of rank at most one and an arbitrary unitarily invariant norm. It asks for a permutation minimizing the norm of its entrywise product with G, whose squared value bounds the product of the corresponding norms for an invertible matrix W and its inverse paired with the transpose of G.")),
            Paragraph(Text("For every permutation matrix, the inverse paired with the transpose of G is the transpose of the original entrywise product. The two norms are equal. A minimum over the finite permutation group is attained, including in dimension zero.")),
            Paragraph(Text("Factor G as an outer product and remove its scalar phases using diagonal unitary matrices. Both factors then use the same two nonnegative diagonal weights. The lower Gelfand-Naimark inequality on arbitrary index subsets shows that pairing the decreasing first weights with the increasing second weights minimizes the norm among expanding middle factors. Zero weights follow by positive regularization and continuity. Apply this lower bound to the balanced average of tW and the inverse adjoint scaled by t^{-1}, then optimize over positive t. The resulting scalar inequality gives the squared lower bound, including vanishing factors.")))));
}
