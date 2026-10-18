using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class LowerGelfandNaimarkDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lower multiplicative singular-value bounds.", H("LowerGelfandNaimark"), Blocks(
            Paragraph(Text("For invertible square matrices C and D, the product of the ratios of singular values of CD to those of D over an arbitrary k-element index set is bounded by the product of the k largest singular values of C.")),
            Paragraph(Text("Write C in singular-value coordinates and divide its diagonal by its kth singular value r. Replace each resulting diagonal entry by its maximum with one. Both the original scaled Gram matrix and the identity are below the clipped Gram matrix. Sorted eigenvalue monotonicity compares each singular value. Every clipped ratio is at least one, so a subset product is bounded by the full product, which is the absolute determinant. Its value is the initial product divided by the kth power of r; cancellation gives the bound.")))));
}
