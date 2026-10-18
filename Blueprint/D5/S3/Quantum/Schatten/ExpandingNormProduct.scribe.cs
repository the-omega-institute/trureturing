using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class ExpandingNormProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Norm products from expanding middle factors.", H("ExpandingNormProduct"), Blocks(
            Paragraph(Text("Fix complex square matrices A and B and a nonnegative m. Suppose N(ATB) is at least m whenever T has T* T at least the identity in positive semidefinite order. For invertible W, the balanced matrix (tW + t⁻¹W⁻*)/2 is expanding for every positive t. The norm triangle inequality and real homogeneity yield 2m ≤ t N(AWB) + t⁻¹ N(AW⁻*B). Scalar optimization gives m² ≤ N(AWB) N(AW⁻*B), including zero factors.")),
            Paragraph(Text("The statement isolates the balance argument from the separate expanding-factor minimization theorem. No positivity or diagonal assumption on A or B is needed for this implication. No mathematical originality is claimed.")))));
}
