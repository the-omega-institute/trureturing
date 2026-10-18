using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class ExpandingAverageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced inverse-adjoint averages are expanding.", H("ExpandingAverage"), Blocks(
            Paragraph(Text("For an invertible complex matrix W and a positive real t, the matrix T=(tW+t^{-1}(W^{-1})^*)/2 satisfies T^*T-I positive semidefinite. Expanding the Gram matrix gives T^*T-I=(tW-t^{-1}(W^{-1})^*)^*(tW-t^{-1}(W^{-1})^*)/4. The mixed terms are identities because W is invertible.")))));
}
