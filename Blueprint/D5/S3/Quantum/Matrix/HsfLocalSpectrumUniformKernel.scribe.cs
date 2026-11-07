using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class HsfLocalSpectrumUniformKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform scalar kernel bounds",
        H("Uniform scalar kernel bounds"),
        Blocks(Paragraph(Text("The spectral Gram polynomial gives the rho triangle inequality. The cyclic residual identity and its positive denominator yield the uniform defect-kernel bound. These scalar estimates are consumed by the uniform Frobenius and cubic trace bounds.")))));
}
