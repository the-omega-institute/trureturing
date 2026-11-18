using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class NativeCommonKernelBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeCommonKernelBound.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common nonzero coefficient kernel vector forces three times the right input dimension to fit in twice its output dimension.", H("The original Gram common-kernel bound"), Blocks(
            Paragraph(Text("For a,b,c,d : ℕ, X : Fin 3 → Matrix (Fin a) (Fin b) ℂ, and Y : Fin 3 → Matrix (Fin d) (Fin c) ℂ, assume a < b, (∑ r, kronecker (X r) (Y r))ᴴ * (∑ r, kronecker (X r) (Y r)) = 1, and ∑ r, (X r)ᴴ * X r = 1. If v : Fin 3 → ℂ is nonzero and every Hermitian T with compression X T = 0 satisfies T *ᵥ v = 0, then 3*c ≤ 2*d.")),
            Describe.Lean(DescribeId.Create("original-gram-common-kernel-bound"), DeclarationHandle.Create(Prefix + "original_gram_common_kernel_bound"), H("The common-kernel dimension bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The exact telescope is {a b c d : ℕ}, X, Y, hab : a < b, hF : (∑ r, Matrix.kronecker (X r) (Y r))ᴴ * (∑ r, Matrix.kronecker (X r) (Y r)) = 1, hXGram : ∑ r, (X r)ᴴ * X r = 1, v : Fin 3 → ℂ, hv : v ≠ 0, and hkernel : ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian → compression X T = 0 → T *ᵥ v = 0. The conclusion is 3 * c ≤ 2 * d."))), DescribeRole.Theorem))));
}
