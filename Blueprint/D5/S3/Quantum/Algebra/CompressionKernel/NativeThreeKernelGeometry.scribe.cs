using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.CompressionKernel;

internal sealed class NativeThreeKernelGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/CompressionKernel/NativeThreeKernelGeometry.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At strict width-three threshold, the Hermitian compression kernel has a common vector or a common neutral two-plane.", H("The native three-kernel geometry"), Blocks(
            Paragraph(Text("For all a,b : ℕ with a < b, every complex-linearly independent X : Fin 3 → Matrix (Fin a) (Fin b) ℂ whose coefficient-first stack is injective has one of two alternatives: a nonzero v : Fin 3 → ℂ killed by every Hermitian T with compression X T = 0, or a complex submodule W of finrank two on which every such T has zero sesquilinear pairing.")),
            Describe.Lean(DescribeId.Create("native-three-compression-kernel-geometry"), DeclarationHandle.Create(Prefix + "native_three_compression_kernel_geometry"), H("The common vector or neutral plane alternative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The quantified conclusion is (∃ v : Fin 3 → ℂ, v ≠ 0 ∧ ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian → compression X T = 0 → T *ᵥ v = 0) ∨ (∃ W : Submodule ℂ (Fin 3 → ℂ), Module.finrank ℂ W = 2 ∧ ∀ T, T.IsHermitian → compression X T = 0 → ∀ u ∈ W, ∀ v ∈ W, star u ⬝ᵥ (T *ᵥ v) = 0). The normalized graph alternatives first establish normalizedGraphTrichotomy. Congruence transports its vector and plane alternatives to the original coefficient space; the primitive iSkew3 branch would give an injective real combination from the common-kernel slice, forcing b ≤ a and contradicting a < b."))), DescribeRole.Theorem))));
}
