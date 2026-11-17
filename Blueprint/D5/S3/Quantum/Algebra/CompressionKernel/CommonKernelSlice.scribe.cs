using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.CompressionKernel;

internal sealed class CommonKernelSliceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/CompressionKernel/CommonKernelSlice.";
    private static DocumentBlock Node(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite adjoint-symmetric matrix family has a real combination with exactly its common kernel.", H("The common-kernel slice"), Blocks(
            Paragraph(Text("For every k, a, and b in ℕ, let X : Fin k → Matrix (Fin a) (Fin b) ℂ. If (X i)ᴴ * X j = (X j)ᴴ * X i for all i,j, a real coefficient function t : Fin k → ℝ has a complex linear combination whose kernel is exactly the infimum of the kernels of all X i. The statement includes empty families and zero dimensions.")),
            Node("common_kernel_slice", "A real combination realizes the common kernel", "For all k a b : ℕ, every X : Fin k → Matrix (Fin a) (Fin b) ℂ, and hcomm : ∀ i j, (X i)ᴴ * X j = (X j)ᴴ * X i, there exists t : Fin k → ℝ such that ker ((∑ i, (t i : ℂ) • X i).mulVecLin) = ⨅ i, ker ((X i).mulVecLin)."),
            Node("common_kernel_slice_injective_of_common_kernel_bot", "The zero-common-kernel consequence", "For all k a b : ℕ, every X and hcomm as above, and hcommon : (⨅ i, ker ((X i).mulVecLin)) = ⊥, there exists t : Fin k → ℝ such that (∑ i, (t i : ℂ) • X i).mulVecLin is injective and b ≤ a."))));
}
