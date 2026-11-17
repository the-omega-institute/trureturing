using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra.CompressionKernel;

internal sealed class NativeTwoKernelBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/CompressionKernel/NativeTwoKernelBound.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict native width-two scalar Gram forces twice the right input dimension to fit in the output dimension.", H("The width-two residual Gram bound"), Blocks(
            Paragraph(Text("For a,b,c,d : ℕ with a < b, let M : Fin 2 → Matrix (Fin a) (Fin b) ℂ and N : Fin 2 → Matrix (Fin d) (Fin c) ℂ. If M is complex-linearly independent, (∑ r, kronecker (M r) (N r))ᴴ * (∑ r, kronecker (M r) (N r)) = 1, and ∑ r, (M r)ᴴ * M r = 1, then 2*c ≤ d. All zero-dimensional factors remain in scope.")),
            Describe.Lean(DescribeId.Create("right-dimension-bound"), DeclarationHandle.Create(Prefix + "right_dimension_bound"), H("The width-two right dimension bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The exact binders are {a b c d : ℕ}, hab : a < b, M : Fin 2 → Matrix (Fin a) (Fin b) ℂ, N : Fin 2 → Matrix (Fin d) (Fin c) ℂ, hM : LinearIndependent ℂ M, hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ * (∑ r, Matrix.kronecker (M r) (N r)) = 1, and hMG : ∑ r, (M r)ᴴ * M r = 1; the conclusion is 2 * c ≤ d."))), DescribeRole.Theorem))));
}
