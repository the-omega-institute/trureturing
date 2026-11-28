using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class MemberKernelsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Member Kernels", H("Member Kernels"),
        Blocks(
            Paragraph(Text("Cauchy-type bounds for all conjugates of theta jets and Schur jets. Regular parameters come from weights; bounds for rows and boxes. Integrality and conjugate bounds for theta kernels of definite pairs; rational automorphy law. Point forms with prescribed residue datum: pairing, and theta descent as a kernel. Kernel as a vector, the free level, and one class sum at that level.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/MemberKernels.exists_modKernel_integral_bound"),
                H("exists_modKernel_integral_bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For each d some c ≠ 0 serves all kernels θ of definite pairs with Q homogeneous of degree d, qg² ∈ 𝔪, Ψ integral off q: c·θ is p-integral for p ∤ q, Q and points integral at p; for q = 1, ranks ≤ 40k, d ≤ g, |σ(c·θ)| ≤ exp(x₁)MB if M bounds all conjugates of Ψ and B bounds σQ on entries ≤ g⁴.")))))));
}
