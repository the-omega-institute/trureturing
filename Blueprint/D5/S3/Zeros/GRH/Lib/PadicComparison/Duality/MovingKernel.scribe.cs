using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.Duality;

internal sealed class MovingKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Moving Kernel", H("Moving Kernel"),
        Blocks(
            Paragraph(Text("Moving a supported kernel class between points of (P^1)^d one coordinate at a time.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/Duality/MovingKernel.exists_move_kernel"),
                H("exists_move_kernel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let maximal ideals of each g(c) be kernels of maps g(f), and t send d sections of P¹, pointwise, to sections of X. Each class δ supported where I is proper at t(q) has a δ' at t(q') such that, after any restriction φ and in any theory Θ, δT = t(q)^*w implies δ'T = t(q')^*w · ∏_j (η_{q_j} + η_{q'_j}).")))))));
}
