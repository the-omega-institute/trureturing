using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class RankOneHadamardDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Schatten/RankOneHadamard";
    private static LibraryNoteRef Background => LibraryNoteRef.Create("D5/L/Eigenstructure/bhatia1997matrixanalysis");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rank-one Hadamard products and nonnegative diagonal weights.",
        H("Rank-one Hadamard products and nonnegative diagonal weights"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zhangli-rankonehadamard-exists-rank-one-factors"),
                DeclarationHandle.Create(Module + ".exists_rank_one_factors"),
                H("Outer-product factorization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("Every complex square G of rank at most one has the form G=xyᵀ for two complex vectors x and y. The zero matrix and dimension zero are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-rankonehadamard-rank-one-hadamard-reduction"),
                DeclarationHandle.Create(Module + ".rank_one_hadamard_reduction"),
                H("Common diagonal weights for both factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex square G of rank at most one and every unitarily invariant norm N, there are nonnegative real vectors a and b such that, simultaneously for every W, N(W∘G)=N(diag(a)Wdiag(b)) and N(W⁻¹∘Gᵀ)=N(diag(a)(W⁻¹)*diag(b)). Factor G=xyᵀ and take aᵢ=|xᵢ| and bᵢ=|yᵢ|. Diagonal unitary phases remove the arguments of x and y, with phase one at zero; transpose and adjoint invariance identify the second factor."))),
                DescribeRole.Theorem))));
}
