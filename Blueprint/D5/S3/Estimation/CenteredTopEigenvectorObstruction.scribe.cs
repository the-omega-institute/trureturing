using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation;

internal sealed class CenteredTopEigenvectorObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/CenteredTopEigenvectorObstruction.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/mazhang2026topeigenvectorweight");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A top eigenvector of weight at most one half relative to a unit vector bounds the "
            + "centered energy and, for positive semidefinite matrices, the half trace.",
        H("The centered top-eigenvector obstruction"),
        Blocks(
            Describe.Lean(DescribeId.Create("centered-top-eigenvector-obstruction-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The obstruction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let H be a real symmetric n×n matrix, u a unit vector and v a unit "
                        + "eigenvector of H whose eigenvalue is at least every eigenvalue of H, "
                        + "with ⟨u,v⟩² ≤ 1/2. Put τ = tr H / n and r = uᵀHu − τ. If r ≥ 0, then "
                        + "2n r² ≤ (n − 2) tr((H − τI)²); for n ≥ 3 and r > 0 this is "
                        + "tr((H − τI)²) ≥ 2n r² / (n − 2), which is Corollary 10 of H. Ma and "
                        + "W. Zhang (version 2). If H is positive semidefinite, then "
                        + "uᵀHu ≤ tr H / 2. No size restriction is needed: for n = 2 the weight "
                        + "condition forces r ≤ 0, and for n = 1 it cannot hold. The Lean "
                        + "statement allows any unit eigenvector of the largest eigenvalue, not "
                        + "only a member of a fixed eigenbasis.")),
                    Paragraph(Text(
                        "Expand u in an orthonormal eigenbasis with weights w_k = ⟨b_k,u⟩², so "
                        + "that uᵀHu = Σ λ_k w_k. If the largest eigenvalue λ occurs at two "
                        + "indices, their eigenvalues sum to 2λ ≥ 2uᵀHu. Otherwise v is a signed "
                        + "basis vector b_i, its weight w_i is at most one half, and comparing "
                        + "with the largest remaining eigenvalue λ_j gives 2uᵀHu ≤ λ_i + λ_j. In "
                        + "both cases two distinct eigenvalues satisfy λ_i + λ_j ≥ 2uᵀHu. The "
                        + "centered eigenvalues λ_k − τ sum to 0 and their squares sum to "
                        + "tr((H − τI)²); the n − 2 remaining ones sum to −(λ_i + λ_j − 2τ), so by "
                        + "Cauchy–Schwarz n(λ_i + λ_j − 2τ)² ≤ 2(n − 2) tr((H − τI)²), and "
                        + "λ_i + λ_j − 2τ ≥ 2r > 0 gives the bound. For positive semidefinite H "
                        + "the remaining eigenvalues are nonnegative, so λ_i + λ_j ≤ tr H. For "
                        + "n = 2, τ is the average of the two eigenvalues, so r ≤ 0.")),
                    Paragraph(Text(
                        "The hypotheses are needed as follows. Without the weight condition the "
                        + "bound fails: for u a top eigenvector of a matrix with eigenvalues "
                        + "1, 0, …, 0 and n large, r is close to 1 while tr((H − τI)²) is close "
                        + "to 1. The sign condition r ≥ 0 cannot be dropped: for H with "
                        + "eigenvalues −1, 0, …, 0, u the first and v the second basis vector, "
                        + "r = −1 + 1/n < 0 and 2n r² exceeds (n − 2)(1 − 1/n). These remarks are "
                        + "not compiled."))),
                DescribeRole.Theorem))));
}
