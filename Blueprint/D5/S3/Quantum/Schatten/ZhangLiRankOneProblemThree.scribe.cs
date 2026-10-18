using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class ZhangLiRankOneProblemThreeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Schatten/ZhangLiRankOneProblemThree";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Eigenstructure/zhangli2026eigenvalueperturbation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zhang–Li Problem 3 for matrices of rank at most one.",
        H("Zhang–Li Problem 3 for matrices of rank at most one"),
        Blocks(
            Paragraph(Text("Lei-Hong Zhang and Ren-Cang Li, On a Conjecture Related to Eigenvalue Perturbations, arXiv:2609.25552v1, §1 Problem 3 and §5.")),
            Paragraph(Text("Problem 3: Relate min_{W nonsingular} ‖W∘G‖_ui ‖W^{-1}∘G^T‖_ui to min_{P permutation} ‖P∘G‖_ui^2.")),
            Paragraph(Text("In fact, for rank-one G, Romeo and Tilli [23, Theorem 1.2] proved (1.1) with c1=1 and the unitary restriction (2.3) with c2=1. They explicitly left the corresponding nonsingular version of Problem 3 unresolved; see [23, Remark 3.1].")),
            Describe.Lean(
                DescribeId.Create("zhangli-zhanglirankoneproblemthree-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The complete rank-one variational assertion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every natural n, every complex n by n matrix G of rank at most one, and every unitarily invariant norm N, there exists a permutation σ minimizing N(Pσ∘G) over all permutations, with N(Pσ∘G)²≤N(W∘G)N(W⁻¹∘Gᵀ) for every invertible W and equality in that product when W=Pσ. This includes zero G and dimension zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zhangli-zhanglirankoneproblemthree-exists-minimizing-permutation"),
                DeclarationHandle.Create(Module + ".exists_minimizing_permutation"),
                H("The permutation minimum and its equal factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, every complex n by n G and every unitarily invariant norm N, a permutation σ minimizes N(Pσ∘G), and N(Pσ∘G)N(Pσ⁻¹∘Gᵀ)=N(Pσ∘G)². Finiteness gives the minimum, while Pσ⁻¹∘Gᵀ=(Pσ∘G)ᵀ gives the equality. No rank hypothesis is needed for this statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-zhanglirankoneproblemthree-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The rank-one infimum equals the permutation minimum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n, every complex n by n G of rank at most one and every unitarily invariant norm N, the infimum over invertible W of N(W∘G)N(W⁻¹∘Gᵀ) equals the minimum over permutation matrices P of N(P∘G)², attained at a minimizing permutation. The statement supplies that permutation together with the lower bound for every invertible W and the equality at the permutation. Factor G and remove its phases to obtain common nonnegative diagonal weights. The expanding diagonal minimum bounds every balanced inverse-adjoint average, and optimization over its positive scale gives the product bound."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhang-li-2026-rank-one-hadamard-product-variational"),
                    ResolutionKind.Proved)))));
}
