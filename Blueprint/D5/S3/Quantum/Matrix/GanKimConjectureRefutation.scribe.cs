using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class GanKimConjectureRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/GanKimConjectureRefutation";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Eigenstructure/gankim2024wasserstein");
    private const string Locator = "arXiv:2301.07934v4, §5, Conjecture 5.7";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two positive definite integer matrices reverse the required determinant comparison "
        + "between powers one half and one for every internal weight, refuting Conjecture 5.7.",
        H("A counterexample to Wasserstein power monotonicity"),
        Blocks(
            Paragraph(Text(Locator + ".")),
            Paragraph(Text("Conjecture 5.7. Let A, B ∈ Pm and t ∈ (0, 1). Then "
                + "(A^p ⋄t B^p)^{1/p} ց≺w log exp((1 − t) log A + t log B) as p ց 0.")),
            Paragraph(Text("A ⋄t B := (1 − t)² A + t² B + t(1 − t)[A(A^{−1} #B) + (A^{−1} #B)A]")),
            Describe.Lean(
                DescribeId.Create("gan-kim-wasserstein-conjecture"),
                DeclarationHandle.Create(Module + ".conjecture"),
                H("Conjecture 5.7 with monotonicity and convergence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every finite dimension m, all complex positive definite "
                    + "matrices A and B, and every real 0<t<1, let F_t(p)=(A^p ⋄t B^p)^(1/p). "
                    + "The decreasing arrow is expressed by the conjunction of F_t(p)≺wlog F_t(q) "
                    + "for every real 0<p<q, and Tendsto F_t (𝓝[>] 0) "
                    + "(𝓝 (exp((1−t) log A+t log B))). Weak log-majorization uses all prefix "
                    + "products of decreasingly sorted eigenvalues. The limit is retained as part "
                    + "of the conjecture even though its monotonicity conjunct supplies the contradiction."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gan-kim-wasserstein-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Conjecture 5.7 is false"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Take A=diag(81,1), B=[[41,40],[40,41]], p=1/2 and q=1. "
                        + "Their positive definite square roots are P=diag(9,1) and Q=[[5,4],[4,5]]. "
                        + "The positive definite matrices T_1=[[3,2],[2,7]]/sqrt(17) and "
                        + "T_2=[[21,20],[20,61]]/sqrt(881) satisfy T_1 P T_1=Q and T_2 A T_2=B. "
                        + "Riccati uniqueness therefore identifies them with P⁻¹ # Q and A⁻¹ # B.")),
                    Paragraph(Text("For equal-determinant positive definite two by two matrices "
                        + "X,Y with common determinant d and T=X⁻¹ # Y, det T=1 and "
                        + "det(X ⋄t Y)=d[1+t(1−t)(tr T−2)]². Set h=t(1−t), "
                        + "u=10/sqrt(17)−2 and v=82/sqrt(881)−2. Exact squared inequalities give "
                        + "u>2/5 and 0<v<4/5, so 2u>v>0. For every 0<t<1, "
                        + "(1+hu)²−(1+hv)=h(2u−v)+h²u²>0. Since both sides are positive, "
                        + "det F_t(1/2)=81(1+hu)⁴>81(1+hv)²=det F_t(1).")),
                    Paragraph(Text("Weak log-majorization at its full prefix would require "
                        + "det F_t(1/2)≤det F_t(1). The strict reverse inequality gives the "
                        + "contradiction. The conditional Theorem 5.6 is a separate assertion. "
                        + "The convergence statement without monotonicity is not decided by this result."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gan-kim-2024-wasserstein-weak-log-majorization"),
                    ResolutionKind.Refuted)))));
}
