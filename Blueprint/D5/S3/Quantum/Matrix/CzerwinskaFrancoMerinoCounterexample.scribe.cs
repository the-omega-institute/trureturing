using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class CzerwinskaFrancoMerinoCounterexampleDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Eigenstructure/czerwinska2026radial");
    private const string Locator = "arXiv:2610.17393v1, §4, Conjecture 4.10";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Radial convexity with respect to the Frobenius norm does not imply matrix monotonicity "
            + "of the same degree: an explicit rational function separates the two properties in degree three.",
        H("A counterexample to the radial convexity characterization"),
        Blocks(
            Paragraph(Text("M. M. Czerwińska, J. A. Franco and A. Merino, Towards a Characterization "
                + "of Matrix Monotonicity via Radial Convexity. " + Locator + ".")),
            Paragraph(Text("Conjecture 4.10. Let f : (0, ∞) → R. Then f is radially convex of order n "
                + "(with respect to the Frobenius norm) if and only if f is matrix monotone of degree n.")),
            Paragraph(Text("arXiv:2610.17393v1, §4, directly after Conjecture 4.10, verbatim: “By Proposition 3.9, "
                + "matrix monotonicity of degree n implies radial convexity of order n. Thus, it remains to prove "
                + "the converse implication. The next theorem establishes the conjecture for n = 2.”")),
            Paragraph(Text("arXiv:2610.17393v1, §1, verbatim: “In degree 3, we show that radial convexity already "
                + "provides the principal minor conditions required for matrix monotonicity, leaving the sign of "
                + "the determinant of the Loewner matrix as the remaining obstruction.”")),
            Describe.Lean(
                DescribeId.Create("cfm-radial-convexity-conjecture"),
                DeclarationHandle.Create(Module + ".conjecture"),
                H("Conjecture 4.10 with its universal quantifiers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For each natural n≥1 and each real scalar function, the conjecture "
                    + "equates the two Frobenius endpoint inequalities on all ordered positive definite "
                    + "complex Hermitian triples with either uniformly increasing or uniformly decreasing "
                    + "Loewner monotonicity on all positive definite pairs. The function is represented on "
                    + "the real line; the positive-definite spectrum restricts its relevant values to (0,∞)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-certificate"),
                DeclarationHandle.Create(Module + ".finite_certificate"),
                H("Opposite signs on an ordered positive pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both endpoints are positive definite and A≤B. Their difference is "
                    + "(2/75)ww* for w=(2,3,6). The increment has quadratic form −2/111549375 at "
                    + "v=(−35,48,−15) and a strictly positive (0,0) entry. Its six inverses are verified "
                    + "by exact matrix multiplication. This excludes both monotonicity directions on the same pair."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("not-matrix-monotone"),
                DeclarationHandle.Create(Module + ".not_matrix_monotone"),
                H("Neither direction of matrix monotonicity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Continuous functional calculus identifies the scalar and matrix rational "
                    + "expressions. The finite certificate contradicts positivity in the increasing direction "
                    + "and diagonal positivity in the decreasing direction, as allowed by Definition 2.15."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cfm-radial-convexity-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Conjecture 4.10 is false in degree three"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Take ε=1/20000 and f(t)=(t+1)/(t+3)+(t+1)/(2t+4)−ε(t+1)/(3t+5). "
                        + "The Cayley map h(A)=I−2(A+I)⁻¹ is order preserving from the positive cone into "
                        + "−I<X<I, and continuous functional calculus identifies f(A) with "
                        + "g(h(A)), where g(X)=R_2(X)+R_3(X)−εR_4(X).")),
                    Paragraph(Text("Uniform endpoint resolvent factors and three-node spectral interpolation "
                        + "give positivity of Dg_C(g(V)−g(U)) at both endpoints C=U,V. The positive remainder "
                        + "coefficient is 1/3−324ε=4757/15000. The actual derivative and Frobenius trace pairing "
                        + "then make the squared endpoint distances monotone along ordered segments. Thus "
                        + "the full order-three radial property holds for every positive definite triple.")),
                    Paragraph(Text("For A=diag(1/3,1,3) and B=(1/25)[[11,4,8],[4,31,12],[8,12,99]], "
                        + "the difference B−A=(2/75)ww* with w=(2,3,6). At v=(−35,48,−15), the exact quadratic "
                        + "form v*(f(B)−f(A))v is −2/111549375, while the (0,0) entry of f(B)−f(A) is positive. "
                        + "Both possible matrix-monotonicity directions therefore fail.")),
                    Paragraph(Text("The paper's order-two differentiable theorem is unaffected. "
                        + "Direct sums extend the finite nonmonotonicity certificate to higher dimensions, "
                        + "but do not supply the all-matrix radial property there. A characterization of radial "
                        + "convexity and refutations in every higher dimension remain separate questions."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("czerwinska-franco-merino-2026-radial-convexity-matrix-monotonicity"),
                    ResolutionKind.Refuted)))));
}
