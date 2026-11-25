using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class PositiveLaplaceContinuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Convergence of a positive Laplace transform from real regularity of its meromorphic continuation",
        H("Positive Laplace convergence across the possible abscissa"),
        Blocks(
            Describe.Lean(DescribeId.Create("positive-laplace-meromorphic-continuation"),
                DeclarationHandle.Create("D5/S3/Analytic/Laplace/PositiveLaplaceContinuation."
                    + "integrable_and_analytic_of_meromorphic_continuation"),
                H("Convergence, holomorphy and agreement of germs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let μ be a measure on a measurable space Ω, and let X : Ω → ℝ be "
                        + "AEMeasurable for μ and nonnegative μ-almost everywhere. Let a and b be real and suppose "
                        + "exp(−bX) is μ-integrable. Write L(z) for complexMGF X μ (−z), the actual "
                        + "Laplace integral of exp(−zX). Suppose H : ℂ → ℂ is meromorphic on Re(z)>a "
                        + "and analytic at each real x with a<x≤b. At some complex z₀ with a<Re(z₀) "
                        + "and b<Re(z₀), assume H and L agree on a neighborhood of z₀.")),
                    Paragraph(Text("Then exp(−xX) is integrable for every real x>a, and L is holomorphic "
                        + "on Re(z)>a. At each complex z of that half-plane, exp(−zX) is integrable, "
                        + "H agrees with L on a punctured neighborhood of z, and H(z)=L(z) whenever "
                        + "H is continuous at z.")),
                    Paragraph(Text("The real convergence set is upward closed because X≥0 almost everywhere. "
                        + "If convergence failed at x>a, the set would have an infimum σ with a<x≤σ≤b. "
                        + "PositiveEulerContinuation.analytic_laplace gives holomorphy to the right of σ. The meromorphic identity "
                        + "theorem propagates the local agreement as equality of punctured germs throughout "
                        + "that half-plane. Analyticity of H at σ and continuity upgrade the agreement on "
                        + "the right portion of a disk around σ to pointwise equality. This gives the "
                        + "holomorphic extension excluded by AbscissaSingularity.no_holomorphic_extension_at_abscissa. "
                        + "Once convergence holds throughout Re(z)>a, the same identity argument gives "
                        + "the stated germ equality and the pointwise equality at continuity points."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("affine-bound-laplace-continuation"),
                DeclarationHandle.Create("D5/S3/Analytic/Laplace/PositiveLaplaceContinuation."
                    + "analytic_continuation_of_affine_bound"),
                H("Laplace continuation from an eventual affine bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let f : ℝ → ℝ be continuous and let a, b, U, c, A and B be real, "
                        + "with a < b, U ≥ 0 and c ≠ 0. Suppose c f(t) ≤ A t + B eventually as t → ∞. "
                        + "For every complex s with Re(s) > b, assume exp(−(s−a)t) f(t) is integrable "
                        + "on (U, ∞) and that F(s) equals its integral there. Assume F : ℂ → ℂ "
                        + "is meromorphic on Re(s) > a and analytic at each real x > a. Then there "
                        + "exists L : ℂ → ℂ holomorphic on Re(s) > a with L(s) = F(s) whenever Re(s) > b.")),
                    Paragraph(Text("Choose a cutoff past which the affine gap A t + B − c f(t) "
                        + "is nonnegative and multiply it by exp(−(b+1−a)t) to obtain a finite positive "
                        + "measure on that tail. Its Laplace transform has a real-regular meromorphic "
                        + "continuation obtained by subtracting the finite head and comparing with the "
                        + "affine transform. Positive Laplace convergence extends the gap transform. "
                        + "Subtracting it from the affine transform, dividing by c and restoring the "
                        + "finite head produces the required L."))),
                DescribeRole.Theorem))));
}
