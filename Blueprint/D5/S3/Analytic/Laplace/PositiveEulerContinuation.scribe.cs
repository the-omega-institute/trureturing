using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class PositiveEulerContinuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual positive Laplace transform satisfying an Euler equation converges throughout a meromorphic forcing half-plane regular on its real axis.",
        H("Positive Laplace convergence from an Euler equation"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-laplace-euler-full-convergence"),
            DeclarationHandle.Create("D5/S3/Analytic/Laplace/PositiveEulerContinuation.integrable_and_analytic_of_euler"),
            H("Convergence throughout the forcing half-plane"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let mu be any finite positive measure on any measurable space Omega, and let X : Omega to the reals be AEMeasurable and nonnegative almost everywhere. Fix a real a < 0. Let R : complex to complex be meromorphic on Re z > a and analytic at every real point x > a. Write G(z) = complexMGF X mu (-z), the actual integral of exp(-z X). Suppose z G''(z) + 2 G'(z) = R(z) for every complex z with Re z > 0. Then exp(-x X) is integrable for every real x > a, and this actual G is AnalyticOnNhd on the whole half-plane Re z > a. No integrability below zero, moment bound, derivative growth, continuation, or prescribed convergence cut is assumed.")),
                Paragraph(Text("The convergence set consists of the real s for which exp(-s X) is integrable. Positivity makes it upward closed, and finiteness of mu puts zero in it. If a missing parameter x > a existed, every member of the convergence set would be at least x. Its genuine infimum sigma would therefore satisfy a < x <= sigma <= 0. Every real t > sigma belongs to the interior of the convergence set. The reflected complex MGF theorem then makes the actual G holomorphic on Re z > sigma.")),
                Paragraph(Text("On that connected half-plane the Euler defect z G'' + 2 G' - R is meromorphic. Its order is infinity near the positive real point one because the given equation holds on Re z > 0. The meromorphic identity theorem propagates infinite order to every point of Re z > sigma. This is equality of punctured germs; it does not identify totalized values at poles. Regularity of R at the real point sigma supplies a full disk on which R is holomorphic. The actual G and its derivatives are holomorphic on the entire complex right half of this disk, so continuity upgrades the zero punctured defect to the pointwise Euler equation there.")),
                Paragraph(Text("If sigma is nonzero, EulerLocalContinuation.exists_extension_of_ne_zero constructs a holomorphic full-disk extension agreeing with G on the entire smaller complex right half-disk. If sigma is zero, the finite-measure dominated convergence theorem gives G(x) tending to the complex total mass as real x decreases to zero. Indeed, exp(-x X) has complex norm at most one almost everywhere for x > 0 and tends pointwise to one. EulerLocalContinuation.exists_extension_at_zero then removes the singular homogeneous solution and yields the same full complex agreement. Both cases contradict AbscissaSingularity.no_holomorphic_extension_at_abscissa at the actual convergence cut.")),
                Paragraph(Text("This combines the classical positive-measure Landau mechanism with a meromorphic Euler equation. It makes no literature originality claim and proves no unconditional statement about zeta zeros or RH. In the Robin route, the finite positive measure, the actual transformed theta-tail equation, and the real regularity of its meromorphic forcing must still be supplied by their own mathematical results. Robin's inequality for integers above 5040 and the eventual theta-tail comparison are separate application hypotheses."))),
            DescribeRole.Theorem))));
}
