using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class MomentPerturbationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Analytic/Probability/MomentPerturbation";
    private static Formula R => F.Id("R");
    private static Formula X => F.Id("x");
    private static Formula P => F.Id("p");
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Law => Call("ProbabilityMeasure", Real);
    private static Formula Order => All(R, Nat);
    private static Formula Baseline => Seq(Order, All(Mu, Law));
    private static Formula Density(Formula law) => Call("density", R, law, X);
    private static Formula Tilt(Formula law) => Call("tilted", R, law);
    private static Formula Eval => Call("eval", P, X);
    private static Formula All(Formula name, Formula type) =>
        Seq(Forall, Sp, name, Sp, Colon, Sp, type, Comma, Sp);
    private static Formula ImpliesDegree =>
        Seq(All(P, Call("Polynomial", Real)), Call("natDegree", P), Sp, Leq, Sp, R,
            Sp, Rightarrow, Sp);
    private static Formula Integral(Formula integrand, Formula law) =>
        Seq(Int, Sp, integrand, Sp, F.Id("d"), law);
    private static Formula IntegrableEval(Formula law) =>
        Call("Integrable", Seq(X, Sp, Mapsto, Sp, Eval), law);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An adjugate tilt preserves low-order moments and separates Gaussian weak limits.",
        H("Polynomial moment perturbation of real probability laws"),
        Blocks(
            Paragraph(Text("Fix a real Borel probability law and a natural order. The triangular window is max(1 minus the absolute value of the observation, 0). The Gram entry at row i and column j is the expectation of the window times the power i plus j. The cross-moment vector uses powers i plus R plus 1. Multiply that vector by the adjugate to obtain the correction coefficients.")),
            Paragraph(Text("The bounded continuous function h is the window times the residual polynomial. The residual has the Gram determinant as its coefficient of degree R plus 1 and the negatives of the correction coefficients in degrees 0 through R. Add one to the sum of the absolute values of these coefficients, double that quantity and take its reciprocal to obtain the scale. The tilted law has density one plus the scaled perturbation. The symbol gamma denotes the standard Gaussian and integrals use the underlying measures.")),
            Describe.Lean(DescribeId.Create("continuous-density"),
                DeclarationHandle.Create(Module + ".continuous_density"),
                H("Continuity of the density in the observation"),
                StatementSource.FromAuthor(Disp(Seq(Baseline,
                    Call("Continuous", Seq(X, Sp, Mapsto, Sp, Density(Mu)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The density is an affine function of the bounded continuous perturbation."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("density-bounds"),
                DeclarationHandle.Create(Module + ".density_bounds"),
                H("Uniform density bounds"),
                StatementSource.FromAuthor(Disp(Seq(Baseline, All(X, Real),
                    Frac, Grp(D(1)), Grp(D(2)), Sp, Leq, Sp, Density(Mu), Sp, Land, Sp,
                    Density(Mu), Sp, Leq, Sp, Frac, Grp(D(3)), Grp(D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each windowed monomial has absolute value at most one. The scale bounds the resulting change of density in absolute value by one half."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-polynomial-cancellation"),
                DeclarationHandle.Create(Module + ".integral_eval_mul_density_sub_one"),
                H("Exact cancellation of the signed change"),
                StatementSource.FromAuthor(Disp(Seq(Baseline, ImpliesDegree,
                    Integral(Seq(Eval, Sp, Open, Density(Mu), Sp, Minus, Sp, D(1), Close), Mu),
                    Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The Gram matrix times the correction vector equals the determinant times the cross-moment vector. Integrating the residual term against each monomial through the chosen degree yields precisely these equations. Linearity extends the cancellation to all polynomials through that degree.")),
                    Paragraph(Text("The identity applies at singular Gram matrices as well. The signed integrand has compact support for every polynomial."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mass-one"),
                DeclarationHandle.Create(Module + ".integral_density"),
                H("Normalization"),
                StatementSource.FromAuthor(Disp(Seq(Baseline, Integral(Density(Mu), Mu),
                    Sp, Eq, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the constant polynomial in the signed cancellation identity."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("polynomial-moment-equality"),
                DeclarationHandle.Create(Module + ".integral_eval_tilted"),
                H("Preservation of integrable polynomial expectations"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(Baseline, ImpliesDegree, IntegrableEval(Mu), Sp, Rightarrow),
                    Seq(IntegrableEval(Tilt(Mu)), Sp, Land, Sp, Integral(Eval, Tilt(Mu)),
                        Sp, Eq, Sp, Integral(Eval, Mu))
                ]))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The density multiplies the baseline integrand by one plus the scaled correction. Its added part is integrable by compact support and has integral zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gaussian-gram-positivity"),
                DeclarationHandle.Create(Module + ".gaussian_gram_posDef"),
                H("Strict positivity of the Gaussian Gram matrix"),
                StatementSource.FromAuthor(Disp(Seq(Order,
                    Call("PosDef", Call("gram", R, GammaLower))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The quadratic form is the expectation of the window times the square of the polynomial with the test vector as coefficients. A nonzero polynomial has a point of nonvanishing inside the open window. Continuity and positive Gaussian mass on each nonempty open interval make the expectation strictly positive."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weak-continuity"),
                DeclarationHandle.Create(Module + ".continuous_tilted"),
                H("Weak continuity of the change of law"),
                StatementSource.FromAuthor(Disp(Seq(Order,
                    Call("Continuous", Seq(Mu, Sp, Mapsto, Sp, Tilt(Mu)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each coefficient depends continuously on the baseline through fixed bounded continuous moments, the determinant, the adjugate, and the positive scale denominator. For each bounded continuous test, the tilted integral is a finite linear combination of baseline integrals against fixed bounded continuous functions. This gives continuity for the weak topology on probability laws."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gaussian-test-separation"),
                DeclarationHandle.Create(Module + ".tilted_gaussian_separation"),
                H("A strict bounded continuous test for the Gaussian tilt"),
                StatementSource.FromAuthor(Disp(Seq(Order,
                    Integral(Call("h", R, GammaLower, X), GammaLower), Sp, Lt, Sp,
                    Integral(Call("h", R, GammaLower, X), Tilt(GammaLower)), Sp, Land, Sp,
                    Tilt(GammaLower), Sp, Neq, Sp, GammaLower))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Gaussian Gram determinant is positive, so the residual polynomial is nonzero. The perturbation itself has a strictly positive squared expectation. Its expectation increases by the positive scale times that squared expectation, which separates the two laws."))),
                DescribeRole.Theorem))));
}
