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
    private static Formula Eval => new Formula.Apply(
        Seq(Operatorname, Grp(F.Id("Polynomial"), Dot, F.Id("eval"))), [X, P]);
    private static Formula All(Formula name, Formula type) =>
        Seq(Forall, Sp, name, Sp, Colon, Sp, type, Comma, Sp);
    private static Formula ImpliesDegree =>
        Seq(All(P, Call("Polynomial", Real)), Call("natDegree", P), Sp, Leq, Sp, R,
            Sp, Rightarrow, Sp);
    private static Formula Parenthesized(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Sp, Colon, Sp, type);
    private static Formula AsMeasure(Formula value) => Parenthesized(Typed(value, Call("Measure", Real)));
    private static Formula Integral(Formula integrand, Formula law) =>
        Seq(Int, Sp, integrand, Sp, F.Id("d"), AsMeasure(law));
    private static Formula Gaussian => Seq(Operatorname, Grp(F.Id("standardGaussian")));
    private static Formula OrderPlusOne => Parenthesized(Seq(R, Plus, D(1)));
    private static Formula Index => Call("Fin", Seq(R, Plus, D(1)));
    private static Formula I => F.Id("i");
    private static Formula J => F.Id("j");
    private static Formula C => F.Id("c");
    private static Formula IndexValue(Formula index) => Seq(index, Dot, F.Id("val"));
    private static Formula Gram => Call("gram", R, Mu);
    private static Formula Det => Call("det", Gram);
    private static Formula WindowPower(Formula power) =>
        Seq(Call("window", X), Sp, Cdot, Sp, new Formula.Power(X, power));
    private static Formula Perturbation(Formula law) => Call("perturbation", R, law, X);
    private static Formula SumOverJ(Formula term) =>
        Seq(new Formula.Subscript(Sum, Typed(J, Index)), Sp, term);
    private static Formula Correction =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, C, Sp, Eq, Sp, Call("mulVec", Call("adjugate", Gram),
            Seq(I, Sp, Mapsto, Sp, Integral(
                WindowPower(Seq(IndexValue(I), Plus, OrderPlusOne)), Mu))), Comma);
    private static Formula Scale =>
        new Formula.Fraction(D(1), Seq(D(2), Sp, Cdot, Sp, Parenthesized(Seq(D(1), Plus,
            Parenthesized(Seq(new Formula.Absolute(Det), Plus, SumOverJ(new Formula.Absolute(Call("c", J)))))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An adjugate tilt preserves low-order moments and separates Gaussian weak limits.",
        H("Polynomial moment perturbation of real probability laws"),
        Blocks(
            Definition("triangular-window", "window", "Triangular window",
                Seq(All(X, Real), Typed(Call("window", X), Real), Sp, Eq, Sp,
                    Call("max", Seq(D(1), Minus, new Formula.Absolute(X)), D(0))),
                "The window vanishes outside the closed unit interval."),
            Definition("windowed-gram", "gram", "Windowed Gram matrix",
                new Formula.Aligned([
                    Seq(Baseline, Typed(Gram, Call("Matrix", Index, Index, Real)), Comma),
                    Seq(All(Seq(I, Comma, J), Index), Call("gram", R, Mu, I, J), Sp, Eq, Sp,
                        Integral(WindowPower(Seq(IndexValue(I), Plus, IndexValue(J))), Mu))
                ]),
                "The entry is the windowed inner product of the two indexed monomials."),
            Definition("adjugate-perturbation", "perturbation", "Bounded continuous perturbation",
                new Formula.Aligned([
                    Seq(Baseline, Typed(Call("perturbation", R, Mu),
                        Seq(Real, new Formula.Power(To, F.Id("b")), Real)), Comma),
                    Correction,
                    Seq(All(X, Real), Perturbation(Mu), Sp, Eq, Sp, Det, Sp, Cdot, Sp,
                        WindowPower(Seq(R, Plus, D(1))), Sp, Minus, Sp,
                        SumOverJ(Parenthesized(Seq(Call("c", J), Sp, Cdot, Sp, WindowPower(IndexValue(J))))))
                ]),
                "Here c is the adjugate of the Gram matrix applied to the vector of cross moments."),
            Definition("adjugate-density", "density", "Real density",
                new Formula.Aligned([
                    Seq(Baseline, All(X, Real), Typed(Density(Mu), Real), Comma),
                    Correction,
                    Seq(Density(Mu), Sp, Eq, Sp, D(1), Plus, Scale, Sp, Cdot, Sp, Perturbation(Mu))
                ]),
                "The denominator uses the sum of the absolute values of the residual coefficients."),
            Definition("tilted-probability", "tilted", "Tilted probability law",
                new Formula.Aligned([
                    Seq(Baseline, Typed(Tilt(Mu), Law), Comma),
                    Seq(AsMeasure(Tilt(Mu)), Sp, Eq, Sp, Call("withDensity", AsMeasure(Mu),
                        Seq(X, Sp, Mapsto, Sp, new Formula.Apply(
                            Seq(Operatorname, Grp(F.Id("ENNReal"), Dot, F.Id("ofReal"))), [Density(Mu)]))))
                ]),
                "The density integrates to one with respect to the baseline."),
            Definition("standard-gaussian", "standardGaussian", "Standard Gaussian probability law",
                Seq(Typed(Gaussian, Law), Comma, Sp, AsMeasure(Gaussian), Sp, Eq, Sp,
                    Call("gaussianReal", D(0), D(1))),
                "The Gaussian has mean zero and variance one."),
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
                    Parenthesized(Seq(Frac, Grp(D(1)), Grp(D(2)), Sp, Leq, Sp, Density(Mu))),
                    Sp, Land, Sp, Parenthesized(Seq(Density(Mu), Sp, Leq, Sp,
                        Frac, Grp(D(3)), Grp(D(2))))))),
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
            Describe.Lean(DescribeId.Create("gaussian-gram-positivity"),
                DeclarationHandle.Create(Module + ".gaussian_gram_posDef"),
                H("Strict positivity of the Gaussian Gram matrix"),
                StatementSource.FromAuthor(Disp(Seq(Order,
                    Call("PosDef", Call("gram", R, Gaussian))))),
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
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(Order, Parenthesized(Seq(Integral(Perturbation(Gaussian), Gaussian), Sp, Lt, Sp,
                        Integral(Perturbation(Gaussian), Tilt(Gaussian)))), Sp, Land),
                    Parenthesized(Seq(Tilt(Gaussian), Sp, Neq, Sp, Gaussian))
                ]))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Gaussian Gram determinant is positive, so the residual polynomial is nonzero. "
                    + "The perturbation h has Gaussian expectation E[h] = 0 by degree-zero cancellation. "
                    + "Its Gaussian second moment E[h²] is strictly positive. Tilting increases the "
                    + "expectation of h by the positive step times E[h²], which separates the two laws."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, Formula formula, string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);
}
