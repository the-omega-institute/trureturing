using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using Fm = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class ThetaDerivativeBoundsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Montgomery =
        LibraryNoteRef.Create("D5/L/Fourier/montgomery1988minimal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real theta Fourier series and its translated Gaussian representation give " +
        "tail-sensitive derivative bounds for every positive parameter and stronger lower " +
        "bounds for parameters at most pi over six.",
        H("Fourier and Gaussian theta derivative bounds"), Blocks([.. Section0.Entries(), .. Section1.Entries(), .. Section2.Entries()])));

    private static class Section0
    {
        public static DocumentBlock[] Entries() =>
        [
            Entry("thetaFourier", "Real theta Fourier series", FourierDefinition(),
                "The constant term is one. Pairing positive and negative integer " +
                "frequencies produces twice the positive cosine series.", true),
            Entry("thetaSine", "Sine series", SineDefinition(),
                "The positive-frequency sine series carries the factor n from " +
                "differentiation in the translation parameter.", true),
            Entry("gaussian_moment", "Polynomial Gaussian moments", Moment(),
                "Restrict the summable integer Gaussian moments to nonnegative " +
                "indices and remove the zero index. This positive-frequency moment " +
                "is shared by the Fourier differentiation, the Gaussian Poisson " +
                "representation, and the planar shear comparison."),
            Entry("cos_summable", "Cosine Gaussian convergence", CosSummable(),
                "Every cosine factor has absolute value at most one. The zeroth " +
                "Gaussian moment therefore dominates the full positive-frequency " +
                "cosine series. This shared summability estimate also bounds " +
                "translated theta values by their zero-translation values."),
            Entry("hasDerivAt_thetaFourier", "Derivative of the Fourier series", Derivative(),
                "Every cosine summand has derivative negative two pi n times the " +
                "corresponding sine. Its absolute value is bounded independently " +
                "of b by the first Gaussian moment. Comparing n squared with n " +
                "gives a summable exponential majorant for every positive s, " +
                "so the differentiated series sums to negative four pi times the sine series."),
            Entry("thetaSine_first_mode", "First-mode error", FirstMode(),
                "The sine addition inequality bounds the absolute value of sin of " +
                "n u by n times the absolute value of sin u. After separating n " +
                "equal to one, each remaining term is therefore dominated by " +
                "n squared times its Gaussian weight times the absolute value " +
                "of sin of two pi b. Factoring out the first Gaussian gives " +
                "exactly the normalized tail. Absolute convergence justifies " +
                "summing the inequalities."),
            Entry("thetaFourier_derivative_bounds", "Tail-sensitive derivative bounds", Bounds(),
                "Separating the first mode gives the exact factors one plus the normalized Gaussian " +
                "tail in the upper bound and one minus that tail in the lower bound. The first-mode " +
                "estimate holds for every positive s. On the closed half-period the sine is " +
                "nonnegative, so the lower bound includes both endpoints."),
            Entry("thetaFourier_derivative_control", "Uniform sine control", Control(),
                "The sine addition bound reduces the derivative to a second Gaussian moment. The " +
                "inequality u exp of negative u at most two exp of negative one times exp of negative " +
                "u over two bounds this moment by the zeroth moment at half the parameter. This " +
                "yields the coefficient four exp of negative one divided by s.")
        ];

    private static DocumentBlock Entry(string name, string title, Formula formula, string body,
        bool definition = false) => Describe.Lean(
            DescribeId.Create("theta-fourier-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Fourier/ThetaDerivativeBounds." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Montgomery),
            Blocks(Paragraph(Text(body))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula V(string s) => Fm.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula NegF(Formula a) => new Formula.Negate(a);
    private static Formula Sq(Formula a) => new Formula.Power(a, D(2));
    private static Formula AbsF(Formula a) => new Formula.Absolute(a);
    private static Formula Lam(string s, Formula t, Formula p) =>
        Seq(Open, V(s), Colon, t, Sp, Mapsto, Sp, p, Close);
    private static Formula Tsum(Formula term) => Call("tsum", Lam("k", N, term));
    private static Formula F(Formula s, Formula b) => Call("thetaFourier", s, b);
    private static Formula S(Formula s, Formula b) => Call("thetaSine", s, b);
    private static Formula PosFreq => Add(V("k"), D(1));
    private static Formula Gaussian => Call("exp", NegF(Mul(Mul(Pi, V("s")), Sq(PosFreq))));
    private static Formula Angle => Mul(Mul(Mul(D(2), Pi), PosFreq), V("b"));
    private static Formula First => Call("exp", NegF(Mul(Pi, V("s"))));
    private static Formula Sin => Call("sin", Mul(Mul(D(2), Pi), V("b")));
    private static Formula AtDeriv => Call("deriv", Lam("z", R, F(V("s"), V("z"))), V("b"));
    private static Formula ForSB(Formula p) => All("s", R, All("b", R, p));
    private static Formula FourierDefinition() => ForSB(Equal(F(V("s"), V("b")),
        Add(D(1), Mul(D(2), Tsum(Mul(Gaussian, Call("cos", Angle)))))));
    private static Formula SineDefinition() => ForSB(Equal(S(V("s"), V("b")),
        Tsum(Mul(Mul(PosFreq, Gaussian), Call("sin", Angle)))));
    private static Formula Derivative() => ForSB(Imp(Lt(D(0), V("s")),
        Call("HasDerivAt", Lam("z", R, F(V("s"), V("z"))),
            Mul(Mul(NegF(D(4)), Pi), S(V("s"), V("b"))), V("b"))));
    private static Formula FirstMode() => ForSB(Imp(Lt(D(0), V("s")),
        Le(AbsF(Sub(S(V("s"), V("b")), Mul(First, Sin))),
            Mul(Mul(First, AbsF(Sin)), Call("gaussianTail", V("s"))))));
    private static Formula Bounds() => ForSB(Imp(Lt(D(0), V("s")),
        And(Le(AbsF(AtDeriv), Mul(Mul(Mul(Mul(D(4), Pi), First), AbsF(Sin)),
                Add(D(1), Call("gaussianTail", V("s"))))),
            Imp(Le(D(0), V("b")), Imp(Le(V("b"), Div(D(1), D(2))),
                Le(Mul(Mul(Mul(Mul(D(4), Pi), First), Sin),
                    Sub(D(1), Call("gaussianTail", V("s")))), NegF(AtDeriv)))))));

    private static Formula Control() => ForSB(Imp(Lt(D(0), V("s")),
        Le(AbsF(AtDeriv), Mul(Mul(Div(Mul(D(4), Call("exp", NegF(D(1)))), V("s")),
            Sub(F(Div(V("s"), D(2)), D(0)), D(1))), AbsF(Sin)))));

    private static Formula Moment() => All("s", R, Imp(Lt(D(0), V("s")),
        All("j", N, Call("Summable", Lam("k", N,
            Mul(new Formula.Power(PosFreq, V("j")), Gaussian))))));

    private static Formula CosSummable() => ForSB(Imp(Lt(D(0), V("s")),
        Call("Summable", Lam("k", N, Mul(Gaussian, Call("cos", Angle))))));

    }

    private static class Section1
    {
        public static DocumentBlock[] Entries() =>
        [
            Entry("real_fourier_int", "Integer Fourier frequencies", IntegerFourier(),
                "Split the absolutely convergent integer series into its zero term " +
                "and its two nonzero half-lines. The positive and negative " +
                "cosine terms agree, so the sum is exactly the positive-frequency " +
                "theta expansion. At zero translation this identity is the shared " +
                "bridge between the real integer Gaussian sum and theta."),
            Entry("thetaFourier_poisson", "Translated Gaussian representation", Poisson(),
                "Apply the Gaussian Poisson identity with coefficient pi s and angle two pi b. Taking real " +
                "parts gives the cosine Fourier sum. Its zero frequency is one, " +
                "and pairing the positive and negative frequencies gives twice " +
                "the positive cosine sum. The coefficient reduces to the reciprocal positive square " +
                "root of s. The transformed Gaussian is centered at b."),
            Entry("thetaFourier_zero_duality", "Reciprocal parameter at zero", Duality(),
                "At zero translation the cosine factors are one. Replacing s by " +
                "its reciprocal in the integer Fourier sum identifies the Gaussian " +
                "series from the Poisson formula. Positivity of s fixes the square root."),
            Entry("hasDerivAt_gaussianTranslate", "Translated Gaussian derivative", Translate(),
                "Near a fixed translation b, choose M equal to the absolute value " +
                "of b plus one. The quadratic inequality for the translated square " +
                "bounds each Gaussian by exp of negative a times n squared plus " +
                "two a M times the absolute value of n. The derivative contributes " +
                "at most two a times the sum of the absolute value of n and M. " +
                "The zeroth and first Gaussian moments are summable, so this uniform " +
                "bound justifies differentiation of the integer series."),
            Entry("thetaFourier_derivative_gaussian", "Signed Gaussian force", Force(),
                "Differentiate the translated Gaussian representation with " +
                "a equal to pi divided by s. Factoring the constant from the " +
                "differentiated series gives the negative factor two pi divided " +
                "by s times the square root of s. Thus positive force gives a " +
                "strictly negative derivative of the Fourier theta function.")
        ];

    private static DocumentBlock Entry(string name, string title, Formula formula, string body) =>
        Describe.Lean(DescribeId.Create("theta-poisson-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Fourier/ThetaDerivativeBounds." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Montgomery),
            Blocks(Paragraph(Text(body))));

    private static Formula V(string s) => Fm.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Z => Seq(Mathbb, Grp(V("Z")));
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula NegF(Formula a) => new Formula.Negate(a);
    private static Formula Sq(Formula a) => new Formula.Power(a, D(2));
    private static Formula Lam(string s, Formula t, Formula p) =>
        Seq(Open, V(s), Colon, t, Sp, Mapsto, Sp, p, Close);
    private static Formula Sum(Formula term) => Call("tsum", Lam("n", Z, term));
    private static Formula Theta(Formula s, Formula b) => Call("thetaFourier", s, b);
    private static Formula Root => Call("sqrt", V("s"));
    private static Formula G(Formula a, Formula b) =>
        Call("exp", NegF(Mul(a, Sq(Sub(b, V("n"))))));
    private static Formula ForSB(Formula p) => All("s", R, All("b", R,
        Imp(Lt(D(0), V("s")), p)));
    private static Formula Poisson() => ForSB(Equal(Theta(V("s"), V("b")),
        Mul(Div(D(1), Root), Sum(G(Div(Pi, V("s")), V("b"))))));
    private static Formula Duality() => All("s", R, Imp(Lt(D(0), V("s")),
        Equal(Theta(V("s"), D(0)),
            Mul(Div(D(1), Root), Theta(Div(D(1), V("s")), D(0))))));
    private static Formula Translate() => All("a", R, All("b", R,
        Imp(Lt(D(0), V("a")), Call("HasDerivAt",
            Lam("z", R, Sum(G(V("a"), V("z")))),
            Sum(Mul(Mul(NegF(Mul(D(2), V("a"))), Sub(V("b"), V("n"))),
                G(V("a"), V("b")))), V("b")))));
    private static Formula Force() => ForSB(Equal(
        Call("deriv", Lam("z", R, Theta(V("s"), V("z"))), V("b")),
        Mul(NegF(Div(Mul(D(2), Pi), Mul(V("s"), Root))),
            Sum(Mul(Sub(V("b"), V("n")), G(Div(Pi, V("s")), V("b")))))));
    private static Formula IntegerFourier() => ForSB(Equal(
        Sum(Mul(Call("exp", NegF(Mul(Mul(Pi, V("s")), Sq(V("n"))))),
            Call("cos", Mul(Mul(Mul(D(2), Pi), V("n")), V("b"))))),
        Theta(V("s"), V("b"))));

    }

    private static class Section2
    {
        public static DocumentBlock[] Entries() =>
        [
            Describe.Lean(
                DescribeId.Create("theta-small-derivative-bounds"),
                DeclarationHandle.Create(
                    "D5/S3/Fourier/ThetaDerivativeBounds.thetaFourier_small_derivative_bounds"),
                H("Uniform derivative bounds"), StatementSource.FromAuthor(Disp(Bounds())),
                AssessedProvenance.FromRepo(Montgomery), Blocks(Paragraph(Text(
                    "The sine addition inequality and a Gaussian second-moment estimate " +
                    "bound the derivative in absolute value using the uniform sine control and the " +
                    "zero-translation theta value at s over two, times the absolute " +
                    "value of sin of two pi b. Reciprocal-parameter duality bounds " +
                    "that zero-translation value by three over the square root of s, giving the upper constant six. " +
                    "For the lower bound, Poisson summation expresses the derivative " +
                    "as negative two pi divided by the product of s and its square " +
                    "root, multiplied by the Gaussian force with a equal to pi over s. " +
                    "The condition " +
                    "s at most pi over six implies a at least six. Gaussian pairing " +
                    "then gives the coefficient three tenths in the lower bound on the closed half-period. " +
                    "The upper bound holds for every real translation."))),
                DescribeRole.Theorem)
        ];

    private static Formula V(string s) => Fm.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula NegF(Formula a) => new Formula.Negate(a);
    private static Formula AbsF(Formula a) => new Formula.Absolute(a);
    private static Formula Lam(string s, Formula t, Formula p) =>
        Seq(Open, V(s), Colon, t, Sp, Mapsto, Sp, p, Close);
    private static Formula AtDeriv => Call("deriv", Lam("z", R,
        Call("thetaFourier", V("s"), V("z"))), V("b"));
    private static Formula Sin => Call("sin", Mul(Mul(D(2), Pi), V("b")));
    private static Formula Root => Call("sqrt", V("s"));
    private static Formula Bounds() => All("s", R, All("b", R,
        Imp(Lt(D(0), V("s")), Imp(Le(V("s"), Div(Pi, D(6))),
            And(Le(AbsF(AtDeriv), Mul(Div(D(6), Mul(V("s"), Root)), AbsF(Sin))),
                Imp(Le(D(0), V("b")), Imp(Le(V("b"), Div(D(1), D(2))),
                    Le(Mul(Mul(Div(D(3), Mul(Mul(D(1, 0), V("s")), Root)),
                        Call("exp", NegF(Div(Pi, Mul(D(4), V("s")))))), Sin),
                        NegF(AtDeriv)))))))));
    }
}
