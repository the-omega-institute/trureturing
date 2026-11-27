using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using Fm = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class PlanarThetaFoundationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Montgomery =
        LibraryNoteRef.Create("D5/L/Fourier/montgomery1988minimal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized binary form has a summable Gaussian series, reciprocal-temperature " +
        "duality and additive lattice reduction. Preserving its quadratic form gives a " +
        "pointwise orthogonal lattice realization, including the degenerate zero-height case.",
        H("Planar theta geometry and orthogonal realization"), Blocks([.. Section0.Entries(), .. Section1.Entries()])));

    private static class Section0
    {
        public static DocumentBlock[] Entries() =>
        [
            Entry("Q", "Binary form", QDefinition(),
                "For y > 0, the form is the squared length in the normalized complex lattice.", true),
            Entry("F", "Planar theta series", FDefinition(),
                "Integer pairs index the Gaussian series, including the zero vector.", true),
            Entry("quadratic_control", "Uniform coercivity", ControlFormula(),
                "The inequality m squared plus n squared is bounded by twice the shifted " +
                "square plus (twice x squared plus one) times n squared. Taking the maximum " +
                "of the two coefficients gives one bound on each height rectangle."),
            Entry("summable", "Absolute convergence", SummableFormula(),
                "The Gram matrix is positive definite, with determinant one. Matrix Gaussian " +
                "summability applies after identifying two coordinates with an integer pair."),
            Entry("hasDerivAt_shear", "Shear derivative", DerivativeFormula(0),
                "On a bounded shear interval, the differentiated summands are bounded by " +
                "a constant times the squared coordinate size times a fixed Gaussian. " +
                "The one-dimensional polynomial Gaussian bounds give summability."),
            Entry("hasDerivAt_height", "Height derivative", DerivativeFormula(1),
                "Restricting height to an interval bounded away from zero controls the " +
                "reciprocal powers. A summable uniform derivative bound permits differentiation."),
            Entry("hasDerivAt_height_deriv", "Second height derivative", DerivativeFormula(2),
                "The second Gaussian derivative has a quadratic square term and a second-form " +
                "derivative term. Fourth Gaussian moments dominate the former and second " +
                "moments dominate the latter."),
            Entry("temperature_duality", "Reciprocal temperature", DualityFormula(),
                "Coordinate Poisson summation uses the inverse Gram matrix. In dimension " +
                "two its form is the original form after an integer quarter-turn. The " +
                "unit determinant and dimension two reduce the factor to reciprocal t."),
            Entry("latticePoint", "Normalized lattice points", PointDefinition(),
                "The two real coordinates use reciprocal square-root and square-root scaling.",
                true),
            Entry("lattice_geometry", "Lengths and injectivity", GeometryFormula(),
                "The imaginary coordinate recovers the second integer; the real coordinate " +
                "then recovers the first. The square-root identity gives the squared length."),
            Entry("basisTheta", "Theta in arbitrary basis coordinates", BasisThetaFormula(),
                "Complex basis vectors give the Euclidean lengths of integer combinations.",
                true),
            Entry("basis_reduction_geometry", "Geometric basis reduction",
                BasisReductionGeometryFormula(),
                "The modular coordinate change is an additive equivalence of integer " +
                "pairs. Its inverse, followed by the possible shear reflection, " +
                "identifies the original quadratic form with a reduced one at every " +
                "integer coordinate. For an arbitrary unit-area basis, the squared " +
                "length identity then retains this same additive reindexing. Thus " +
                "the reduction preserves both lengths and lattice addition.")
        ];

    private static DocumentBlock Entry(string name, string title, Formula formula, string body,
        bool definition = false) => Describe.Lean(
            DescribeId.Create("planartheta-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Fourier/PlanarThetaFoundation." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Montgomery),
            Blocks(Paragraph(Text(body))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula V(string s) => Fm.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Z => Seq(Mathbb, Grp(V("Z")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Pair => Seq(Z, Times, Z);
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Ex(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Pos(Formula a) => Lt(D(0), a);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula NegF(Formula a) => new Formula.Negate(a);
    private static Formula Sq(Formula a) => new Formula.Power(a, D(2));
    private static Formula Inv(Formula a) => new Formula.Power(a, NegF(D(1)));
    private static Formula AbsF(Formula a) => new Formula.Absolute(a);
    private static Formula Cast(Formula a, Formula t) => Seq(Open, a, Colon, t, Close);
    private static Formula Lam(string s, Formula t, Formula p) =>
        Seq(Open, V(s), Colon, t, Sp, Mapsto, Sp, p, Close);
    private static Formula Tsum(string s, Formula t, Formula p) => Call("tsum", Lam(s, t, p));
    private static Formula Q(Formula x, Formula y, Formula v) => Call("Q", x, y, v);
    private static Formula Theta(Formula t, Formula x, Formula y) => Call("F", t, x, y);
    private static Formula ExpF(Formula p) => Call("exp", p);
    private static Formula First(Formula v) => Cast(Call("fst", v), R);
    private static Formula Second(Formula v) => Cast(Call("snd", v), R);
    private static Formula Shift(Formula x, Formula v) => Add(First(v), Mul(Second(v), x));
    private static Formula Term(Formula t, Formula x, Formula y, Formula v) =>
        ExpF(NegF(Mul(Mul(Pi, t), Q(x, y, v))));
    private static Formula TXY(Formula p) => All("t", R, All("x", R, All("y", R, p)));
    private static Formula PositiveTXY(Formula p) =>
        TXY(Imp(Pos(V("t")), Imp(Pos(V("y")), p)));
    private static Formula AtPoint(Formula v) => Call("latticePoint", V("x"), V("y"), v);

    private static Formula QDefinition() => All("x", R, All("y", R, All("v", Pair,
        Equal(Q(V("x"), V("y"), V("v")),
            Add(Div(Sq(Shift(V("x"), V("v"))), V("y")),
                Mul(V("y"), Sq(Second(V("v")))))))));
    private static Formula FDefinition() => TXY(Equal(Theta(V("t"), V("x"), V("y")),
        Tsum("v", Pair, Term(V("t"), V("x"), V("y"), V("v")))));
    private static Formula SummableFormula() => PositiveTXY(Call("Summable",
        Lam("v", Pair, Term(V("t"), V("x"), V("y"), V("v")))));


    private static Formula ControlFormula() => All("M", R, All("l", R, All("u", R,
        All("x", R, All("y", R, Imp(Pos(V("l")),
            Imp(Le(AbsF(V("x")), V("M")), Imp(Le(V("l"), V("y")),
                Imp(Le(V("y"), V("u")), All("v", Pair,
                    Le(Add(Sq(First(V("v"))), Sq(Second(V("v")))),
                        Mul(Call("max", Mul(D(2), V("u")),
                            Div(Add(Mul(D(2), Sq(V("M"))), D(1)), V("l"))),
                            Q(V("x"), V("y"), V("v"))))))))))))));

    private static Formula Qx => Div(Mul(Mul(D(2), Second(V("v"))),
        Shift(V("x"), V("v"))), V("y"));
    private static Formula Qy => Sub(Sq(Second(V("v"))),
        Div(Sq(Shift(V("x"), V("v"))), Sq(V("y"))));
    private static Formula Qyy => Div(Mul(D(2), Sq(Shift(V("x"), V("v")))),
        new Formula.Power(V("y"), D(3)));
    private static Formula DerivativeFormula(int order)
    {
        var p = Mul(Pi, V("t"));
        var coefficient = order switch
        {
            0 => NegF(Mul(p, Qx)),
            1 => NegF(Mul(p, Qy)),
            _ => Sub(Mul(Sq(p), Sq(Qy)), Mul(p, Qyy))
        };
        var series = Tsum("v", Pair,
            Mul(coefficient, Term(V("t"), V("x"), V("y"), V("v"))));
        var function = order == 0
            ? Lam("a", R, Theta(V("t"), V("a"), V("y")))
            : order == 1 ? Lam("b", R, Theta(V("t"), V("x"), V("b")))
            : Lam("b", R, Call("deriv",
                Lam("z", R, Theta(V("t"), V("x"), V("z"))), V("b")));
        return PositiveTXY(Call("HasDerivAt", function, series, V(order == 0 ? "x" : "y")));
    }






    private static Formula DualityFormula() => PositiveTXY(Equal(
        Theta(V("t"), V("x"), V("y")),
        Mul(Inv(V("t")), Theta(Inv(V("t")), V("x"), V("y")))));


    private static Formula PointDefinition() => All("x", R, All("y", R, All("v", Pair,
        Equal(AtPoint(V("v")), Call("ComplexMk",
            Div(Shift(V("x"), V("v")), Call("sqrt", V("y"))),
            Mul(Call("sqrt", V("y")), Second(V("v"))))))));
    private static Formula GeometryFormula() => All("x", R, All("y", R, Imp(Pos(V("y")),
        And(Call("Injective", Lam("v", Pair, AtPoint(V("v")))), All("v", Pair,
            Equal(Call("normSq", AtPoint(V("v"))), Q(V("x"), V("y"), V("v"))))))));


    private static Formula BasisTerm() => ExpF(NegF(Mul(Mul(Pi, V("t")),
        Call("normSq", Add(Mul(Cast(Call("fst", V("v")), C), V("a")),
            Mul(Cast(Call("snd", V("v")), C), V("b")))))));
    private static Formula BasisThetaFormula() => All("t", R, All("a", C, All("b", C,
        Equal(Call("basisTheta", V("t"), V("a"), V("b")),
            Tsum("v", Pair, BasisTerm())))));
    private static Formula BasisReductionGeometryFormula() => All("a", C, All("b", C,
        Imp(Equal(AbsF(Sub(Mul(Call("re", V("a")), Call("im", V("b"))),
            Mul(Call("im", V("a")), Call("re", V("b"))))), D(1)),
            Ex("x", R, Ex("y", R, And(Le(D(0), V("x")),
                And(Le(V("x"), Div(D(1), D(2))), And(Pos(V("y")),
                    And(Le(D(1), Add(Sq(V("x")), Sq(V("y")))),
                        And(Le(Div(Call("sqrt", D(3)), D(2)), V("y")),
                            Ex("e", Call("AddEquiv", Pair, Pair), All("v", Pair,
                                Equal(Call("normSq", Add(
                                    Mul(Cast(Call("fst", V("v")), C), V("a")),
                                    Mul(Cast(Call("snd", V("v")), C), V("b")))),
                                    Q(V("x"), V("y"),
                                        Call("apply", V("e"), V("v"))))))))))))))));

    }

    private static class Section1
    {
        public static DocumentBlock[] Entries() =>
        [
            Describe.Lean(DescribeId.Create("theta-quadratic-reindex-isometry"),
                DeclarationHandle.Create(
                    "D5/S3/Fourier/PlanarThetaFoundation.basis_isometry_of_quadratic_reindex"),
                H("Pointwise lattice isometry"), StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(Montgomery), Blocks(Paragraph(Text(
                    "Take the original lattice vectors whose new coordinates are one zero " +
                    "and zero one. Additivity identifies every integer combination of " +
                    "these vectors. Their squared lengths and the squared length of " +
                    "their sum determine the full Gram matrix. This matrix agrees " +
                    "with the normalized shear-height basis. The resulting real-linear " +
                    "map preserves the norm on the entire plane. Its injectivity and " +
                    "finite dimension give surjectivity, hence a linear isometric " +
                    "equivalence. Inverting this map gives the asserted pointwise " +
                    "identification, including either orientation. At zero height both basis vectors " +
                    "vanish; negative height is incompatible with the quadratic identity."))), DescribeRole.Theorem)
        ];

    private static Formula V(string s) => Fm.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Z => Seq(Mathbb, Grp(V("Z")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Pair => Seq(Z, Times, Z);
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Ex(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Cast(Formula a) => Seq(Open, a, Colon, C, Close);
    private static Formula Point => Add(Mul(Cast(Call("fst", V("v"))), V("a")),
        Mul(Cast(Call("snd", V("v"))), V("b")));
    private static Formula Reindex => Call("apply", V("e"), V("v"));
    private static Formula Statement() => All("a", C, All("b", C, All("x", R, All("y", R,
        All("e", Call("AddEquiv", Pair, Pair),
            Imp(All("v", Pair, Equal(Call("normSq", Point),
                Call("Q", V("x"), V("y"), Reindex))),
                Ex("U", Call("LinearIsometryEquiv", R, C, C), All("v", Pair,
                    Equal(Call("apply", V("U"), Point),
                        Call("latticePoint", V("x"), V("y"), Reindex))))))))));

    }
}
