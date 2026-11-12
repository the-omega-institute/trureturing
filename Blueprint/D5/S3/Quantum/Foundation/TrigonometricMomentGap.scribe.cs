using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class TrigonometricMomentGapDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/TrigonometricMomentGap.";
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(params Formula[] xs) => xs.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula In(Formula a, Formula b) => Seq(a, InMacro, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Neq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, F.Lt, Sp, b);
    private static Formula App(Formula f, Formula x) => C("apply", f, x);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula X => C("Coordinates");
    private static Formula Space => C("Carrier");
    private static Formula Dual => C("LinearMap", R, Space, R);
    private static Formula K => C("base", C("cone"), C("unit"));
    private static Formula Proper(Formula f) => C("proper", C("cone"), C("unit"), f);
    private static Formula Conf(Formula f) => C("confirms", C("cone"), C("unit"), C("p"), f);
    private static Formula Num(int n) => D([.. n.ToString().Select(c => (byte)(c - '0'))]);
    private static Formula Q(int a, int b) => Seq(Frac, Grp(Num(a)), Grp(Num(b)));
    private static Formula Half(Formula a, Formula b) => Seq(Q(1, 2), Cdot, Open, a, Plus, b, Close);
    private static Formula Excludes(Formula x) => Ex("f", Dual, And(Conf(V("f")), Eq(App(V("f"), x), D(0))));

    public DocumentDefinition Create()
    {
        Formula a = V("a"), b = V("b"), f = V("f"), w = V("w"), theta = V("theta");
        Formula trig = C("trigonometric", a, b, theta);
        Formula result = And(
            Eq(K, C("image", C("lift"), C("body"))),
            Eq(C("pure", C("cone"), C("unit")), C("range", C("curve"))),
            C("IsCompact", K), C("IsCompact", C("body")), Eq(C("affineSpan", R, C("body")), C("top")),
            Eq(C("finrank", R, C("vectorSpan", R, C("body"))), D(4)),
            C("IsClosed", C("carrier", C("cone"))), C("Salient", C("cone")),
            Eq(C("span", R, C("carrier", C("cone"))), C("top")),
            All("a", R, All("b", R, All("w", Space,
                Iff(And(In(w, K), Eq(App(C("pairSupport", a, b), w), D(0))),
                    In(w, C("segment", R, C("curve", a), C("curve", b))))))),
            All("a", R, All("b", R, Eq(C("pairBase", C("cone"), C("unit"), C("curve", a), C("curve", b)),
                C("segment", R, C("curve", a), C("curve", b))))),
            C("wholePairBalls", C("cone"), C("unit")), Seq(Neg, Sp, C("allAntipodes", C("cone"), C("unit"))),
            All("f", Dual, Ex("a", R, Ex("b", X, Eq(f, C("effect", a, b))))),
            All("a", R, All("b", X, Iff(Proper(C("effect", a, b)),
                All("theta", R, And(Le(D(0), trig), Le(trig, D(1))))))),
            All("w", Space, Imp(In(w, C("cone")), Imp(Ne(w, D(0)), Lt(D(0), App(C("unit"), w))))),
            In(C("p"), K), In(C("x"), K), In(C("y"), K), In(C("mixed"), K), In(C("z"), K),
            And(Lt(D(0), C("angle")), Lt(C("angle"), C("pi"))),
            Eq(C("cos", C("angle")), Seq(F.Minus, Q(2, 3))),
            All("f", Dual, Imp(Conf(f), Le(Q(1, 10), App(f, C("mixed"))))),
            Conf(C("attainer")), Eq(App(C("attainer"), C("mixed")), Q(1, 10)),
            Eq(C("comparison", C("cone"), C("unit"), C("p"), C("mixed")), Q(1, 10)),
            Excludes(C("x")), Excludes(C("y")), Seq(Neg, Sp, C("zeroGluing", C("cone"), C("unit"))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The original second trigonometric moment body has an attained one-tenth comparison gap over its entire proper-effect interval.",
            H("The entire trigonometric moment body and its effects"), Blocks(
                Paragraph(Text("Use four real coordinates in the order cos(theta), sin(theta), cos(2 theta), sin(2 theta). The homogeneous carrier is their product with the original mass coordinate. The angle parameter ranges over all real numbers. Repeated periodic labels denote the same actual point; no angle inequality is used as a point-distinctness assumption.")),
                Def("Coordinates", "Four real coordinates", Eq(X, Seq(C("Fin", D(4)), To, Sp, R)), "Functions on Fin 4 with real values, using indices 0 through 3."),
                Def("Carrier", "The original homogeneous carrier", Eq(Space, Seq(R, Times, X)), "The first coordinate is mass, and the remaining four coordinates are unnormalized moments."),
                Def("momentCurve", "The complete moment curve", All("theta", R,
                    Eq(C("momentCurve", theta), C("tuple", C("cos", theta), C("sin", theta),
                        C("cos", Seq(D(2), Cdot, theta)), C("sin", Seq(D(2), Cdot, theta))))),
                    "The full real parameter domain is retained."),
                Def("body", "The original convex body", Eq(C("body"), C("convexHull", R, C("range", C("momentCurve")))),
                    "The convex hull of the entire curve, with no finite approximation."),
                Def("lift", "Normalization at mass one", All("w", X, Eq(App(C("lift"), w), C("pair", D(1), w))),
                    "This is an affine map into the original homogeneous carrier."),
                Def("curve", "Normalized original curve", All("theta", R,
                    Eq(C("curve", theta), App(C("lift"), C("momentCurve", theta)))),
                    "The homogeneous state with mass one and the four original moments."),
                Def("states", "The entire normalized state set", Eq(C("states"), C("convexHull", R, C("range", C("curve")))),
                    "Affine images commute with convex hull, so this is exactly lift applied to body."),
                Def("cone", "The original full homogeneous cone", Eq(C("cone"), C("radialHull", C("states"))),
                    "radialHull(S) means precisely the set of t times w, for every real t>=0 and every w in S. It includes zero. Closure under addition uses convexity of the entire state set; scalar closure uses every nonnegative real scalar."),
                Def("unit", "The unchanged original unit", All("w", Space, Eq(App(C("unit"), w), C("fst", w))),
                    "The first-coordinate real-linear map. It is strictly positive at every nonzero element of the cone."),
                Def("effect", "Every real-linear original effect", All("a", R, All("b", X, All("w", Space,
                    Eq(App(C("effect", a, b), w), Seq(a, Cdot, C("fst", w), Plus, C("dot", b, C("snd", w))))))),
                    "The dot product sums all four coordinates. Every real-linear map from Carrier to the reals has this form; properness is not assumed in this representation."),
                Def("trigonometric", "The full degree-two restriction", All("a", R, All("b", X, All("theta", R,
                    Eq(trig, Seq(a, Plus, App(b, D(0)), Cdot, C("cos", theta), Plus,
                        App(b, D(1)), Cdot, C("sin", theta), Plus,
                        App(b, D(2)), Cdot, C("cos", Seq(D(2), Cdot, theta)), Plus,
                        App(b, D(3)), Cdot, C("sin", Seq(D(2), Cdot, theta))))))),
                    "The original proper interval is exactly the set of these polynomials whose values lie in [0,1] at every real angle. Both implications are proved on the entire cone."),
                Def("pairSupport", "The full exposed two-point zero face", All("a", R, All("b", R, All("theta", R,
                    Eq(App(C("pairSupport", a, b), C("curve", theta)),
                        Seq(Open, D(1), F.Minus, C("cos", Seq(theta, F.Minus, a)), Close, Cdot,
                            Open, D(1), F.Minus, C("cos", Seq(theta, F.Minus, b)), Close))))),
                    "The real-linear coefficients are mass 1+cos(a-b)/2 and moments (-cos(a)-cos(b), -sin(a)-sin(b), cos(a+b)/2, sin(a+b)/2). The functional is nonnegative on the entire original cone. Its whole normalized zero face is exactly the segment of the two actual curve points. This equality also holds for coincident periodic labels, when the segment is a singleton. The entire original minimal cone-face base equals this segment. Distinct actual points give an injective affine chart of the closed one-dimensional ball."),
                Def("p", "The reference pure point", Eq(C("p"), C("curve", D(0))), "The reference point is proved extreme in the entire original base."),
                Def("x", "The first excluded mixed state", Eq(C("x"), Half(C("curve", Seq(C("pi"), F.Slash, D(2))), C("curve", Seq(F.Minus, C("pi"), F.Slash, D(2))))),
                    "The mean of the two quarter-turn curve points."),
                Def("y", "The second excluded state", Eq(C("y"), C("curve", C("pi"))), "The half-turn pure point."),
                Def("mixed", "The midpoint of the two excluded states", Eq(C("mixed"), Half(C("x"), C("y"))), "It has mass one and moment coordinates (-1/2,0,0,0)."),
                Def("angle", "The angle of the lower-bound decomposition", Eq(C("angle"), C("arccos", Seq(F.Minus, Q(2, 3)))),
                    "Its cosine is exactly -2/3."),
                Def("z", "An actual original mixed state", Eq(C("z"), Half(C("curve", C("angle")), C("curve", Seq(F.Minus, C("angle"))))),
                    "The two actual original curve states average to moments (-2/3,0,-1/9,0). The original mixed state equals (1/10)p+(9/10)z."),
                Def("attainer", "A globally proper attaining effect", Eq(C("attainer"), C("effect", Q(17, 50), C("tuple", Q(12, 25), D(0), Q(9, 50), D(0)))),
                    "On every curve point its value is ((3 cos(theta)+2)/5)^2. It lies in [0,1] on the whole curve and hence on the whole base. Its homogeneous extension is proper on the whole cone."),
                Describe.Lean(DescribeId.Create("attained-full-effect-gap"), DeclarationHandle.Create(Owner + "attained_full_effect_gap"),
                    H("An attained gap over all original confirming effects"), StatementSource.FromAuthor(Disp(result)),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("The base equals lift(body), and its entire extreme-point set equals the range of the complete normalized curve. Every linear effect has the stated five coefficients, and properness is equivalent to the global [0,1] trigonometric bounds. The body is compact and has full affine span in its four coordinates; the original homogeneous cone is closed, salient and generating, and the unit is strict. The entire minimal face of every pair is its segment, so all distinct original pure pairs satisfy wholePairBalls. Original global allAntipodes fails. All five displayed states belong to the original base. Every original proper confirmer of p reads at least 1/10 at mixed. The displayed attainer is itself an original proper confirmer and reads exactly 1/10 there. Thus the original sInf comparison equals 1/10, with its minimum attained. Proper cos-squared and half-one-plus-cos effects respectively exclude x and y. No original confirmer excludes their midpoint, so the original zeroGluing law fails.")),
                        Paragraph(Text("For each real angle a, the first harmonic cos(theta-a) has a unique maximizing actual curve point. A strict supporting inequality extends through convex hull, and the pinned exposedPoints_subset_extremePoints theorem makes its unique maximizer extreme. Conversely, the pinned extremePoints_convexHull_subset theorem excludes all other extreme points. The continuous periodic curve has compact range. Caratheodory gives a representation by at most five points; the compact simplex and the finite product of the whole compact curve then give compactness of the whole hull. Five actual curve evaluations force any vanishing linear functional to vanish identically, proving full affine span and cone generation. Strict positivity gives salience, and compactness of the normalized base gives cone closedness by subsequential limits. The product support has zeros precisely at the two actual curve points; its zero-face equality extends through the entire hull and the intersection of all cone faces. The segment is affinely parametrized by the full closed one-dimensional ball. Global effect bounds extend by convexity and nonnegative homogeneous scaling. Values at five curve points bound every proper effect coefficient, giving a common modulus of variation near curve(0). A sufficiently close distinct curve point cannot be excluded by any original proper confirmer of curve(0). The explicit segment chart makes these two pure endpoints antipodes, contradicting the original allAntipodes predicate. The actual decomposition mixed=(1/10)p+(9/10)z yields the lower bound for every proper confirmer. The attaining polynomial gives equality, and the existing attained_comparison theorem identifies the original lower envelope.")),
                        Paragraph(Text("The predecessor VII98.7 positive theorem in dimensions at most three is not supplied or reused here. Consequently this theorem does not certify the exact lowest-dimensional qualification in VII99.9."))), DescribeRole.Theorem))));
    }

    private static DocumentBlock Def(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
