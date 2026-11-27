using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using Fm = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class HexagonalThetaStabilityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Montgomery =
        LibraryNoteRef.Create("D5/L/Fourier/montgomery1988minimal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least three-point exponential gap over all admissible orbit angles gives " +
        "an all-temperature lower bound for the hexagonal theta difference. " +
        "A freely chosen positive anchor supplies a cubic certificate, and a negative " +
        "orbit displacement supplies an exponential certificate.",
        H("Parametric hexagonal theta stability"), Blocks(
            Entry("hexGap", "Hyperbolic displacement", GapDefinition(),
                "For positive height, h is cosh of the hyperbolic distance from x plus iy " +
                "to one half plus i times square root three over two, minus one.", true),
            Entry("gapAmplitude", "Orbit amplitude", All("h", R,
                Equal(Amp, Call("sqrt", Mul(V("h"), Add(V("h"), D(2)))))),
                "The nonnegative amplitude is denoted by s. Its square equals h(h+2) " +
                "when h(h+2) is nonnegative.", true),
            Entry("threePointGap", "Three-point gap", ThreeDefinition(),
                "The three exponents are the deformations of one hexagonal orbit.", true),
            Entry("OrbitCoeff", "Admissible coefficients", CoeffDefinition(),
                "The first moment is zero and the second moment is three halves. " +
                "In particular, each coefficient lies between minus one and one.", true),
            Entry("orbitGap", "Uniform orbit bound", OrbitDefinition(),
                "The infimum over the admissible coefficients is the greatest lower " +
                "bound uniform in the unknown orbit angle. The coefficient set contains " +
                "(1,−1/2,−1/2), and every three-point gap is at least minus three.", true),
            Entry("cubicGap", "Cubic anchor certificate", CubicDefinition(),
                "The cubic Taylor polynomial of the exponential is a lower bound on " +
                "the entire real line.", true),
            Entry("escapeGap", "Exponential escape certificate", EscapeDefinition(),
                "At least one coefficient is at most minus one half. Its exponential " +
                "remainder controls escape once s/2 exceeds h.", true),
            Entry("orbitGap_lower", "Parametric lower certificates", Lower(),
                "The finite budget envelope, applied to probabilities " +
                "(2+c)/6, (2+d)/6, (2+e)/6 and again after negating c,d,e, " +
                "bounds the absolute third moment by three quarters. When h(h+2)≥0, " +
                "the displacement moments are 3h, 3h+9h²/2, and at most " +
                "9h²+15h³/2+3s³/4. " +
                "Taylor's inequality gives the cubic certificate at any positive b. " +
                "Convexity of the three-exponential sum and its value three at zero " +
                "extend it to every a at least b, with factor a/b. For the escape bound, " +
                "exp(u)−1−u is nonnegative everywhere and increasing for u nonnegative. " +
                "On the negative half-line the remainder is decreasing; the same least " +
                "displacement therefore supplies the escape bound for every real a. " +
                "For −2<h<0 the amplitude is zero, and both certificates still hold. " +
                "In that interval the cubic certificate follows directly from the cubic " +
                "Taylor bound and a nonpositive correction term."),
            Entry("hexagonal_theta_stability", "All-temperature orbit stability", Stability(),
                "Put a_v=πtQ_hex(v) and h=hexGap(x,y). The order-three rotation " +
                "preserves Q_hex. Each nonzero orbit has lengths " +
                "Q_hex(v)(1+h+s c_j), where the coefficients have zero first moment " +
                "and second moment three halves; zero amplitude permits any admissible " +
                "coefficients. Reindexing the three absolutely convergent theta sums gives " +
                "the identity 3(F_z−F_hex)=Σ_v exp(−a_v) threePointGap(h,a_v,c_v). " +
                "The zero vector contributes zero. Replacing each orbit gap by its " +
                "infimum proves the inequality. Its series converges absolutely: " +
                "the absolute summand is bounded by " +
                "3exp(−a_v)+3exp(−a_v(1+h−s)), with 1+h−s positive. " +
                "At t=0 each theta summand is one, so the theta series diverges; " +
                "t=0 is outside its convergence range. Lean's totalized sum " +
                "there is only a conventional value. " +
                "The following consequences have not been separately checked in Lean. " +
                "Far from the hexagonal point the bound is not a positive modulus. " +
                "For h≥2/3 one has s≤2h, and the admissible coefficients " +
                "(1,−1/2,−1/2) give orbitGap(h,a)≤exp(−a(h+s))+2exp(−a(h−s/2))−3<0 " +
                "for every a>0. Hence for every t>0 and every point with hexGap≥2/3, " +
                "for example x=3/2, y=√3/2, the whole orbit series is strictly " +
                "negative, and on that region the inequality alone does not recover " +
                "the hexagonal minimum. " +
                "For 0≤h≤1/25, choosing b=3 gives cubicGap(h,3)≥3h/2. " +
                "At t≥1 each nonzero a_v is at least three, so " +
                "F_z−F_hex≥(h/6)Σ_v a_v exp(−a_v)≥h αt exp(−αt), " +
                "where α=2π/√3. Temperature duality gives the corresponding bound " +
                "for t<1, with reciprocal temperature and factor 1/t. " +
                "On the same h interval, m=max(s/2−h,0) satisfies m²≥h/4; " +
                "exp(u)−1−u≥u²/2 for u≥0 gives the quadratic certificate " +
                "h(a²/8−3a). The number 1/25 is an h cutoff for the cubic " +
                "certificate; no optimality of this cutoff is asserted. A global lower " +
                "bound linear in h cannot hold: for fixed positive temperature and " +
                "y tending to infinity, F grows on the scale √y whereas h grows " +
                "on the scale y. Montgomery's minimal-theta theorem gives qualitative " +
                "hexagonal minimality. Local Hessian and local optimality precedents " +
                "include L. Bétermin, arXiv:1611.07820, and T. Leblé, arXiv:2511.03353. " +
                "M. Faulhuber and S. Steinerberger, arXiv:1903.06856, give local " +
                "coercivity in the deep-hole direction. These precedents are not " +
                "asserted to contain the parametric orbit bound stated here."))));

    private static DocumentBlock Entry(string name, string title, Formula formula, string body,
        bool definition = false) => Describe.Lean(
            DescribeId.Create("hexagonal-stability-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Fourier/HexagonalThetaStability." + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Montgomery),
            Blocks(Paragraph(Text(body))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula V(string s) => Fm.Id(s);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Z => Seq(Mathbb, Grp(V("Z")));
    private static Formula Pair => Call("Prod", Z, Z);
    private static Formula All(string s, Formula t, Formula p) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, p);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula NegF(Formula a) => new Formula.Negate(a);
    private static Formula Pow(Formula a, byte n) => new Formula.Power(a, D(n));
    private static Formula Sq(Formula a) => Pow(a, 2);
    private static Formula Root => Call("sqrt", D(3));
    private static Formula Height => Div(Root, D(2));
    private static Formula Half => Div(D(1), D(2));
    private static Formula Gap => Call("hexGap", V("x"), V("y"));
    private static Formula Amp => Call("gapAmplitude", V("h"));
    private static Formula Orb(Formula h, Formula a) => Call("orbitGap", h, a);
    private static Formula Cubic => Call("cubicGap", V("h"), V("b"));
    private static Formula Escape => Call("escapeGap", V("h"), V("a"));
    private static Formula Theta(Formula t, Formula x, Formula y) => Call("F", t, x, y);
    private static Formula Hex(Formula t) => Theta(t, Half, Height);
    private static Formula Difference => Sub(Theta(V("t"), V("x"), V("y")), Hex(V("t")));
    private static Formula ForXY(Formula p) => All("x", R, All("y", R, p));
    private static Formula GapDefinition() => ForXY(Equal(Gap,
        Div(Add(Sq(Sub(V("x"), Half)), Sq(Sub(V("y"), Height))), Mul(Root, V("y")))));
    private static Formula ExpDelta(string c) => Call("exp",
        NegF(Mul(V("a"), Add(V("h"), Mul(Amp, V(c))))));
    private static Formula Three => Call("threePointGap", V("h"), V("a"),
        V("c"), V("d"), V("e"));
    private static Formula ThreeDefinition() => All("h", R, All("a", R, All("c", R,
        All("d", R, All("e", R, Equal(Three,
            Sub(Add(Add(ExpDelta("c"), ExpDelta("d")), ExpDelta("e")), D(3))))))));
    private static Formula CoeffDefinition() => Equal(V("OrbitCoeff"), Call("setOf",
        Seq(Open, V("c"), V("d"), V("e"), Colon,
            Call("Prod", R, Call("Prod", R, R)), Sp, Mapsto, Sp,
            And(Equal(Add(Add(V("c"), V("d")), V("e")), D(0)),
                Equal(Add(Add(Sq(V("c")), Sq(V("d"))), Sq(V("e"))), Div(D(3), D(2)))),
            Close)));
    private static Formula OrbitDefinition() => All("h", R, All("a", R,
        Equal(Orb(V("h"), V("a")), Call("iInf", Seq(Open, V("c"), V("d"), V("e"),
            Colon, V("OrbitCoeff"), Sp, Mapsto, Sp, Three, Close)))));
    private static Formula CubicDefinition() => All("h", R, All("b", R, Equal(Cubic,
        Sub(Add(NegF(Mul(Mul(D(3), V("b")), V("h"))),
            Mul(Div(Sq(V("b")), D(2)),
                Add(Mul(D(3), V("h")), Div(Mul(D(9), Sq(V("h"))), D(2))))),
            Mul(Div(Pow(V("b"), 3), D(6)),
                Add(Add(Mul(D(9), Sq(V("h"))),
                    Div(Mul(D(1, 5), Pow(V("h"), 3)), D(2))),
                    Mul(Div(D(3), D(4)), Pow(Amp, 3))))))));
    private static Formula EscapeDefinition()
    {
        Formula m = Call("max", Sub(Div(Amp, D(2)), V("h")), D(0));
        return All("h", R, All("a", R, Equal(Escape,
            Sub(Sub(Sub(Call("exp", Mul(V("a"), m)), D(1)), Mul(V("a"), m)),
                Mul(Mul(D(3), V("a")), V("h"))))));
    }
    private static Formula Lower() => All("h", R, And(
            All("b", R, All("a", R, Imp(Lt(D(0), V("b")), Imp(Le(V("b"), V("a")),
                Le(Mul(Div(V("a"), V("b")), Cubic), Orb(V("h"), V("a"))))))),
            All("a", R, Le(Escape, Orb(V("h"), V("a"))))));
    private static Formula Argument => Mul(Mul(Pi, V("t")), Call("Q", Half, Height, V("v")));
    private static Formula Summand =>
        Mul(Orb(Gap, Argument), Call("exp", NegF(Argument)));
    private static Formula Series => Call("tsum",
        Seq(Open, V("v"), Colon, Pair, Sp, Mapsto, Sp, Summand, Close));
    private static Formula Stability() => All("t", R, ForXY(
        Imp(Lt(D(0), V("t")), Imp(Lt(D(0), V("y")), And(
            Call("Summable", Seq(Open, V("v"), Colon, Pair, Sp, Mapsto, Sp, Summand, Close)),
            Le(Mul(Div(D(1), D(3)), Series), Difference))))));
}
