using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class LorentzWeightedHolderControlDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/SeriesInequalities/LorentzWeightedHolderControl.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Estimation/holtznazarovperes2011smoothcoins");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted Bernstein kernels control Lorentz approximation at both endpoints.",
        H("Weighted Derivative Kernels and Holder Control"),
        Blocks(
            Paragraph(Text("Let I=[0,1] and let D(n,p)=max(sqrt(p(1-p)/n),1/n). "
                + "Write B(n,i,p) for the normalized Bernstein basis polynomial evaluated at p, "
                + "and Bder(l,n,i,p) for its lth derivative. Write F(j,f,p) for the jth "
                + "iterated derivative within I. The polynomial Q(m,r,f) is the actual Lorentz "
                + "jet operator sampled from these derivatives on the degree-m grid. Der(j,V,p) evaluates the jth polynomial derivative of V at p. "
                + "Qder(j,m,r,f,p) denotes its jth polynomial derivative evaluated at p. "
                + "The hypothesis H(r,b,f,A) means that f is C^r on I, A is nonnegative, "
                + "and the modulus of F(r,f,x)-F(r,f,y) is at most A times |x-y|^(b-r) "
                + "for every x,y in I. All derivatives and norms allow complex values.")),
            Entry("scale-positive", "delta_pos", "A positive endpoint scale", ScalePositive(),
                "The reciprocal grid size keeps the scale strictly positive, even at the endpoints.", false),
            Entry("weighted-kernel", "weighted_derivative_kernel_bound", "Uniform weighted derivative kernels", Kernel(),
                "This is Lemma 17 of Holtz, Nazarov and Peres. The same constant works for all "
                + "positive grid degrees and all points of the closed interval. The weight exponent "
                + "can be any nonnegative real number, and the derivative order can exceed the degree. "
                + "Centered exponential tilting bounds a complex disk; phase alignment then permits "
                + "a Cauchy derivative estimate for the entire weighted sum.", true),
            Entry("derivative-control", "holder_derivative_control", "Simultaneous derivative approximation", Derivative(),
                "The constant depends only on r and b. Taylor subtraction and exact Lorentz "
                + "reproduction give every residual derivative through r and the next derivative "
                + "of the approximating polynomial. This complex-valued seminorm formulation "
                + "is a deduction from the method of HNP Lemmas 19 and 20, and allows every b>r.", false),
            Entry("scale-comparison", "inverse_delta_comparison", "Comparison between two endpoint scales", Comparison(),
                "The scale at one point controls the reciprocal scale at another, with a correction "
                + "proportional to their separation. Both endpoints remain in the domain.", false),
            Entry("seminorm-control", "holder_seminorm_control", "Preservation of the top Holder seminorm", Seminorm(),
                "For r<b<r+1, near and distant pairs of points give a bound uniform in the grid "
                + "degree. This is the seminorm estimate underlying HNP Lemma 21. It does not "
                + "assert a bound for the complete C^b norm or for lower derivative sup norms.", false),
            Entry("weighted-stability", "weighted_lorentz_stability", "Weighted stability for complex polynomials", Stability(),
                "Here V is an arbitrary complex polynomial and L(m,r,V) is its actual Lorentz "
                + "operator. A weighted bound for the next derivative passes to L with a uniform "
                + "constant. This complex-polynomial version follows the argument of HNP Lemma 22; "
                + "it does not state that lemma for arbitrary functions." , false))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula, string prose, bool attested) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            attested ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula I(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(I(name), [.. args]);
    private static Formula Field(string name) => Seq(Mathbb, Grp(I(name)));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula Abs(Formula x) => new Formula.Absolute(x);
    private static Formula Fr(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Domain => Seq(OpenBracket, D(0), Comma, D(1), CloseBracket);
    private static Formula Fn => Seq(Field("R"), To, Sp, Field("C"));
    private static Formula Scale(Formula n, Formula p) => Call("D", n, p);
    private static Formula Point(string name, Formula body) => All(name, Domain, body);
    private static Formula Grid(string name, Formula body) => All(name, Field("N"), Seq(D(0), Lt, Sp, I(name), Rightarrow, Sp, body));
    private static Formula Constant(string name, Formula body) => Ex(name, Field("R"), Seq(D(0), Lt, Sp, I(name), Land, Sp, body));
    private static Formula Hyp(Formula body) => All("f", Fn, All("A", Field("R"),
        Seq(Call("H", I("r"), I("b"), I("f"), I("A")), Rightarrow, Sp, body)));
    private static Formula Smooth(Formula body, bool upper) => All("r", Field("N"), All("b", Field("R"),
        Seq(I("r"), Lt, Sp, I("b"), upper ? Seq(Land, Sp, I("b"), Lt, Sp, I("r"), Plus, D(1)) : Seq(), Rightarrow, Sp, body)));

    private static Formula ScalePositive() => Disp(Grid("n", All("p", Field("R"), Seq(D(0), Lt, Sp, Scale(I("n"), I("p"))))));
    private static Formula Kernel()
    {
        Formula n = I("n"), p = I("p"), i = I("i"), l = I("l"), g = I("g");
        Formula sum = Seq(Sum, Underscore, Grp(i, Eq, D(0)), Caret, Grp(n), Sp,
            Seq(Pow(Abs(Seq(Fr(i, n), Minus, p)), g), Cdot, Sp, Abs(Call("Bder", l, n, i, p))));
        return Disp(All("l", Field("N"), All("g", Field("R"), Seq(D(0), Le, Sp, g, Rightarrow, Sp,
            Constant("K", Grid("n", Point("p", Seq(sum, Le, Sp, I("K"), Cdot, Sp, Pow(Scale(n, p), Seq(g, Minus, l))))))))));
    }
    private static Formula Derivative()
    {
        Formula r = I("r"), b = I("b"), m = I("m"), p = I("p"), f = I("f"), j = I("j");
        Formula Bound(Formula order) => Seq(I("K"), Cdot, Sp, I("A"), Cdot, Sp, Pow(Scale(m, p), Seq(b, Minus, order)));
        Formula low = All("j", Field("N"), Seq(j, Le, Sp, r, Rightarrow, Sp,
            Norm(Seq(Call("F", j, f, p), Minus, Call("Qder", j, m, r, f, p))), Le, Sp, Bound(j)));
        Formula high = Seq(Norm(Call("Qder", Seq(r, Plus, D(1)), m, r, f, p)), Le, Sp, Bound(Par(Seq(r, Plus, D(1)))));
        return Disp(Smooth(Constant("K", Hyp(Grid("m", Point("p", Seq(Par(low), Land, Sp, high))))), false));
    }
    private static Formula Comparison() => Disp(Grid("m", Point("x", Point("y",
        Seq(Fr(Scale(I("m"), I("x")), Scale(I("m"), I("y"))), Le, Sp, D(1), Plus,
            Fr(Abs(Seq(I("x"), Minus, I("y"))), Scale(I("m"), I("x"))))))));
    private static Formula Seminorm() => Disp(Smooth(Constant("L", Hyp(Grid("m", Point("x", Point("y",
        Seq(Norm(Seq(Call("Qder", I("r"), I("m"), I("r"), I("f"), I("x")), Minus,
            Call("Qder", I("r"), I("m"), I("r"), I("f"), I("y")))), Le, Sp,
            I("L"), Cdot, Sp, I("A"), Cdot, Sp, Pow(Abs(Seq(I("x"), Minus, I("y"))), Seq(I("b"), Minus, I("r"))))))))), true));
    private static Formula Stability()
    {
        Formula r = I("r"), e = I("e"), m = I("m"), v = I("V"), a = I("A");
        Formula Der(Formula polynomial, Formula x) => Call("Der", Seq(r, Plus, D(1)), polynomial, x);
        Formula Weight(Formula x) => Seq(a, Cdot, Sp, Pow(Scale(m, x), Seq(Minus, e)));
        Formula result = Point("p", Seq(Norm(Der(Call("L", m, r, v), I("p"))), Le, Sp, I("K"), Cdot, Sp, Weight(I("p"))));
        Formula premise = Point("x", Seq(Norm(Der(v, I("x"))), Le, Sp, Weight(I("x"))));
        result = All("V", Seq(Field("C"), OpenBracket, I("X"), CloseBracket), Seq(Par(premise), Rightarrow, Sp, result));
        result = All("A", Field("R"), Seq(D(0), Le, Sp, a, Rightarrow, Sp, result));
        return Disp(All("r", Field("N"), All("e", Field("R"), Seq(D(0), Le, Sp, e, Land, Sp, e, Le, Sp, D(1), Rightarrow, Sp,
            Constant("K", Grid("m", result))))));
    }
}
