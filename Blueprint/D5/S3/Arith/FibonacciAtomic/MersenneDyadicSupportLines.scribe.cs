using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class MersenneDyadicSupportLinesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/MersenneDyadicSupportLines.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) => Par(Seq(a, Sp, Land, Sp, b));
    private static Formula Imp(Formula a, Formula b) => Par(Seq(a, Sp, Rightarrow, Sp, b));
    private static Formula Power(Formula d) => new Formula.Power(D(2), d);
    private static Formula IndexedSum(Formula i, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(i, Sp, InMacro, Sp, domain)), body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two affine inequalities for the classical dyadic tail cost on every Mersenne real simplex.",
        H("Mersenne Dyadic Cost Support Lines"),
        Blocks(
            Describe.Lean(DescribeId.Create("simplex-data"),
                DeclarationHandle.Create(Prefix + "simplex_data"), H("Dyadic series bounds"),
                StatementSource.FromAuthor(SimplexDataFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any real vector on Fin(2^h-1) summing to one, "
                    + "each residual lies between zero and 2^h-1. Geometric domination "
                    + "makes the residual series summable and its cost nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("simplex-atom-upper"),
                DeclarationHandle.Create(Prefix + "simplex_atom_upper"), H("Individual atom bound"),
                StatementSource.FromAuthor(AtomUpperFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If every coordinate is at least t and their sum is "
                    + "one, any single coordinate is at most 1-(m-1)t, where m=2^h-1."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("scaling-floors"),
                DeclarationHandle.Create(Prefix + "scaling_floors"), H("Vanishing prefix floors"),
                StatementSource.FromAuthor(ScalingFloorsFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When every coordinate is nonnegative and M times "
                    + "each coordinate is below two, all floors before depth h vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("scaling"),
                DeclarationHandle.Create(Prefix + "scaling"), H("Exact high interval scaling"),
                StatementSource.FromAuthor(ScalingFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For h>=2, a vector of sum one with all coordinates "
                    + "at least t>1/M transforms to q(i)=Mp(i)-1, a nonnegative vector "
                    + "of sum one. Vanishing prefix floors and integer translation of "
                    + "the remaining floors give L(p)=h+L(q)/M."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("support-lines"),
            DeclarationHandle.Create(Prefix + "mersenne_support_lines"),
            H("Both supporting lines"), StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Let h be a natural number at least two, M=2^h and m=M-1. "
                + "For every nonnegative real probability vector p on Fin(m), let t be its "
                + "smallest coordinate. The dyadic series L(p) is summable, 0<=t<=1/m, "
                + "and (hM-2)t<=L(p) and ((h+2)M-2)t-2<=L(p). "
                + "The residual R and cost L are the definitions in Dyadic Cost Support Lines. "
                + "They accept arbitrary finite real vectors; an unsummable real tsum is zero. "
                + "Values outside the probability simplex have no sampling-cost interpretation.")),
                Paragraph(Text("In the low interval t<=1/M, put w(i)=(p(i)-t)/(1-mt). "
                + "These weights sum to one. Each scalar dyadic prefix of length h is at least "
                + "t times h+(h-2)w(i). To prove this, take the first dyadic depth k with "
                + "2^k p(i)>=1, when such a depth occurs by h. The preceding k floors vanish, "
                + "so their contribution is kp(i). The affine function (k-2)x+2/2^k lies "
                + "below this contribution, is nonnegative at zero and one, and has values "
                + "at least h/M and 2(h-1)/M at 1/M and 2/M. The inequalities "
                + "2^(h-k)>=h-k+1 verify those endpoint values. The convex decomposition "
                + "p(i)=(1-Mt)w(i)+Mt(1+w(i))/M then gives the scalar bound. "
                + "If no such depth occurs, the whole prefix equals hp(i). Summing the "
                + "scalar bounds gives the first supporting line without logarithms.")),
                Paragraph(Text("Above t=1/M, q(i)=Mp(i)-1 is another probability vector. "
                + "Every floor before depth h vanishes, and subsequent floors translate by "
                + "2^d. Consequently L(p)=h+L(q)/M. Repeatedly applying this identity to "
                + "a supporting inequality with an error of size (h+3)/M^r, and letting "
                + "r tend to infinity, gives the second line on the entire real simplex. "
                + "The first line follows from the second in the high interval. Zero atoms "
                + "and terminating dyadic expansions remain included. At h=2 the lines "
                + "are 6t and 14t-2 on the three-outcome simplex.")),
                Paragraph(Text("Only these numerical support inequalities are asserted. "
                + "They do not assert a sampler optimization, a batch phase transition, "
                + "an equality classification, or a value at every prescribed minimum atom."))),
            DescribeRole.Theorem))));

    private static Formula SimplexDataFormula()
    {
        var h = V("h"); var p = V("p"); var i = V("i"); var d = V("d");
        var m = Par(Seq(Power(h), Sp, Minus, Sp, D(1)));
        var indices = Call("Fin", m);
        var laws = Seq(indices, Sp, To, Sp, Real);
        var residualBounds = All(d, Nat, And(Seq(D(0), Sp, Le, Sp, Call("R", p, d)),
            Seq(Call("R", p, d), Sp, Le, Sp, m)));
        var series = Call("Summable", Seq(d, Colon, Sp, Nat, Sp, Mapsto, Sp,
            new Formula.Fraction(Call("R", p, d), Power(d))));
        return Disp(All(h, Nat, All(p, laws, Imp(Equal(IndexedSum(i, indices, Call("p", i)), D(1)),
            And(residualBounds, And(series, Seq(D(0), Sp, Le, Sp, Call("L", p))))))));
    }

    private static Formula AtomUpperFormula()
    {
        var h = V("h"); var p = V("p"); var i = V("i"); var t = V("t");
        var m = Par(Seq(Power(h), Sp, Minus, Sp, D(1)));
        var indices = Call("Fin", m);
        var laws = Seq(indices, Sp, To, Sp, Real);
        return Disp(All(h, Nat, All(p, laws, Imp(Equal(IndexedSum(i, indices, Call("p", i)), D(1)),
            All(t, Real, Imp(All(i, indices, Seq(t, Sp, Le, Sp, Call("p", i))),
                All(i, indices, Seq(Call("p", i), Sp, Le, Sp, D(1), Sp, Minus, Sp,
                    Par(Seq(m, Sp, Minus, Sp, D(1))), Sp, t))))))));
    }

    private static Formula ScalingFloorsFormula()
    {
        var h = V("h"); var p = V("p"); var i = V("i"); var d = V("d");
        var indices = Call("Fin", Par(Seq(Power(h), Sp, Minus, Sp, D(1))));
        var laws = Seq(indices, Sp, To, Sp, Real);
        var assumptions = All(i, indices, And(Seq(D(0), Sp, Le, Sp, Call("p", i)),
            Seq(Power(h), Sp, Call("p", i), Sp, Lt, Sp, D(2))));
        return Disp(All(h, Nat, All(p, laws, Imp(assumptions, All(i, indices, All(d, Nat,
            Imp(Seq(d, Sp, Lt, Sp, h), Equal(Call("floor", Seq(Power(d), Sp, Call("p", i))), D(0)))))))));
    }

    private static Formula ScalingFormula()
    {
        var h = V("h"); var p = V("p"); var q = V("q"); var i = V("i"); var t = V("t");
        var M = Power(h);
        var indices = Call("Fin", Par(Seq(M, Sp, Minus, Sp, D(1))));
        var laws = Seq(indices, Sp, To, Sp, Real);
        var assumptions = And(Equal(IndexedSum(i, indices, Call("p", i)), D(1)),
            And(All(i, indices, Seq(t, Sp, Le, Sp, Call("p", i))),
                Seq(new Formula.Fraction(D(1), M), Sp, Lt, Sp, t)));
        var qDefinition = Equal(q, Seq(i, Colon, Sp, indices, Sp, Mapsto, Sp,
            M, Sp, Call("p", i), Sp, Minus, Sp, D(1)));
        var result = And(All(i, indices, Seq(D(0), Sp, Le, Sp, Call("q", i))),
            And(Equal(IndexedSum(i, indices, Call("q", i)), D(1)),
                Equal(Call("L", p), Seq(h, Sp, Plus, Sp, new Formula.Fraction(Call("L", q), M)))));
        return Disp(All(h, Nat, Imp(Seq(D(2), Sp, Le, Sp, h), All(p, laws, All(t, Real,
            Imp(assumptions, All(q, laws, Imp(qDefinition, result))))))));
    }

    private static Formula ResultFormula()
    {
        var h = V("h"); var p = V("p"); var i = V("i"); var d = V("d"); var t = V("t");
        var M = Power(h);
        var m = Par(Seq(M, Sp, Minus, Sp, D(1)));
        var indices = Call("Fin", m);
        var laws = Seq(indices, Sp, To, Sp, Real);
        var term = new Formula.Fraction(Call("R", p, d), Power(d));
        var first = Par(Seq(h, Sp, M, Sp, Minus, Sp, D(2)));
        var second = Par(Seq(Par(Seq(h, Sp, Plus, Sp, D(2))), Sp, M, Sp, Minus, Sp, D(2)));
        var assumptions = And(Par(All(i, indices, Seq(D(0), Sp, Le, Sp, Call("p", i)))),
            Equal(IndexedSum(i, indices, Call("p", i)), D(1)));
        var bounds = And(Seq(D(0), Sp, Le, Sp, t),
            And(Seq(t, Sp, Le, Sp, new Formula.Fraction(D(1), m)),
            And(Seq(first, Sp, t, Sp, Le, Sp, Call("L", p)),
                Seq(second, Sp, t, Sp, Minus, Sp, D(2), Sp, Le, Sp, Call("L", p)))));
        return Disp(All(h, Nat, Imp(Seq(D(2), Sp, Le, Sp, h), All(p, laws, Imp(assumptions,
            And(Call("Summable", Seq(d, Colon, Sp, Nat, Sp, Mapsto, Sp, term)),
                All(t, Real, Imp(Equal(t, Call("min", p)), bounds))))))));
    }
}
