using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ComplementaryDyadicSupportLinesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ComplementaryDyadicSupportLines.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula And(params Formula[] f)
    {
        var r = f[^1];
        for (var j = f.Length - 2; j >= 0; j--) r = Par(Seq(f[j], Sp, Land, Sp, r));
        return r;
    }
    private static Formula Imp(Formula a, Formula b) => Par(Seq(a, Sp, Rightarrow, Sp, b));
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Add(Formula a, Formula b) => Par(Seq(a, Sp, Plus, Sp, b));
    private static Formula Sub(Formula a, Formula b) => Par(Seq(a, Sp, Minus, Sp, b));
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Pow(Formula x, Formula n) => new Formula.Power(x, n);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula B(Formula a) => Pow(D(2), a);
    private static Formula Indices(Formula a) => Call("Fin", Add(B(a), D(1)));
    private static Formula Laws(Formula a) => Seq(Indices(a), Sp, To, Sp, Real);
    private static Formula Sum(Formula a, Formula p) =>
        Seq(new Formula.Subscript(F.Sum, Seq(V("i"), Sp, InMacro, Sp, Indices(a))), Call("eval", p, V("i")));
    private static Formula Minimum(Formula p) => Call("min", p);
    private static Formula Cost(Formula p) => Call("L", p);
    private static Formula Nonnegative(Formula a, Formula p) =>
        All(V("i"), Indices(a), Leq(D(0), Call("eval", p, V("i"))));
    private static Formula Positive(Formula a, Formula p) =>
        All(V("i"), Indices(a), Lt(D(0), Call("eval", p, V("i"))));
    private static Formula Probability(Formula a, Formula p) => And(Nonnegative(a, p), Equal(Sum(a, p), D(1)));
    private static Formula SummableCost(Formula p) => Call("Summable",
        Seq(V("d"), Colon, Sp, Nat, Sp, Mapsto, Sp, Div(Call("R", p, V("d")), B(V("d")))));
    private static Formula Uniform(Formula a, Formula p) => All(V("i"), Indices(a),
        Equal(Call("eval", p, V("i")), Div(D(1), Add(B(a), D(1)))));
    private static Formula Iterated(Formula a, Formula j, Formula p) => Call("iterate", Call("T", a), j, p);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact dyadic law refutes a proposed support bound on every complementary simplex; "
        + "a strict high-side affine transformation preserves the tail series up to scale.",
        H("Complementary Dyadic Cost Laws"),
        Blocks(
            Describe.Lean(DescribeId.Create("two-mass-law"), DeclarationHandle.Create(Prefix + "counterexampleLaw"),
                H("The two-mass vector"), StatementSource.FromAuthor(LawFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write B=2^a and m=B+1. On labels with value less than "
                    + "2^(a-1)+1, pstar(a) has mass 1/B; on the remaining labels it has mass "
                    + "(B-2)/B^2. The subtraction in the natural exponent is truncated at zero. "
                    + "For a>=3 the multiplicities are B/2+1 and B/2. The residual R and cost L "
                    + "are reused from Dyadic Cost Support Lines: R(p,d)=2^d-sum_i floor(2^d p(i)) "
                    + "and L(p)=sum_d R(p,d)/2^d. The real tsum has its usual Lean convention "
                    + "outside the summable domain."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("counterexample"),
                DeclarationHandle.Create(Prefix + "complementary_counterexample"),
                H("A counterexample for every exponent"), StatementSource.FromAuthor(CounterexampleFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every natural a>=3, the vector is nonnegative and has total "
                        + "mass one. Its smallest coordinate is (B-2)/B^2, its series converges, "
                        + "and its cost is (a+1)(B-1)/B. With A=B(a+2), the gap "
                        + "A min(pstar)-L(pstar)=(B-a-3)/B is strictly positive. Consequently "
                        + "the universal inequality L(p)>=A min(p) on this real simplex is false.")),
                    Paragraph(Text("At depths d<a every floor is zero. At depths a+j with j<a "
                        + "the large-atom floor is 2^j and the small-atom floor is 2^j-1, including "
                        + "j=a-1. Thus R(pstar,a+j)=B/2-2^j, and all residuals from depth "
                        + "2a-1 onward vanish. The resulting finite geometric sum gives the exact "
                        + "cost. The inequality 2^a>a+3 holds for the whole range a>=3.")),
                    Paragraph(Text("This refutes the universal bound on m=2^a+1 stated in "
                        + "Whitebox section 70.1. The Mersenne bounds in section 67.10 concern "
                        + "m=2^h-1 and have different coefficients, so the conclusions are compatible."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("high-side-map"), DeclarationHandle.Create(Prefix + "highSideMap"),
                H("The strict high-side transformation"), StatementSource.FromAuthor(MapFormula()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("T_a(p)(i)=B^2 p(i)-(B-1) "
                    + "is an affine map on all real vectors. Its probability-law and cost identities "
                    + "below require the strict condition min(p)>t0=(B-1)/B^2. "
                    + "The notation iterate(T_a,k,p) means T_a applied k times to p."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("high-side-scaling"),
                DeclarationHandle.Create(Prefix + "complementary_high_side_scaling"),
                H("Scaling, finite exit, and the fixed point"), StatementSource.FromAuthor(ScalingFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let a>=3 and p be any nonnegative real vector of total mass "
                        + "one with t=min(p)>t0. Put q=T_a(p), s=min(q), "
                        + "H0=a+2-a/B-2/B^2, C=B(a+2)+2B^2 and d0=2(B-1). "
                        + "Then q is strictly positive with total mass one, s=B^2 t-(B-1), "
                        + "both cost series converge, L(p)=H0+L(q)/B^2, and "
                        + "L(p)-Ct+d0=(L(q)-Cs+d0)/B^2.")),
                    Paragraph(Text("Every coordinate of p lies strictly between t0 and 1/B. "
                        + "Floors before depth a are zero; at depth a+j with j<a, every floor "
                        + "is 2^j-1. Their prefix contribution is H0. At depth 2a+e the floor "
                        + "equals (B-1)2^e+floor(2^e q(i)), hence R(p,2a+e)=R(q,e). "
                        + "Splitting the convergent series establishes the scaling identities.")),
                    Paragraph(Text("For a nonuniform p there is a finite k such that all earlier "
                        + "iterates remain above t0, the kth iterate is still a strictly positive "
                        + "probability law, and its minimum lies in (0,t0]. Its minimum is "
                        + "1/(B+1)-(B^2)^j(1/(B+1)-t) at step j. Exponential growth and "
                        + "t<1/(B+1) give finite exit. The uniform vector is a fixed point and "
                        + "has cost (B(a+2)+2)/(B+1). Neither the boundary-jump statement "
                        + "70.41 nor the second-support statement 70.42 is asserted here."))), DescribeRole.Theorem))));

    private static Formula LawFormula()
    {
        var a = V("a"); var i = V("i"); var p = Call("pstar", a);
        var cut = Add(B(Sub(a, D(1))), D(1));
        var h = Lt(Call("val", i), cut);
        return Disp(All(a, Nat, All(i, Indices(a), And(
            Imp(h, Equal(Call("eval", p, i), Div(D(1), B(a)))),
            Imp(Seq(Neg, h), Equal(Call("eval", p, i), Div(Sub(B(a), D(2)), Pow(B(a), D(2)))))))));
    }

    private static Formula MapFormula()
    {
        var a = V("a"); var p = V("p"); var i = V("i");
        return Disp(All(a, Nat, All(p, Laws(a), All(i, Indices(a),
            Equal(Call("eval", Call("T", a, p), i),
                Sub(Mul(Pow(B(a), D(2)), Call("eval", p, i)), Sub(B(a), D(1))))))));
    }

    private static Formula CounterexampleFormula()
    {
        var a = V("a"); var b = B(a); var p = Call("pstar", a); var P = V("P");
        var t = Minimum(p); var A = Mul(b, Add(a, D(2)));
        var gap = Div(Sub(Sub(b, a), D(3)), b);
        var claim = All(P, Laws(a), Imp(Probability(a, P), Leq(Mul(A, Minimum(P)), Cost(P))));
        return Disp(All(a, Nat, Imp(Leq(D(3), a), And(Probability(a, p), SummableCost(p),
            Equal(t, Div(Sub(b, D(2)), Pow(b, D(2)))),
            Equal(Cost(p), Div(Mul(Add(a, D(1)), Sub(b, D(1))), b)),
            Equal(Sub(Mul(A, t), Cost(p)), gap), Lt(D(0), gap), Seq(Neg, Par(claim))))));
    }

    private static Formula ScalingFormula()
    {
        var a = V("a"); var b = B(a); var p = V("p"); var q = Call("T", a, p);
        var t = Minimum(p); var s = Minimum(q); var k = V("k"); var j = V("j");
        var t0 = Div(Sub(b, D(1)), Pow(b, D(2)));
        var H0 = Sub(Sub(Add(a, D(2)), Div(a, b)), Div(D(2), Pow(b, D(2))));
        var C = Add(Mul(b, Add(a, D(2))), Mul(D(2), Pow(b, D(2))));
        var d0 = Mul(D(2), Sub(b, D(1)));
        Formula Defect(Formula P) => Add(Sub(Cost(P), Mul(C, Minimum(P))), d0);
        var pk = Iterated(a, k, p);
        var exit = Seq(Exists, Sp, k, Colon, Sp, Nat, Comma, Sp, And(
            All(j, Nat, Imp(Lt(j, k), Lt(t0, Minimum(Iterated(a, j, p))))),
            Positive(a, pk), Equal(Sum(a, pk), D(1)), Lt(D(0), Minimum(pk)), Leq(Minimum(pk), t0)));
        var fixedPoint = Imp(Uniform(a, p), And(Equal(q, p),
            Equal(Cost(p), Div(Add(Mul(b, Add(a, D(2))), D(2)), Add(b, D(1))))));
        return Disp(All(a, Nat, Imp(Leq(D(3), a), All(p, Laws(a),
            Imp(And(Probability(a, p), Lt(t0, t)), And(SummableCost(p),
                Positive(a, q), Equal(Sum(a, q), D(1)), Equal(s, Sub(Mul(Pow(b, D(2)), t), Sub(b, D(1)))),
                SummableCost(q), Equal(Cost(p), Add(H0, Div(Cost(q), Pow(b, D(2))))),
                Equal(Defect(p), Div(Defect(q), Pow(b, D(2)))),
                Imp(Seq(Neg, Par(Uniform(a, p))), exit), fixedPoint)))))));
    }
}
