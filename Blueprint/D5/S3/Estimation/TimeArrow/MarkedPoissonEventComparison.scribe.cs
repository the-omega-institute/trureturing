using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class MarkedPoissonEventComparisonDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Estimation/TimeArrow/MarkedPoissonEventComparison.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Marked Counts and Poisson Events", H("Actual Marked Counts and Poisson Events"), Blocks(

Describe.Lean(DescribeId.Create("actual-forward-count-tail"), DeclarationHandle.Create(Module + "actual_forward_marked_count_tail"),
 H("Forward count tails"), StatementSource.FromAuthor(Disp(ForwardTail())), AssessedProvenance.FromRepo(),
 Blocks(Paragraph(Text("The forward actual total-count tail plus the genuine product-Poisson tail at rates L(1+b(m(j)))/2 and L(1-b(m(j)))/2 is at most 3 exp(kL)/2^B. Both experiments share the same support and arbitrary integer s. The assumptions are M>=64, 1<=q<M, 0<r<1, compensation<1, distinct one or two marks, and s/M^2<=1/256."))), DescribeRole.Theorem),
Describe.Lean(DescribeId.Create("actual-forward-every-event"), DeclarationHandle.Create(Module + "actual_forward_marked_every_event"),
 H("Forward count events"), StatementSource.FromAuthor(Disp(ForwardEveryEvent())), AssessedProvenance.FromRepo(),
 Blocks(Paragraph(Text("For fixed 0<kappa<1 and Czero>=1, choose constants A>0, Mzero>=64 and etazero>0 before the support, marks, experiment, tuple cutoff and event. Assume r<=1-kappa and compensation<=1-kappa. The scale L=s/(2M) is real, L>=1 and L/M<=etazero. The same fixed support defines both actual history mass and directional exact Poisson rates. Every count event has absolute discrepancy at most A L^(k+1)/M times its comparison mass plus 3 exp(kL)/2^B, whenever B<=Czero L."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("markedpoissoneventcomparison-poissonproduct"), DeclarationHandle.Create(Module + "poissonProduct"),
            H("poissonProduct"), StatementSource.FromAuthor(Disp(ProductDef())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For a finite coordinate type iota and nonnegative rates mu, poissonProduct(mu) is the product of the genuine Poisson probability measures on the natural numbers. It contains all count tuples, without truncation."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("markedpoissoneventcomparison-product-poisson-tail"), DeclarationHandle.Create(Module + "product_poisson_tail"),
            H("product poisson tail"), StatementSource.FromAuthor(Disp(ProductTail())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The total-count tail is at most exp(sum_i mu(i))/2^B for every natural B, including zero rates. The proof evaluates the coordinate exponential series at tilt 2, forms the product integral and applies Markov inequality."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("markedpoissoneventcomparison-actual-reverse-marked-count-tail"), DeclarationHandle.Create(Module + "actual_reverse_marked_count_tail"),
            H("actual reverse marked count tail"), StatementSource.FromAuthor(Disp(NativeTail())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("L=s/(2M), and all 2k comparison rates are exactly L/2. The actual term sums reverse history masses with total marked count greater than B. The comparison term is the tail of the genuine product Poisson law. For M>=64 and s/M^2<=1/256 their sum is at most 3 exp(kL)/2^B, uniformly over the same fixed support, distinct marks and both experiments."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("markedpoissoneventcomparison-actual-reverse-marked-every-event"), DeclarationHandle.Create(Module + "actual_reverse_marked_every_event"),
            H("actual reverse marked every event"), StatementSource.FromAuthor(Disp(EveryEvent())), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For Czero>=1 there exist A>0, Mzero>=64 and etazero>0. Whenever L=s/(2M)>=1, L/M<=etazero and k=1 or 2, every natural B<=Czero L and every count event E satisfy the displayed bound. The count vector uses two copies of Fin(k), one per destination parity. ReverseEvent sums actual reverse history masses whose vector belongs to E. nu is the independent Poisson product with all rates L/2. The relative term is A L^(k+1)/M times nu(E); the additive term is 3 exp(kL)/2^B. Local estimates are summed on the finite total-count box, and both tails control its complement."))), DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula N(byte n) => D(n);
    private static Formula Call(string name, params Formula[] args)
    {
        var p = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) p.AddRange([Comma, Sp]); p.Add(args[i]); }
        p.Add(Close); return Seq([.. p]);
    }
    private static Formula Q(string names, Formula type, Formula body) =>
        Seq(Forall, Sp, Seq([.. names.Split(' ').SelectMany((s, i) => i == 0 ? new[] { V(s) } : new[] { Comma, V(s) })]), Colon, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) => Seq(Exists, Sp, V(name), Colon, type, Comma, Sp, body);
    private static Formula Fn(Formula a, Formula b) => Seq(a, To, Sp, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, Sp, b);
    private static Formula LtF(Formula a, Formula b) => Seq(a, Lt, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula SubF(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Mul(Formula a, Formula b) => Seq(Open, a, Close, Sp, Cdot, Sp, Open, b, Close);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
    private static Formula DivF(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula AndF(params Formula[] xs) => Join(xs, Land);
    private static Formula Join(Formula[] xs, Formula op)
    {
        var p = new List<Formula>();
        for (var i = 0; i < xs.Length; i++) { if (i > 0) p.AddRange([Sp, op, Sp]); p.Add(xs[i]); }
        return Seq([.. p]);
    }
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Sp, Rightarrow, Sp, b);
    private static Formula AbsF(Formula a) => Seq(Lvert, Sp, a, Sp, Rvert);
    private static Formula FinF(Formula a) => Call("Fin", a);
    private static Formula SupportF => Call("Support", V("M"), V("q"));
    private static Formula Marks => Fn(FinF(V("k")), FinF(V("M")));
    private static Formula Native(Formula body, string naturals = "M q s k") => Q(naturals, V("Nat"), Q("r", V("Real"), Q("S", SupportF, Q("m", Marks, body))));
    private static Formula Hyp => AndF(Le(N(1), V("q")), LtF(V("q"), V("M")), LtF(N(0), V("r")), LtF(V("r"), N(1)), LtF(Call("compensation", V("M"), V("q"), V("r")), N(1)), Call("injective", V("m")));
    private static Formula SmallK => Seq(Open, V("k"), Eq, N(1), Sp, Lor, Sp, V("k"), Eq, N(2), Close);
    private static Formula L => DivF(V("s"), Mul(N(2), V("M")));
    private static Formula ProductDef() => Q("iota", V("Type"), Seq(OpenBracket, Call("Fintype", V("iota")), CloseBracket, Sp,
        Q("mu", Fn(V("iota"), Call("NonnegativeReal")), Eqn(Call("poissonProduct", V("mu")), Call("productPoissonMeasures", V("mu"))))));
    private static Formula ProductTail() => Q("iota", V("Type"), Seq(OpenBracket, Call("Fintype", V("iota")), CloseBracket, Sp,
        Q("mu", Fn(V("iota"), Call("NonnegativeReal")), Q("B", V("Nat"), Le(Call("productPoissonTotalTail", V("mu"), V("B")), DivF(Call("exp", Call("sum", V("mu"))), Pow(N(2), V("B"))))))));
    private static Formula TailHyp => AndF(Hyp, SmallK, Le(D(6,4), V("M")), Le(DivF(V("s"), Pow(V("M"), N(2))), DivF(N(1), D(2,5,6))));
    private static Formula NativeTail() => Native(Imp(TailHyp, Q("e", Call("Experiment"), Q("B", V("Nat"),
        Le(Add(Call("reverseTotalTail", V("r"), V("S"), V("m"), V("s"), V("e"), V("B")), Call("fairPoissonTotalTail", V("k"), L, V("B"))), DivF(Mul(N(3), Call("exp", Mul(V("k"), L))), Pow(N(2), V("B"))))))));
    private static Formula EveryEvent()
    {
        Formula counts = Fn(Call("Sum", FinF(V("k")), FinF(V("k"))), V("Nat"));
        Formula nu = Call("fairPoissonEvent", V("k"), L, V("E"));
        Formula body = Native(Imp(AndF(Hyp, SmallK, Le(V("Mzero"), V("M")), Le(N(1), L), Le(DivF(L, V("M")), V("etazero"))),
            Q("e", Call("Experiment"), Q("B", V("Nat"), Imp(Le(V("B"), Mul(V("Czero"), L)), Q("E", Call("Set", counts),
                Le(AbsF(SubF(Call("reverseEvent", V("r"), V("S"), V("m"), V("s"), V("e"), V("E")), nu)),
                    Add(Mul(DivF(Mul(V("A"), Pow(L, Add(V("k"), N(1)))), V("M")), nu), DivF(Mul(N(3), Call("exp", Mul(V("k"), L))), Pow(N(2), V("B")))))))))));
        return Q("Czero", V("Real"), Imp(Le(N(1), V("Czero")), Ex("A", V("Real"), Ex("Mzero", V("Nat"), Ex("etazero", V("Real"), AndF(LtF(N(0), V("A")), Le(D(6,4), V("Mzero")), LtF(N(0), V("etazero")), body))))));
    }

    private static Formula ForwardHyp => AndF(Le(N(1), V("q")), LtF(V("q"), V("M")), LtF(N(0), V("r")),
        Le(V("r"), SubF(N(1), V("kappa"))), Le(Call("compensation", V("M"), V("q"), V("r")), SubF(N(1), V("kappa"))), Call("injective", V("m")));
    private static Formula ForwardTail() => Native(Imp(TailHyp, Q("e", Call("Experiment"), Q("B", V("Nat"),
        Le(Add(Call("forwardTotalTail", V("r"), V("S"), V("m"), V("s"), V("e"), V("B")),
            Call("directionalPoissonTotalTail", V("r"), V("S"), V("m"), L, V("B"))),
            DivF(Mul(N(3), Call("exp", Mul(V("k"), L))), Pow(N(2), V("B"))))))));
    private static Formula ForwardEveryEvent()
    {
        Formula counts = Fn(Call("Sum", FinF(V("k")), FinF(V("k"))), V("Nat"));
        Formula nu = Call("directionalPoissonEvent", V("r"), V("S"), V("m"), L, V("E"));
        Formula error = Add(Mul(DivF(Mul(V("A"), Pow(L, Add(V("k"), N(1)))), V("M")), nu), DivF(Mul(N(3), Call("exp", Mul(V("k"), L))), Pow(N(2), V("B"))));
        Formula bound = Le(AbsF(SubF(Call("forwardEvent", V("r"), V("S"), V("m"), V("s"), V("e"), V("E")), nu)), error);
        Formula events = Q("e", Call("Experiment"), Q("B", V("Nat"), Imp(Le(V("B"), Mul(V("Czero"), L)), Q("E", Call("Set", counts), bound))));
        Formula body = Native(Imp(AndF(ForwardHyp, SmallK, Le(V("Mzero"), V("M")), Le(N(1), L), Le(DivF(L, V("M")), V("etazero"))), events));
        Formula constants = Ex("A", V("Real"), Ex("Mzero", V("Nat"), Ex("etazero", V("Real"), AndF(LtF(N(0), V("A")), Le(D(6,4), V("Mzero")), LtF(N(0), V("etazero")), body))));
        return Q("kappa Czero", V("Real"), Imp(AndF(LtF(N(0), V("kappa")), LtF(V("kappa"), N(1)), Le(N(1), V("Czero"))), constants));
    }

}
