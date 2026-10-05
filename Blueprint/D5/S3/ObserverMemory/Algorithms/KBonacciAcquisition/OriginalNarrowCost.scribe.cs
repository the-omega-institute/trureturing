using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class OriginalNarrowCostDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/OriginalNarrowCost.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary initial record labels require first-window waiting and binary depth.",
        H("A waiting lower bound for arbitrary initial record targets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-kbonacci-record"),
                DeclarationHandle.Create(Owner + "OriginalRecord"),
                H("The joint original record of a literal history"),
                StatementSource.FromAuthor(Disp(RecordFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The accepted record consists of the original low-bit-first scalar value, "
                    + "the literal word length modulo k+1, and the scanner's actual final run of ones. "
                    + "All three coordinates come from the same word. A rejected word has record none."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-kbonacci-fiber-feasible"),
                DeclarationHandle.Create(Owner + "OriginalFiberFeasible"),
                H("Uniform success on the whole initial free-value fiber"),
                StatementSource.FromAuthor(Disp(FeasibleFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "One selector receives the free initial endpoint and a chronological archive "
                        + "of complete issued words with their endpoint replies. At each step it either "
                        + "stops or appends every position of its chosen word before reading the new endpoint. "
                        + "The target is f of the INITIAL joint record throughout execution. Correctness "
                        + "quantifies every actual initial history of AllowedBlock actions in the fixed-value "
                        + "fiber, including every realizable initial tail. No phase or tail is revealed.")),
                    Paragraph(Text(
                        "When a is true, every word chosen by the selector is internally admissible; "
                        + "when a is false, every complete Boolean word is allowed. The scanner still checks "
                        + "actual seams in either alphabet. The initial rejection stops freely with f(none). "
                        + "Each issued block costs one, including zero words, padding, and rejected blocks. "
                        + "Early stops may use less than the uniform budget d."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-kbonacci-fiber-cost"),
                DeclarationHandle.Create(Owner + "OriginalFiberCost"),
                H("Least uniform acquisition cost, with infinity allowed"),
                StatementSource.FromAuthor(Disp(CostFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The cost is the infimum in ENat of all feasible natural budgets. "
                    + "If there is no feasible budget, the infimum of the empty family is infinity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-kbonacci-narrow-cost-lower"),
                DeclarationHandle.Create(Owner + "original_cost_lower"),
                H("First-window waiting plus binary discrimination"),
                StatementSource.FromAuthor(Disp(LowerFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here g=gcd(m,k+1), u=m/g, p=(k+1)/g, and h=p/u uses natural floor division. "
                        + "There are u tail-zero sources q(j), indexed by j in Fin u, and n is the number "
                        + "of distinct INITIAL labels f(q(j)). Nat.clog(2,n) is the ceiling binary logarithm; positivek denotes the positivity proof implied by k>=2. "
                        + "The target f is otherwise arbitrary and may depend on the INITIAL tail.")),
                    Paragraph(Text(
                        "Every q(j) is realized by an actual allowed history. A successful lawful selector "
                        + "gives a decision tree with the same finite budget, the same complete-word actions, "
                        + "and the same endpoint-dependent continuation. Uniform rejection of the first word "
                        + "would erase all distinct labels. Otherwise its two successful replies split the label "
                        + "image, so one child retains at least ceiling(n/2) labels, hence at least two.")),
                    Paragraph(Text(
                        "The coefficients vanish at every continuation position from m through h*m-1 "
                        + "for all selected phases. The sources in the chosen child have the same current "
                        + "value and tail. Any subsequent adaptive words therefore give a shared chronological "
                        + "archive for h-1 paid steps, or reject all these sources together. Uniform rejection "
                        + "and an early stop cannot recover their distinct INITIAL labels. After that shared "
                        + "prefix, binary branching needs at least clog(2,ceiling(n/2)) further words. "
                        + "The integer logarithm recurrence yields h+clog(2,n)-1.")),
                    Paragraph(Text(
                        "No lower bound g>=2 or root first-zero condition is required. The case g=1 is "
                        + "included. When h=1 the quiet prefix has length zero and the estimate is the binary "
                        + "depth bound. The inequality also holds for targets whose cost is infinity."))),
                DescribeRole.Theorem))));

    private static Formula RecordFormula()
    {
        var k = F.Id("k"); var hk = F.Id("hk"); var w = F.Id("w"); var t = F.Id("tail");
        var record = Triple(Call("value", k, D(0), w),
            Call("cast", Call("length", w), Call("ZMod", Add(k, D(1)))), Call("val", t));
        return All(k, NatType(), All(hk, Rel(D(0), Lt, k), All(w, Call("List", Op("Bool")),
            Equal(Call("OriginalRecord", k, hk, w),
                Call("map", Call("eval", Call("scanner", k, hk), w),
                    Lam(t, Call("Fin", k), record))))));
    }

    private static Formula FeasibleFormula()
    {
        var Y = F.Id("Y"); var k = F.Id("k"); var m = F.Id("m"); var hk = F.Id("hk");
        var a = F.Id("a"); var f = F.Id("f"); var v = F.Id("v"); var d = F.Id("d");
        var pi = F.Id("pi"); var y = F.Id("y"); var archive = F.Id("archive"); var B = F.Id("B");
        var history = F.Id("history"); var action = F.Id("action"); var w = F.Id("w"); var c = F.Id("c");
        var legality = All(y, ObservationType(), All(archive, Call("Archive", m), All(B, WordType(m),
            Imp(Equal(App(pi, y, archive), Call("inr", B)),
                Imp(Equal(a, Op("true")), Call("DBonacciAdmissible", k, m, B))))));
        var bottom = Equal(App(pi, Op("none"), Nil()), Call("inl", App(f, Op("none"))));
        var word = Call("flatMap", history, Lam(action, Call("AllowedBlock", k, m, a),
            Call("ofFn", Call("val", action))));
        var success = All(history, Call("List", Call("AllowedBlock", k, m, a)),
            Let(w, word, Imp(Equal(Call("output", k, hk, w), Call("some", v)),
                Ex(c, NatType(), And(Rel(c, Leq, d),
                    Equal(Call("execute", k, hk, pi, d, w, Call("some", v), Nil()),
                        Call("some", Pair(App(f, Call("OriginalRecord", k, hk, w)), c))))))));
        return FiberParameters(Y, k, m, hk, a, f, v,
            All(d, NatType(), Equal(Call("OriginalFiberFeasible", k, m, hk, a, f, v, d),
                Ex(pi, Call("Selector", m, Y), And(legality, bottom, success)))));
    }

    private static Formula CostFormula()
    {
        var Y = F.Id("Y"); var k = F.Id("k"); var m = F.Id("m"); var hk = F.Id("hk");
        var a = F.Id("a"); var f = F.Id("f"); var v = F.Id("v"); var d = F.Id("d"); var b = F.Id("budget");
        var budgets = Call("Subtype", Lam(d, NatType(), Call("OriginalFiberFeasible", k, m, hk, a, f, v, d)));
        return FiberParameters(Y, k, m, hk, a, f, v,
            Equal(Call("OriginalFiberCost", k, m, hk, a, f, v),
                Call("iInf", Lam(b, budgets, Call("cast", Call("val", b), Op("ENat"))))));
    }

    private static Formula LowerFormula()
    {
        var Y = F.Id("Y"); var k = F.Id("k"); var m = F.Id("m");
        var f = F.Id("f"); var v = F.Id("v"); var a = F.Id("a");
        var g = F.Id("g"); var u = F.Id("u"); var p = F.Id("p"); var h = F.Id("h");
        var q = F.Id("q"); var j = F.Id("j"); var n = F.Id("n"); var T = Add(k, D(1));
        var source = Lam(j, Call("Fin", u), Call("some", Triple(v,
            Seq(Minus, Call("cast", Multiply(Call("val", j), g), Call("ZMod", T))), D(0))));
        var labels = Call("range", Lam(j, Call("Fin", u), App(f, App(q, j))));
        var lower = Call("cast", Call("natSub", Add(h, Call("clog", D(2), n)), D(1)), Op("ENat"));
        var result = Imp(Rel(D(3), Leq, n),
            Rel(lower, Leq, Call("OriginalFiberCost", k, m, Op("positivek"), a, f, v)));
        return All(Y, Op("Type"), All(k, NatType(), All(m, NatType(),
            Imp(And(Rel(D(2), Leq, k), Rel(D(1), Leq, m), Rel(m, Lt, T)),
                All(f, Rel(Call("Option", Call("LiveRecord", k)), To, Y),
                    All(v, Call("ZMod", D(2)), All(a, Op("Bool"),
                        Let(g, Call("gcd", m, T), Let(u, Call("div", m, g),
                            Let(p, Call("div", T, g), Let(h, Call("div", p, u),
                                Let(q, source, Let(n, Call("card", labels), result)))))))))))));
    }

    private static Formula FiberParameters(Formula Y, Formula k, Formula m, Formula hk,
        Formula a, Formula f, Formula v, Formula body) =>
        All(Y, Op("Type"), All(k, NatType(), All(m, NatType(), All(hk, Rel(D(0), Lt, k),
            All(a, Op("Bool"), All(f, Rel(Call("Option", Call("LiveRecord", k)), To, Y),
                All(v, Call("ZMod", D(2)), body)))))));
    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ObservationType() => Call("Option", Call("ZMod", D(2)));
    private static Formula WordType(Formula m) => Rel(Call("Fin", m), To, Op("Bool"));
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, b, Close);
    private static Formula Triple(Formula a, Formula b, Formula c) => Seq(Open, a, Comma, b, Comma, c, Close);
    private static Formula Nil() => Seq(OpenBracket, CloseBracket);
    private static Formula Rel(Formula a, Formula relation, Formula b) => Seq(a, Sp, relation, Sp, b);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula Imp(Formula a, Formula b) => Par(Rel(Par(a), Implies, Par(b)));
    private static Formula All(Formula w, Formula type, Formula body) => Bound(Forall, w, type, body);
    private static Formula Ex(Formula w, Formula type, Formula body) => Bound(Exists, w, type, body);
    private static Formula Lam(Formula w, Formula type, Formula body) => Bound(LambdaLower, w, type, body);
    private static Formula Bound(Formula binder, Formula w, Formula type, Formula body) =>
        Par(Seq(binder, Sp, Open, w, Colon, type, Close, Comma, Sp, Par(body)));
    private static Formula Let(Formula w, Formula value, Formula body) =>
        Seq(Op("let"), Sp, w, Eq, value, Sp, Op("in"), Sp, Par(body));
    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0) items.Add(Seq(Sp, Land, Sp));
            items.Add(clauses[index]);
        }
        return Par(Seq([.. items]));
    }
    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.Add(Comma);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
