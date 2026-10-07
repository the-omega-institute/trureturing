using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class NarrowWindowCostDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete literal windows acquire monochromatic initial phase labels at exact cost.",
        H("Exact cost of narrow k-bonacci windows"),
        Blocks(
            Paragraph(Text(
                "Fix k at least two and a positive complete word width m. Words are read "
                    + "from left to right, with the first position having the lowest weight. "
                    + "The original weights G_i are dbonacci k (i+2): the first k weights "
                    + "are powers of two, and each later weight is the sum of the preceding "
                    + "k weights. Values and their sums below belong to ZMod 2. Every zero "
                    + "bit advances the position. The scanner records the consecutive final "
                    + "ones and rejects on the kth consecutive one. Rejection, written none, "
                    + "is distinct from both scalar values and is absorbing.")),
            Paragraph(Math(Disp(ReaderFormula()))),
            Paragraph(Text(
                "A hidden source is an actual finite literal history w of length divisible "
                    + "by m. On acceptance its joint coordinates are its scalar value, "
                    + "its length modulo T=k+1, and its actual final run of ones. These "
                    + "coordinates arise from the same word. The selector receives only "
                    + "the free initial endpoint output and the chronological archive H "
                    + "of complete issued words and their endpoint outputs. Its two choices "
                    + "are to stop with a label or to append one complete m-position word. "
                    + "No initial length, phase, or tail is available to the selector.")),
            Paragraph(Math(Disp(ExecutionFormula()))),
            Paragraph(Text(
                "Execution E uses a natural bound d on the number of issued words. At "
                    + "bound zero a stop succeeds and a further action fails. Every issued "
                    + "word contributes one unit, even when it is all zero, has a constant "
                    + "endpoint, or contains only padding. The hidden history grows by "
                    + "literal concatenation. The initial phase label is retained as the "
                    + "correctness target throughout these destructive updates.")),
            Paragraph(Math(Disp(FeasibleFormula()))),
            Paragraph(Text(
                "Here a=true restricts actions to words internally avoiding k consecutive "
                    + "ones, while a=false allows every complete Boolean word. Both execute "
                    + "the actual scanner across seams. F(a,lambda,r,v,d) requires one "
                    + "selector to be correct on every accepted initial history with free "
                    + "value v and compatible initial phase, with total cost at most d. "
                    + "It also returns the prescribed initial rejection label r at zero "
                    + "cost on every initially rejected history. The index j identifies "
                    + "the initial phase -jg modulo T; the target lambda(j) is independent "
                    + "of the initial tail.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-narrow-window-cost"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/NarrowWindowCost.narrow_window_cost"),
                H("Least uniform budget for monochromatic windows"),
                StatementSource.FromAuthor(Disp(LawFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The baseline is A=lambda(0). The index J is the largest index "
                            + "whose label differs from A, with J=0 for a constant target. "
                            + "In each interval t*u<j<=(t+1)*u, restricted to j<=J, all "
                            + "nonbaseline labels must agree. Labels are otherwise arbitrary: "
                            + "different windows can carry different labels, and a label can "
                            + "recur in several windows. Empty windows are included.")),
                    Paragraph(Math(Disp(PulseFormula()))),
                    Paragraph(Text(
                        "For the upper bound, issue B_t at the tth step until an endpoint "
                            + "differs from the initial value, or until D words have been "
                            + "issued. The complete word B_t has a one exactly at the "
                            + "displayed selected positions; every other position is zero. "
                            + "Its first bit is zero, distinct ones are at least g positions "
                            + "apart, and its final tail is at most one. It therefore accepts "
                            + "from every initial tail, and the next first zero protects "
                            + "each actual seam.")),
                    Paragraph(Text(
                        "The original coefficient sequence modulo two has support at "
                            + "residues zero and k modulo T. A selected absolute position "
                            + "jg-1 contributes one exactly for initial phase -jg. Thus the "
                            + "scalar increment of B_t is one precisely for the nonbaseline "
                            + "indices in its own window. Before the first such increment "
                            + "all endpoints equal the initial value. A changed endpoint "
                            + "determines the common window label; after D unchanged "
                            + "endpoints the label is A. Every empty window and the final "
                            + "partial window still use one complete paid word.")),
                    Paragraph(Text(
                        "The lower bound permits all adaptive selectors and all actions. "
                            + "Joint initial histories with any prescribed value, compatible "
                            + "phase, and tail are obtained by a simultaneous congruence "
                            + "construction: choose a sufficiently large length N divisible "
                            + "by m in the prescribed residue class modulo T, use a first "
                            + "correction bit, then zeros, then the prescribed final ones. "
                            + "The correction bit compensates the scalar contribution of "
                            + "the final ones.")),
                    Paragraph(Text(
                        "When J>0, two different initial labels with tail k-1 force the "
                            + "first action to start with zero: a leading one would reject "
                            + "both and make every subsequent endpoint identical. Now take "
                            + "tail-zero initial histories of phases zero and -Jg with the "
                            + "same free value. For d<D, their first d*m continuation "
                            + "positions miss Jg-1 and Jg, and miss T-1. The sole phase-zero "
                            + "position at zero is suppressed by that first zero.")),
                    Paragraph(Text(
                        "Every common continuation of at most d complete words therefore "
                            + "has equal scalar increments for the two sources. Their "
                            + "scanners have the same current tail and hence the same "
                            + "acceptance or rejection. Induction on the chronological "
                            + "archive forces the same later actions, including arbitrary "
                            + "leading ones, and the same terminal answer. Their different "
                            + "initial labels preclude success within d words.")),
                    Paragraph(Text(
                        "The conclusion includes J=0, single-index windows u=1, "
                            + "empty windows, repeated labels, both free values, and both "
                            + "action alphabets. It places no condition D*m<T on the final "
                            + "padding: for k=9 and m=6, g=2, p=5, u=3, and J=4 give "
                            + "D=2 and D*m=12>T=10. Positions after the last selected "
                            + "pulse remain actual zero positions."))),
                DescribeRole.Theorem))));

    private static Formula ReaderFormula()
    {
        var k = F.Id("k"); var n = F.Id("n"); var i = F.Id("i");
        var b = F.Id("b"); var w = F.Id("w"); var s = F.Id("s");
        var r = F.Id("r"); var T = F.Id("T");
        var scalar = Call("ZMod", D(2)); var none = Op("none");
        return Rows(
            Equal(T, Add(k, D(1))),
            Equal(Fn("G", i), Call("dbonacci", k, Add(i, D(2)))),
            Equal(Fn("c", i), Seq(Fn("G", i), Colon, scalar)),
            Equal(Fn("c", i), If(Or(Equal(Call("mod", i, T), D(0)),
                Equal(Call("mod", i, T), k)), D(1), D(0))),
            Equal(Fn("V", n, Nil()), D(0)),
            Equal(Fn("V", n, Call("cons", b, w)),
                Add(If(Equal(b, Op("true")), Fn("c", n), D(0)), Fn("V", Add(n, D(1)), w))),
            Equal(Fn("delta", s, b), If(Equal(b, Op("false")), Call("some", D(0)),
                If(Rel(Add(s, D(1)), Lt, k), Call("some", Add(s, D(1))), none))),
            Equal(Fn("R", s, Nil()), Call("some", s)),
            Equal(Fn("R", s, Call("cons", b, w)),
                Call("bind", Fn("delta", s, b), Lam(r, Call("Fin", k), Fn("R", r, w)))),
            Equal(Fn("o", w), Call("map", Fn("R", D(0), w),
                Lam(s, Call("Fin", k), Fn("V", D(0), w)))));
    }

    private static Formula ExecutionFormula()
    {
        var m = F.Id("m"); var Y = F.Id("Y"); var w = F.Id("w");
        var y = F.Id("y"); var Hh = F.Id("H"); var d = F.Id("d");
        var q = F.Id("q"); var B = F.Id("B"); var pi = F.Id("pi");
        var h = F.Id("h"); var word = WordType(m); var obs = ObservationType();
        var record = Rel(Par(word), Times, obs); var wp = Append(w, Call("ofFn", B));
        var hp = Append(Hh, List(Pair(B, Fn("o", wp))));
        var selected = App(pi, y, Hh);
        var stop = Equal(selected, Call("inl", q));
        var action = Equal(selected, Call("inr", B));
        var next = Fn("E", pi, d, wp, y, hp);
        return Rows(
            Equal(F.Id("Archive"), Call("List", record)),
            Equal(F.Id("Selector"), Rel(obs, To, Rel(Call("List", record), To, Call("Sum", Y, word)))),
            Equal(Fn("E", pi, D(0), w, y, Hh), Cases(
                Seq(Call("some", Pair(q, D(0))), Amp, stop),
                Seq(Op("none"), Amp, action))),
            Equal(Fn("E", pi, Add(d, D(1)), w, y, Hh), Cases(
                Seq(Call("some", Pair(q, D(0))), Amp, stop),
                Seq(Call("map", next, Lam(h, Rel(Y, Times, NatType()),
                    Pair(Call("fst", h), Add(Call("snd", h), D(1))))), Amp, action))));
    }

    private static Formula FeasibleFormula()
    {
        var k = F.Id("k"); var m = F.Id("m"); var p = F.Id("p"); var g = F.Id("g");
        var a = F.Id("a"); var labels = F.Id("lambda"); var reject = F.Id("r");
        var v = F.Id("v"); var d = F.Id("d"); var pi = F.Id("pi");
        var w = F.Id("w"); var j = F.Id("j"); var q = F.Id("q");
        var y = F.Id("y"); var Hh = F.Id("H"); var B = F.Id("B");
        var word = WordType(m); var obs = ObservationType(); var length = Call("length", w);
        var legality = All(y, obs, All(Hh, Call("List", Rel(Par(word), Times, obs)), All(B, word,
            Imp(And(Equal(App(pi, y, Hh), Call("inr", B)), Equal(a, Op("true"))),
                Call("DBonacciAdmissible", k, m, B)))));
        var rejected = All(w, Call("List", Op("Bool")),
            Imp(And(Divides(m, length), Equal(Fn("o", w), Op("none"))),
                Equal(Fn("E", pi, d, w, Op("none"), Nil()), Call("some", Pair(reject, D(0))))));
        var accepted = All(w, Call("List", Op("Bool")), All(j, Call("Fin", p),
            Imp(And(Divides(m, length), Equal(Fn("o", w), Call("some", v)),
                Divides(Add(k, D(1)), Add(length, Multiply(j, g)))),
                Ex(q, NatType(), And(Rel(q, Leq, d),
                    Equal(Fn("E", pi, d, w, Call("some", v), Nil()),
                        Call("some", Pair(App(labels, j), q))))))));
        return Equal(Fn("F", a, labels, reject, v, d),
            Ex(pi, F.Id("Selector"), And(legality, rejected, accepted)));
    }

    private static Formula LawFormula()
    {
        var k = F.Id("k"); var m = F.Id("m"); var Y = F.Id("Y");
        var g = F.Id("g"); var p = F.Id("p"); var u = F.Id("u"); var J = F.Id("J");
        var labels = F.Id("lambda"); var v = F.Id("v"); var reject = F.Id("r");
        var a = F.Id("a"); var d = F.Id("d"); var t = F.Id("t");
        var j = F.Id("j"); var jp = F.Id("jprime"); var T = Add(k, D(1));
        var A = App(labels, D(0)); var indices = Call("Fin", p);
        var mono = All(t, NatType(), All(j, indices, All(jp, indices,
            Imp(And(Window(t, u, J, j, labels, A), Window(t, u, J, jp, labels, A)),
                Equal(App(labels, j), App(labels, jp))))));
        var budgets = Seq(OpenBrace, d, Sp, InMacro, Sp, NatType(), Sp, Mid, Sp,
            Fn("F", a, labels, reject, v, d), CloseBrace);
        var exact = All(v, Call("ZMod", D(2)), All(reject, Y, All(a, Op("Bool"),
            Call("IsLeast", budgets, Call("ceilDiv", J, u)))));
        var result = And(Rel(D(0), Lt, p), Imp(mono, exact));
        var last = Call("max", Rel(Set(D(0)), Cup,
            Seq(OpenBrace, j, Sp, InMacro, Sp, indices, Sp, Mid, Sp,
                NotEqual(App(labels, j), A), CloseBrace)));
        return All(Y, Op("Type"), All(k, NatType(), All(m, NatType(),
            Imp(And(Rel(D(2), Leq, k), Rel(D(1), Leq, m),
                Rel(D(2), Leq, Call("gcd", m, T)), Rel(m, Lt, T)),
                Let(g, Call("gcd", m, T), Let(p, Call("div", T, g),
                    Let(u, Call("div", m, g), All(labels, Rel(indices, To, Y),
                        Let(J, last, result)))))))));
    }

    private static Formula PulseFormula()
    {
        var t = F.Id("t"); var j = F.Id("j"); var i = F.Id("i");
        var g = F.Id("g"); var m = F.Id("m"); var u = F.Id("u");
        var p = F.Id("p"); var J = F.Id("J"); var labels = F.Id("lambda");
        var A = F.Id("A"); var S = Fn("S", t, j);
        var selected = Ex(j, Call("Fin", p), And(S,
            Equal(Add(Add(Multiply(t, m), i), D(1)), Multiply(j, g))));
        return Rows(
            Equal(A, App(labels, D(0))),
            Equal(S, Window(t, u, J, j, labels, A)),
            Equal(Fn("B", t, i), If(selected, Op("true"), Op("false"))),
            Equal(F.Id("D"), Call("ceilDiv", J, u)),
            All(t, NatType(), All(F.Id("N"), NatType(), All(j, Call("Fin", p),
                Imp(Divides(Add(F.Id("k"), D(1)), Add(F.Id("N"), Multiply(j, g))),
                    Equal(Fn("V", Add(F.Id("N"), Multiply(t, m)), Call("ofFn", Fn("B", t))),
                        If(S, D(1), D(0))))))));
    }

    private static Formula Window(Formula t, Formula u, Formula J, Formula j, Formula labels, Formula A) =>
        And(Rel(Multiply(t, u), Lt, j), Rel(j, Leq, Multiply(Add(t, D(1)), u)),
            Rel(j, Leq, J), NotEqual(App(labels, j), A));
    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ObservationType() => Call("Option", Call("ZMod", D(2)));
    private static Formula WordType(Formula m) => Rel(Call("Fin", m), To, Op("Bool"));
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Fn(string name, params Formula[] args) => App(F.Id(name), args);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, b, Close);
    private static Formula Nil() => Seq(OpenBracket, CloseBracket);
    private static Formula List(Formula a) => Seq(OpenBracket, a, CloseBracket);
    private static Formula Set(Formula a) => Seq(OpenBrace, a, CloseBrace);
    private static Formula Append(Formula a, Formula b) => Seq(a, Plus, Plus, b);
    private static Formula Divides(Formula a, Formula b) => Rel(a, Mid, b);
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
    private static Formula If(Formula condition, Formula yes, Formula no) => Cases(
        Seq(yes, Amp, condition), Seq(no, Amp, Op("otherwise")));
    private static Formula Cases(params Formula[] rows) => Seq(Begin, Grp(F.Id("cases")),
        Join(rows, RowBreak), End, Grp(F.Id("cases")));
    private static Formula Rows(params Formula[] rows) => new Formula.Aligned([.. rows]);
    private static Formula And(params Formula[] clauses) => Par(Join(clauses, Seq(Sp, Land, Sp)));
    private static Formula Or(Formula a, Formula b) => Par(Rel(a, Lor, b));
    private static Formula Join(Formula[] items, Formula separator)
    {
        var result = new System.Collections.Generic.List<Formula>();
        for (var i = 0; i < items.Length; i++)
        {
            if (i > 0) result.Add(separator);
            result.Add(items[i]);
        }
        return Seq([.. result]);
    }
}
