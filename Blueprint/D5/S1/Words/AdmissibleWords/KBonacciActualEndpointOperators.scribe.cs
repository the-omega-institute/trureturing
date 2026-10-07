using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class KBonacciActualEndpointOperatorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classify actual Boolean-word endpoint transfers, complete-window products, "
            + "and their faithful transfers with absorbing rejection over every field.",
        H("Actual endpoint operators and complete windows"),
        Blocks(
            Paragraph(Text(
                "Fix any field K and an integer k at least two. The live states are "
                    + "the integers from zero through k-1. A false bit resets a live "
                    + "state to zero. A true bit increments it when the result is below "
                    + "k and otherwise rejects. Rejection is absorbing. Words are "
                    + "finite Boolean functions read in increasing coordinate order. "
                    + "List.ofFn preserves their length and every coordinate; conversely, "
                    + "a list is exactly List.ofFn of its own coordinate function. "
                    + "In the display, arithmetic on Fin k states uses their natural "
                    + "values, and natural subtraction is truncated at zero. Finite "
                    + "families use image and card for image and cardinality. "
                    + "The get operation on an option is used only in branches "
                    + "where that option is present. The matrix unit denotes the "
                    + "identity on the indicated state space.")),
            Paragraph(Text(
                "The run from live state s agrees with the original runAdmissible "
                    + "scanner with maximum fuel k-1 and initial fuel k-1-s. A word "
                    + "is DBonacciAdmissible exactly when its run from zero accepts. "
                    + "The live transfer L_w has column s equal to the basis vector "
                    + "at the actual terminal state, or the zero column on rejection. "
                    + "The totalized transfer retains one additional rejection basis "
                    + "state, represented by none, and sends every column to its actual "
                    + "terminal basis vector. These are column-input matrices.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-actual-endpoint-operators"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciActualEndpointOperators."
                        + "actual_endpoint_operators"),
                H("Endpoint composition, exact families, and faithful totalization"),
                StatementSource.FromAuthor(Disp(MainFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a word containing a false bit, let p and t be the lengths "
                            + "of its initial and final true runs. If its run from zero "
                            + "accepts, both endpoints are below k, their sum is strictly "
                            + "less than the complete word length, and the run from any "
                            + "state s ends at t exactly when s+p is below k. Thus "
                            + "L_w=E(p,t)=e_t r_p^T, where r_p(s) is one for s+p below "
                            + "k and zero otherwise. If a word rejects from zero, it "
                            + "rejects from every live input.")),
                    Paragraph(Text(
                        "Reading u and then v gives L_(uv)=L_v L_u. For two arbitrary "
                            + "length, zero-containing words accepted from zero, the "
                            + "displayed endpoint product is their actual composition. "
                            + "The composed run from s accepts exactly when both "
                            + "t_1+p_2 and s+p_1 are below k, and then ends at t_2. "
                            + "When t_1+p_2 reaches k, every input rejects.")),
                    Paragraph(Text(
                        "At width m=k+1, every accepted word contains a false bit. "
                            + "The possible endpoints are exactly p,t below k with "
                            + "p+t at most k. The actual word consisting of p true bits, "
                            + "m-p-t false bits, and t true bits realizes each pair. "
                            + "Its length is exactly m, with every false bit retained. "
                            + "The all-true width-m word rejects and induces the zero "
                            + "live matrix. Endpoint matrices are nonzero and distinct "
                            + "over every field. There are N_k nonzero one-window "
                            + "operators and N_k+1 one-window operators in total.")),
                    Paragraph(Text(
                        "For every k at least three, the windows with endpoints "
                            + "(k-1,0) and (0,k-1) compose to (k-1,k-1), outside the "
                            + "one-window domain because its endpoint sum exceeds k. "
                            + "For k=3 these actual windows are 1100 and 0011. "
                            + "Consequently the one-window family is not closed under "
                            + "composition for any k at least three.")),
                    Paragraph(Text(
                        "For every positive integer r, every actual word of length "
                            + "r*m induces either rejection or one of the k squared "
                            + "endpoint matrices. Conversely, any pair (p,t) is realized "
                            + "by the two full windows (p,0) followed by (0,t). The "
                            + "entire family generated by positive numbers of complete "
                            + "windows is therefore exactly all endpoint matrices plus "
                            + "zero, is closed under multiplication, and has k squared "
                            + "plus one elements. This includes k=2.")),
                    Paragraph(Text(
                        "Allowing r=0 adds exactly the empty-word identity. Every "
                            + "nonempty complete-window operator has rank at most one, "
                            + "whereas the live identity has rank k and k is at least "
                            + "two. The resulting monoid is closed under multiplication "
                            + "and has k squared plus two elements.")),
                    Paragraph(Text(
                        "The faithful lift Gamma sends A to the matrix whose live "
                            + "block is A, whose live rows in the rejection-input column "
                            + "are zero, whose rejection row in live column s is "
                            + "1 minus the sum of A's column s, and whose rejection "
                            + "diagonal entry is one. Gamma is injective, preserves "
                            + "identity and multiplication, and the actual totalized "
                            + "word transfer is Gamma(L_w). In particular Gamma(0) "
                            + "is e_bottom times the all-one row and is nonzero. "
                            + "The rejection-input column always stays at rejection.")),
                    Paragraph(Text(
                        "The totalized one-window, positive-window, and empty-inclusive "
                            + "families are exactly the respective Gamma images. They "
                            + "have the same three operator counts, the generated "
                            + "families are closed, and the same two actual windows "
                            + "witness one-window nonclosure when k is at least three. "
                            + "These counts concern operators, not historical states.")),
                    Paragraph(Text(
                        "Adjoining a final false bit to any original admissible "
                            + "n-coordinate word preserves admissibility, gives exactly "
                            + "n+1 coordinates, and ends the actual run at zero. "
                            + "Zero resets the tail while remaining an actual position; "
                            + "endpoint parameters never remove internal positions."))),
                DescribeRole.Theorem))));

    private static Formula MainFormula()
    {
        var K = F.Id("K"); var k = F.Id("k"); var S = F.Id("S");
        var O = F.Id("O"); var W = F.Id("W"); var M = F.Id("M"); var Q = F.Id("Q");
        var z = F.Id("z"); var n = F.Id("n"); var w = F.Id("w");
        var s = F.Id("s"); var i = F.Id("i"); var b = F.Id("b");
        var p = F.Id("p"); var t = F.Id("t"); var u = F.Id("u"); var v = F.Id("v");
        var A = F.Id("A"); var B = F.Id("B"); var r = F.Id("r"); var q = F.Id("q");
        var a = F.Id("a"); var m = F.Id("m"); var domain = F.Id("D");
        var one = F.Id("C"); var positive = F.Id("P"); var monoid = F.Id("H");
        var top = F.Id("h"); var count = Seq(F.Id("N"), Underscore, Grp(k));
        var nat = Seq(Mathbb, Grp(F.Id("N"))); var boolean = Op("Bool");
        var none = Op("none"); var yes = Op("true"); var no = Op("false");
        var zero = D(0); var unit = D(1); var pairType = Rel(S, Times, S);
        var pOne = Index("p", 1); var tOne = Index("t", 1);
        var pTwo = Index("p", 2); var tTwo = Index("t", 2);
        var endpoints = Seq(pOne, Comma, tOne, Comma, pTwo, Comma, tTwo);
        var coordinateWord = Rel(Call("Fin", n), To, boolean);
        var indexed = Call("ofFn", w);
        var repeated = Call("replicate", m, yes);
        var firstWindow = Fn("V", top, z); var secondWindow = Fn("V", z, top);
        var joinedWindows = Append(firstWindow, secondWindow);
        var pairMap = Lam(q, pairType, Fn("E", Call("fst", q), Call("snd", q)));
        var image = Call("image", pairMap, domain);
        var liftedOne = Call("image", Gamma, one);
        var liftedPositive = Call("image", Gamma, positive);
        var liftedMonoid = Call("image", Gamma, monoid);
        var joinCondition = Rel(Add(tOne, pTwo), Lt, k);
        var product = Seq(Fn("E", pTwo, tTwo), Sp, Fn("E", pOne, tOne));
        var endpointProduct = Cases(
            Seq(Fn("E", pOne, tTwo), Amp, joinCondition),
            Seq(zero, Amp, Rel(Add(tOne, pTwo), Geq, k)));
        var endWord = Call("ofFn", Call("snoc", w, no));
        var definitions = Rows(
            Equal(S, Call("Fin", k)), Equal(O, Call("Option", S)),
            Equal(W, Call("List", boolean)), Equal(M, Call("Matrix", S, S, K)),
            Equal(Q, Call("Matrix", O, O, K)), Equal(z, Seq(zero, Colon, S)),
            Equal(Seq(Op("base"), Colon, Call("PartialDFA", boolean, S)),
                Seq(Open, Op("start"), Eq, z, Comma, Op("step"), Eq,
                    Lam(s, S, Lam(b, boolean,
                    If(Equal(b, yes), If(Rel(Add(s, unit), Lt, k),
                        Call("some", Add(s, unit)), none), Call("some", z)))), Close)),
            Equal(F.Id("R"), Call("evalFrom", Op("base"))),
            Equal(F.Id("a"), Lam(w, W, Call("length", Call("takeWhile", Op("id"), w)))),
            Equal(F.Id("b"), Lam(w, W,
                Call("length", Call("takeWhile", Op("id"), Call("reverse", w))))),
            Equal(F.Id("L"), Lam(w, W, Lam(Seq(i, Comma, s), S,
                If(Equal(Fn("R", s, w), Call("some", i)), unit, zero)))),
            Equal(F.Id("E"), Lam(Seq(p, Comma, t), S, Lam(Seq(i, Comma, s), S,
                If(And(Equal(i, t), Rel(Add(s, p), Lt, k)), unit, zero)))),
            Equal(m, Add(k, unit)),
            Equal(F.Id("V"), Lam(Seq(p, Comma, t), S,
                Append(Append(Call("replicate", p, yes),
                    Call("replicate", Subtract(Subtract(m, p), t), no)),
                    Call("replicate", t, yes)))),
            Equal(domain, Seq(OpenBrace, Open, p, Comma, t, Close, Sp, InMacro, Sp,
                pairType, Sp, Mid, Sp, Rel(Add(p, t), Leq, k), CloseBrace)),
            Equal(one, Rel(Set(zero), Cup, image)),
            Equal(positive, Rel(Set(zero), Cup, Call("image", pairMap, Call("univ", pairType)))),
            Equal(monoid, Rel(Set(unit), Cup, positive)),
            Equal(count, Seq(Frac, Grp(k, Caret, D(2), Plus, D(3), k, Minus, D(2)), Grp(D(2)))),
            Equal(F.Id("T"), Lam(w, W, Lam(Seq(i, Comma, s), O,
                If(Equal(Call("bind", s, Lam(a, S, Fn("R", a, w))), i), unit, zero)))),
            Equal(Gamma, Lam(A, M, Lam(Seq(i, Comma, s), O, Cases(
                Seq(App(A, Call("get", i), Call("get", s)), Amp,
                    And(NotEqual(i, none), NotEqual(s, none))),
                Seq(zero, Amp, And(NotEqual(i, none), Equal(s, none))),
                Seq(Subtract(unit, Seq(Sum, Underscore, Grp(a, Sp, InMacro, Sp, S),
                    Sp, App(A, a, Call("get", s)))), Amp,
                    And(Equal(i, none), NotEqual(s, none))),
                Seq(unit, Amp, And(Equal(i, none), Equal(s, none))))))));
        var clauses = ConjoinedRows(
            All(n, nat, All(w, coordinateWord, All(s, S,
                Equal(Call("isSome", Fn("R", s, indexed)),
                    Call("runAdmissible", Subtract(k, unit),
                        Subtract(Subtract(k, unit), s), n, w))))),
            All(n, nat, All(w, coordinateWord,
                Rel(Call("DBonacciAdmissible", k, n, w), Iff,
                    NotEqual(Fn("R", z, indexed), none)))),
            All(n, nat, All(w, coordinateWord, And(Equal(Call("length", indexed), n),
                All(i, Call("Fin", n), Equal(Call("get", indexed, i), App(w, i)))))),
            All(w, W, And(Equal(Call("length", Call("ofFn", Call("get", w))), Call("length", w)),
                Equal(Call("ofFn", Call("get", w)), w))),
            All(w, W, Imp(And(Rel(no, InMacro, w), NotEqual(Fn("R", z, w), none)),
                Ex(Seq(p, Comma, t), S, And(Equal(Fn("a", w), p), Equal(Fn("b", w), t),
                    Rel(Add(p, t), Lt, Call("length", w)),
                    All(s, S, Equal(Fn("R", s, w),
                        If(Rel(Add(s, p), Lt, k), Call("some", t), none))),
                    Equal(Fn("L", w), Fn("E", p, t)))))),
            All(w, W, Imp(Equal(Fn("R", z, w), none), All(s, S, Equal(Fn("R", s, w), none)))),
            All(w, W, Imp(And(Rel(k, Leq, Call("length", w)), NotEqual(Fn("R", z, w), none)),
                Rel(no, InMacro, w))),
            All(Seq(u, Comma, v), W, Equal(Fn("L", Append(u, v)), Product(Fn("L", v), Fn("L", u)))),
            All(endpoints, S, Equal(product, endpointProduct)),
            All(Seq(u, Comma, v), W, All(endpoints, S,
                Imp(And(Rel(no, InMacro, u), Rel(no, InMacro, v),
                    NotEqual(Fn("R", z, u), none), NotEqual(Fn("R", z, v), none),
                    Equal(Fn("a", u), pOne), Equal(Fn("b", u), tOne),
                    Equal(Fn("a", v), pTwo), Equal(Fn("b", v), tTwo)),
                    And(Equal(Fn("L", Append(u, v)), endpointProduct),
                        All(s, S, Equal(Fn("R", s, Append(u, v)),
                            If(And(joinCondition, Rel(Add(s, pOne), Lt, k)), Call("some", tTwo), none))))))),
            All(Seq(p, Comma, t), S, Imp(Rel(Add(p, t), Leq, k),
                And(Equal(Call("length", Fn("V", p, t)), m),
                    Equal(Fn("a", Fn("V", p, t)), p), Equal(Fn("b", Fn("V", p, t)), t),
                    Equal(Fn("R", z, Fn("V", p, t)), Call("some", t)),
                    Equal(Fn("L", Fn("V", p, t)), Fn("E", p, t))))),
            All(Seq(p, Comma, t), S, Rel(Ex(w, W,
                And(Equal(Call("length", w), m), NotEqual(Fn("R", z, w), none),
                    Equal(Fn("a", w), p), Equal(Fn("b", w), t))), Iff, Rel(Add(p, t), Leq, k))),
            All(Seq(p, Comma, t), S, And(
                Equal(Call("length", Append(Fn("V", p, z), Fn("V", z, t))), Multiply(D(2), m)),
                Equal(Fn("L", Append(Fn("V", p, z), Fn("V", z, t))), Fn("E", p, t)))),
            Equal(Fn("R", z, repeated), none), Equal(Fn("L", repeated), zero),
            All(Seq(p, Comma, t), S, And(NotEqual(Fn("E", p, t), zero),
                Rel(Call("rank", Fn("E", p, t)), Leq, unit))), Call("Injective", pairMap),
            Family(M, one, Fn("L", w), w, W, r, nat, m, 0),
            Family(M, positive, Fn("L", w), w, W, r, nat, m, 1),
            Family(M, monoid, Fn("L", w), w, W, r, nat, m, 2),
            Closed(positive, A, B, M), Closed(monoid, A, B, M),
            All(A, M, Imp(Rel(A, InMacro, positive),
                And(Rel(Call("rank", A), Leq, unit), NotEqual(A, unit)))),
            Imp(Rel(D(3), Leq, k), Let(top, S, Subtract(k, unit),
                And(Rel(Fn("L", firstWindow), InMacro, one), Rel(Fn("L", secondWindow), InMacro, one),
                    Seq(Neg, Sp, Par(Rel(Fn("L", joinedWindows), InMacro, one)))))),
            Imp(Equal(k, D(3)), Let(top, S, Subtract(k, unit),
                And(Equal(firstWindow, Seq(OpenBracket, yes, Comma, yes, Comma, no, Comma, no, CloseBracket)),
                    Equal(secondWindow, Seq(OpenBracket, no, Comma, no, Comma, yes, Comma, yes, CloseBracket))))),
            Equal(Call("card", domain), count), Equal(Call("card", image), count),
            Equal(Call("card", one), Add(count, unit)),
            Equal(Call("card", positive), Add(Seq(k, Caret, D(2)), unit)),
            Equal(Call("card", monoid), Add(Seq(k, Caret, D(2)), D(2))),
            Call("Injective", Gamma), Equal(App(Gamma, unit), unit),
            All(Seq(A, Comma, B), M, Equal(App(Gamma, Product(B, A)), Product(App(Gamma, B), App(Gamma, A)))),
            All(w, W, Equal(Fn("T", w), App(Gamma, Fn("L", w)))),
            All(w, W, And(Equal(App(Fn("T", w), none, none), unit),
                All(s, S, Equal(App(Fn("T", w), Call("some", s), none), zero)))),
            All(Seq(u, Comma, v), W, Equal(Fn("T", Append(u, v)), Product(Fn("T", v), Fn("T", u)))),
            All(Seq(i, Comma, s), O,
                Equal(App(App(Gamma, zero), i, s), If(Equal(i, none), unit, zero))),
            NotEqual(App(Gamma, zero), zero),
            Family(Q, liftedOne, Fn("T", w), w, W, r, nat, m, 0),
            Family(Q, liftedPositive, Fn("T", w), w, W, r, nat, m, 1),
            Family(Q, liftedMonoid, Fn("T", w), w, W, r, nat, m, 2),
            Equal(Call("card", liftedOne), Add(count, unit)),
            Equal(Call("card", liftedPositive), Add(Seq(k, Caret, D(2)), unit)),
            Equal(Call("card", liftedMonoid), Add(Seq(k, Caret, D(2)), D(2))),
            Closed(liftedPositive, A, B, Q), Closed(liftedMonoid, A, B, Q),
            All(n, nat, All(w, coordinateWord, Imp(Call("DBonacciAdmissible", k, n, w),
                And(Call("DBonacciAdmissible", k, Add(n, unit), Call("snoc", w, no)),
                    Equal(Call("length", endWord), Add(n, unit)),
                    Equal(Fn("R", z, endWord), Call("some", z)))))),
            Imp(Rel(D(3), Leq, k), Let(top, S, Subtract(k, unit),
                And(Rel(Fn("T", firstWindow), InMacro, liftedOne),
                    Rel(Fn("T", secondWindow), InMacro, liftedOne),
                    Seq(Neg, Sp, Par(Rel(Fn("T", joinedWindows), InMacro, liftedOne)))))));
        return Seq(Forall, Sp, Open, K, Colon, Op("Type"), Close,
            OpenBracket, Call("Field", K), CloseBracket, Open, k, Colon, nat, Close, Comma, Sp,
            Imp(Rel(D(2), Leq, k), Seq(Op("let"), Sp, definitions, Sp, Op("in"), Sp, clauses)));
    }

    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Fn(string name, params Formula[] arguments) => App(F.Id(name), arguments);
    private static Formula Index(string name, byte digit) => Seq(F.Id(name), Underscore, D(digit));
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula Rel(Formula left, Formula relation, Formula right) => Seq(left, Sp, relation, Sp, right);
    private static Formula Product(Formula left, Formula right) => Rel(left, Cdot, right);
    private static Formula Append(Formula left, Formula right) => Seq(left, Plus, Plus, right);
    private static Formula Set(Formula item) => Seq(OpenBrace, item, CloseBrace);
    private static Formula All(Formula variables, Formula type, Formula body) => Bound(Forall, variables, type, body);
    private static Formula Ex(Formula variables, Formula type, Formula body) => Bound(Exists, variables, type, body);
    private static Formula Lam(Formula variables, Formula type, Formula body) => Bound(LambdaLower, variables, type, body);
    private static Formula Bound(Formula binder, Formula variables, Formula type, Formula body) =>
        Par(Seq(binder, Sp, Open, variables, Colon, type, Close, Comma, Sp, Par(body)));
    private static Formula Imp(Formula premise, Formula body) => Par(Rel(Par(premise), Implies, Par(body)));
    private static Formula Let(Formula variable, Formula type, Formula value, Formula body) =>
        Seq(Op("let"), Sp, Open, variable, Colon, type, Close, Eq, value, Sp, Op("in"), Sp, Par(body));
    private static Formula If(Formula condition, Formula yes, Formula no) => Cases(
        Seq(yes, Amp, condition), Seq(no, Amp, Op("otherwise")));
    private static Formula Cases(params Formula[] rows) => Seq(Begin, Grp(F.Id("cases")), Join(rows, RowBreak), End, Grp(F.Id("cases")));
    private static Formula Rows(params Formula[] rows) => new Formula.Aligned([.. rows]);
    private static Formula And(params Formula[] clauses) => Par(Join(clauses, Seq(Sp, Land, Sp)));
    private static Formula ConjoinedRows(params Formula[] clauses) => Rows(Join(clauses, Seq(RowBreak, Sp, Land, Sp)));
    private static Formula Join(Formula[] items, Formula separator)
    {
        var result = new System.Collections.Generic.List<Formula>();
        for (var index = 0; index < items.Length; index++)
        {
            if (index > 0) result.Add(separator);
            result.Add(items[index]);
        }
        return Seq([.. result]);
    }
    private static Formula Closed(Formula family, Formula A, Formula B, Formula type) =>
        All(A, type, Imp(Rel(A, InMacro, family),
            All(B, type, Imp(Rel(B, InMacro, family), Rel(Product(B, A), InMacro, family)))));
    private static Formula Family(Formula type, Formula family, Formula transfer, Formula word,
        Formula words, Formula r, Formula nat, Formula width, int kind)
    {
        var A = F.Id("A");
        var length = Equal(Call("length", word), kind == 0 ? width : Multiply(r, width));
        var realization = Ex(word, words, And(length, Equal(transfer, A)));
        if (kind != 0) realization = Ex(r, nat,
            kind == 1 ? And(Rel(D(0), Lt, r), realization) : realization);
        return All(A, type, Rel(realization, Iff, Rel(A, InMacro, family)));
    }
}
