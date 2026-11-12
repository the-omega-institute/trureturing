using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233177LadderDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Ladder.";
    private const string LeanPrefix =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder.";

    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233177");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's recurrence for the literal normalized four-row six-colour ladder.",
        H("Four-row complementary-pair ladders"),
        Blocks(
            Paragraph(Text("Cells are Fin 4 times Fin n, with colour set Fin 6. "
                + "Only bonds between consecutive columns are constrained: row indices "
                + "may differ by at most one. A bond excludes equal colours and colours "
                + "whose values sum to five. Vertical neighbours inside a column are free. "
                + "The first cell is zero and the predecessor conditions use the strict "
                + "row-major rank row.val*n+column.val.")),
            Node("normal", "Row-major predecessor conditions", NormalFormula(), false),
            Node("instDecidableNormal", "Deciding the row-major conditions", DecidableNormalFormula(), false),
            Node("Legal", "Literal array conditions", LegalFormula(), false),
            Node("a", "The literal filtered count", CountFormula(), false, true),
            Node("cellOrder", "The lifted row-major order", CellOrderFormula(), false),
            Node("RowNormal", "Normalization in the lifted order", OrderedPredicateFormula(false), false),
            Node("Canon", "Canonical labels in the lifted order", OrderedPredicateFormula(true), false),
            Node("row_major_lt", "The strict row-major comparison", RowMajorLtFormula(), true),
            Node("normal_iff", "The two normalization expressions agree", NormalIffFormula(), true),
            Node("used", "Number of labels used", UsedFormula(), false),
            Node("used_eq_card", "Used labels as a finite image", UsedEqCardFormula(), true),
            Node("omitted_label", "Two used labels omit a third", OmittedLabelFormula(), true),
            Node("alternating", "Two alternating constant columns", AlternatingFormula(), false),
            Node("alternating_proper", "Alternation satisfies both directions of the diagonal bonds",
                AlternatingProperFormula(), true),
            Node("alternating_used", "Alternation uses exactly two distinct labels",
                AlternatingUsedFormula(), true),
            Node("alternating_canon", "Zero-one alternation is canonical",
                AlternatingCanonFormula(), true),
            Node("two_label_classification", "Classification when one label is omitted",
                TwoLabelClassificationFormula(), true),
            Node("canon_two_eq", "The canonical two-label pattern is zero-one alternation",
                CanonTwoEqFormula(), true),
            Node("counting_bridge", "The canonical-form counting bridge", BridgeFormula(), true),
            Paragraph(Text("The beta-label identifies the pairs {0,5}, {1,4}, {2,3}; "
                + "the side is an independent Boolean choice. Normalization introduces "
                + "pair labels in first-appearance order and fixes the first side of each "
                + "used pair to the smaller colour. A canonical pattern using k labels "
                + "therefore has 2^(4*n-k) lifts. At width at least two a proper pattern "
                + "uses two or three labels, and every relabelling orbit has six members. "
                + "If one label is omitted, adjacent entries of a column must agree: "
                + "a common neighbour in another column excludes both differing labels. "
                + "Each column is then constant and the two labels alternate. The six "
                + "such patterns have exactly one canonical member. If C is the number "
                + "of canonical proper patterns, L=6*C and a=2^(4*n-3)*(C+1). "
                + "This gives the displayed bridge for every width at least two.")),
            Node("finite_certificate", "The first permitted recurrence instance",
                RecurrenceFormula(null), true),
            Resolution("result", "Hardin's shifted integer recurrence",
                RecurrenceFormula(V("n"))),
            Paragraph(Text("The pair-pattern transfer has fourteen column classes. "
                + "Its sextic tail polynomial, multiplied by x-1, gives the recurrence "
                + "for L+6. Multiplication by 16^n scales the coefficient at lag j by "
                + "16^j. The finite base instance covers index nine, while the shifted "
                + "tail relation covers all larger indices. Writing the index as n+9 "
                + "makes the condition index>8 explicit. Counts are cast to Int "
                + "before subtraction. Width one is exceptional for the counting bridge.")))));

    private static DocumentBlock Resolution(string name, string title, Formula formula) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(title + "."))), DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233177"),
                ResolutionKind.Proved));

    private static DocumentBlock Node(string name, string title, Formula formula, bool theorem,
        bool literature = false) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(title + "."))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula BridgeFormula()
    {
        var n = V("n");
        return All("n", Q("Nat"), Imp(Le(D(2), n), Eq(
            Mul(D(4,8), Typed(Own("a", n), Q("Int"))),
            Mul(Power(Typed(D(1,6), Q("Int")), n),
                Add(Typed(Call("D5.S3.Combinatorics.TraceAvoidingArrays."
                    + "HardinA233177PairTransfer.L", n), Q("Int")), D(6))))));
    }

    private static Formula Cells(Formula n) => Product(Fin(D(4)), Fin(n));
    private static Formula OrderLT(Formula n) =>
        Seq(Parenthesized(Own("cellOrder", n)), Dot, V("toLT"));

    private static Formula CellOrderFormula()
    {
        var n = V("n");
        var lift = Seq(Q("LinearOrder.lift"), Apos);
        var value = App(lift, Q("finProdFinEquiv"),
            Call("Equiv.injective", Q("finProdFinEquiv")));
        return All("n", Q("Nat"), Eq(Typed(Own("cellOrder", n),
            Call("LinearOrder", Parenthesized(Cells(n)))), Parenthesized(value)));
    }

    private static Formula OrderedPredicateFormula(bool canonical)
    {
        var n = V("n"); var p = V(canonical ? "P" : "A");
        var name = canonical ? "Canon" : "RowNormal";
        var target = "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical."
            + (canonical ? "Canonical" : "Normal");
        var value = canonical ? Call(target, Parenthesized(Cells(n)), OrderLT(n), D(3), p)
            : Call(target, Parenthesized(Cells(n)), OrderLT(n), p);
        return All("n", Q("Nat"), All(canonical ? "P" : "A",
            Arrow(Cells(n), Fin(D(canonical ? (byte)3 : (byte)6))),
            Eq(Own(name, p), Parenthesized(value))));
    }

    private static Formula RowMajorLtFormula()
    {
        var n = V("n"); var p = V("p"); var q = V("q");
        Formula Rank(Formula x) => Add(Mul(Val(Call("Prod.fst", x)), n),
            Val(Call("Prod.snd", x)));
        return All("n", Q("Nat"), All("p", Cells(n), All("q", Cells(n),
            IffTo(Call("LT.lt", Parenthesized(Cells(n)), OrderLT(n), p, q),
                Lt(Rank(p), Rank(q))))));
    }

    private static Formula NormalIffFormula()
    {
        var n = V("n"); var a = V("A");
        return All("n", Q("Nat"), All("A", Arrow(Cells(n), Fin(D(6))),
            IffTo(Own("normal", a), Own("RowNormal", a))));
    }

    private static Formula UsedEqCardFormula()
    {
        var n = V("n"); var p = V("P");
        var image = Call("Finset.image", p, Typed(Q("Finset.univ"),
            Call("Finset", Parenthesized(Cells(n)))));
        return All("n", Q("Nat"), All("P", Arrow(Cells(n), Fin(D(3))),
            Eq(Own("used", p), Call("Finset.card", Parenthesized(image)))));
    }

    private static Formula OmittedLabelFormula()
    {
        var n = V("n"); var p = V("P"); var d = V("d");
        return All("n", Q("Nat"), All("P", Arrow(Cells(n), Fin(D(3))),
            All("h", Eq(Own("used", p), D(2)), Ex("d", Fin(D(3)),
                All("i", Cells(n), Ne(App(p, V("i")), d))))));
    }

    private static Formula AlternatingProperFormula()
    {
        var n = V("n"); var a = V("a"); var b = V("b");
        var proper = Call("D5.S3.Combinatorics.TraceAvoidingArrays."
            + "HardinA233177PairTransfer.Proper", Parenthesized(Own("alternating", n, a, b)));
        return All("n", Q("Nat"), All("a", Fin(D(3)), All("b", Fin(D(3)),
            All("hab", Ne(a, b), proper))));
    }

    private static Formula AlternatingUsedFormula()
    {
        var n = V("n"); var a = V("a"); var b = V("b");
        return All("n", Q("Nat"), All("hn", Le(D(2), n),
            All("a", Fin(D(3)), All("b", Fin(D(3)), All("hab", Ne(a, b),
                Eq(Own("used", Parenthesized(Own("alternating", n, a, b))), D(2)))))));
    }

    private static Formula AlternatingCanonFormula()
    {
        var n = V("n");
        return All("n", Q("Nat"), All("hn", Lt(D(0), n),
            Own("Canon", Parenthesized(Own("alternating", n,
                Typed(D(0), Fin(D(3))), Typed(D(1), Fin(D(3))))))));
    }

    private static Formula AlternatingFormula()
    {
        var n = V("n"); var a = V("a"); var b = V("b"); var p = V("p");
        var cells = Product(Fin(D(4)), Fin(n));
        var even = Eq(Call("Nat.mod", Val(Call("Prod.snd", p)), D(2)), D(0));
        var value = Parenthesized(Seq(V("if"), Sp, Parenthesized(even), Sp,
            V("then"), Sp, a, Sp, V("else"), Sp, b));
        return All("n", Q("Nat"), All("a", Fin(D(3)), All("b", Fin(D(3)),
            Eq(Own("alternating", n, a, b), Fn("p", cells, value)))));
    }

    private static Formula TwoLabelClassificationFormula()
    {
        var n = V("n"); var p = V("P"); var d = V("d");
        var a = V("a"); var b = V("b");
        var cells = Product(Fin(D(4)), Fin(n));
        var omitted = All("i", cells, Ne(App(p, V("i")), d));
        var proper = Call("D5.S3.Combinatorics.TraceAvoidingArrays."
            + "HardinA233177PairTransfer.Proper", p);
        var classification = Ex("a", Fin(D(3)), Ex("b", Fin(D(3)),
            And(Ne(a, b), Eq(p, Own("alternating", n, a, b)))));
        return All("n", Q("Nat"), All("hn", Le(D(2), n),
            All("P", Arrow(cells, Fin(D(3))), All("hp", proper,
                All("d", Fin(D(3)), All("hd", omitted, classification))))));
    }

    private static Formula CanonTwoEqFormula()
    {
        var n = V("n"); var p = V("P");
        var proper = Call("D5.S3.Combinatorics.TraceAvoidingArrays."
            + "HardinA233177PairTransfer.Proper", p);
        return All("n", Q("Nat"), All("hn", Le(D(2), n),
            All("P", Arrow(Cells(n), Fin(D(3))), All("hp", proper,
                All("hc", Own("Canon", p), All("hu", Eq(Own("used", p), D(2)),
                    Eq(p, Own("alternating", n, Typed(D(0), Fin(D(3))),
                        Typed(D(1), Fin(D(3)))))))))));
    }

    private static Formula RecurrenceFormula(Formula? n)
    {
        Formula A(int i) => Typed(Own("a", n is null ? Num(i) : Add(n, Num(i))), Q("Int"));
        var rhs = Sub(Add(Add(Sub(Sub(Add(Mul(Num(64), A(8)), Mul(Num(3328), A(7))),
            Mul(Num(77824), A(6))), Mul(Num(1441792), A(5))), Mul(Num(28311552), A(4))),
            Mul(Num(33554432), A(3))), Mul(Num(1073741824), A(2)));
        var equation = Eq(A(9), rhs);
        return n is null ? equation : All("n", Q("Nat"), equation);
    }

    private static Formula UsedFormula()
    {
        var n = V("n"); var p = V("P");
        var cells = Product(Fin(D(4)), Fin(n));
        return All("n", Q("Nat"), All("P", Arrow(cells, Fin(D(3))),
            Eq(Own("used", p), Call("Nat.card", Parenthesized(Call("Set.range", p))))));
    }

    private static Formula NormalCondition(Formula n, Formula a)
    {
        var p = V("p"); var q = V("q");
        var cells = Product(Fin(D(4)), Fin(n));
        Formula Rank(Formula x) => Add(Mul(Val(Call("Prod.fst", x)), n),
            Val(Call("Prod.snd", x)));
        Formula Earlier(byte colour) => Ex("q", cells,
            And(Lt(Rank(q), Rank(p)), Eq(App(a, q), Typed(D(colour), Fin(D(6))))));
        var current = App(a, p);
        return All("p", cells, And(
            Imp(Or(Eq(current, Typed(D(2), Fin(D(6)))),
                Or(Eq(current, Typed(D(3), Fin(D(6)))),
                    Eq(current, Typed(D(4), Fin(D(6)))))), Earlier(1)),
            Imp(Eq(current, Typed(D(3), Fin(D(6)))), Earlier(2))));
    }

    private static Formula NormalFormula()
    {
        var n = V("n"); var a = V("A");
        var cells = Product(Fin(D(4)), Fin(n));
        return All("n", Q("Nat"), All("A", Arrow(cells, Fin(D(6))),
            Eq(Own("normal", a), Parenthesized(NormalCondition(n, a)))));
    }

    private static Formula DecidableNormalFormula()
    {
        var n = V("n"); var a = V("A");
        var cells = Product(Fin(D(4)), Fin(n));
        Formula Decides(Formula proposition) => Call("Decidable", Parenthesized(proposition));
        return All("n", Q("Nat"), All("A", Arrow(cells, Fin(D(6))),
            Eq(Typed(Own("instDecidableNormal", a), Decides(Own("normal", a))),
                Call("inferInstanceAs", Parenthesized(Decides(NormalCondition(n, a)))))));
    }

    private static Formula LegalFormula()
    {
        var n = V("n"); var a = V("A"); var j = V("j");
        var r = V("r"); var s = V("s"); var h = V("h");
        var cells = Product(Fin(D(4)), Fin(n));
        var first = Ex("j", Fin(n),
            And(Eq(Val(j), D(0)), Eq(App(a, Pair(Typed(D(0), Fin(D(4))), j)),
                Typed(D(0), Fin(D(6))))));
        var adjacent = And(Le(Val(r), Add(Val(s), D(1))),
            Le(Val(s), Add(Val(r), D(1))));
        var here = App(a, Pair(r, j));
        var next = App(a, Pair(s, Typed(Call("Fin.mk", Add(Val(j), D(1)), h), Fin(n))));
        var bonds = All("j", Fin(n), All("h", Lt(Add(Val(j), D(1)), n),
            All("r", Fin(D(4)), All("s", Fin(D(4)), Imp(adjacent,
                And(Ne(here, next), Ne(Add(Val(here), Val(next)), D(5))))))));
        return All("n", Q("Nat"), All("A", Arrow(cells, Fin(D(6))),
            Eq(Own("Legal", a), Parenthesized(And(first, And(bonds, Own("normal", a)))))));
    }

    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A");
        var arrays = Arrow(Product(Fin(D(4)), Fin(n)), Fin(D(6)));
        return All("n", Q("Nat"), Eq(Own("a", n), Call("Finset.card",
            Call("Finset.filter", Fn("A", arrays, Own("Legal", a)), Q("Finset.univ")))));
    }

    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { NamePart(part) } : new[] { Dot, NamePart(part) }).ToArray());
    private static Formula NamePart(string name)
    {
        var words = name.Split('_');
        Formula result = V(words[^1]);
        for (var i = words.Length - 2; i >= 0; --i)
            result = Seq(V(words[i]), Underscore, Grp(result));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Own(string name, params Formula[] args) =>
        Call(LeanPrefix + name, args);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula App(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula x, Formula type) =>
        Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
}
