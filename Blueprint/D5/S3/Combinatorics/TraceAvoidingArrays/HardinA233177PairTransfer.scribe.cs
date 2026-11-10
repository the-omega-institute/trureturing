using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233177PairTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.";
    private const string LeanPrefix =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233177");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fourteen-class transfer for proper four-row pair-label patterns.",
        H("Pair-label patterns and their column classes"),
        Blocks(
            Paragraph(Text("A column has four labels in Fin 3. Two consecutive columns "
                + "are compatible when labels at row distance at most one differ. "
                + "Relabelling the three labels preserves compatibility. The fourteen "
                + "first-appearance representatives are 0000, 0001, 0010, 0011, 0012, "
                + "0100, 0101, 0102, 0110, 0111, 0112, 0120, 0121 and 0122. "
                + "The constant column has three relabellings; each other representative "
                + "has six. A finite check counts all compatible successors in every "
                + "class for every one of the 81 columns. TransferMatrix.cardMatrix "
                + "propagates these equalities to arbitrary width.")),
            Node("Proper", "Proper pair-label patterns", ProperFormula(), false),
            Node("L", "Literal pair-pattern count", CountFormula(), false),
            Node("Col", "Four-label columns", ColFormula(), false),
            Node("column", "Column coordinates", ColumnFormula(), false),
            Node("cls", "The fourteen equality classes", ClassFormula(), false),
            Node("representatives", "First-appearance representatives", RepresentativesFormula(), false),
            Node("relabel", "Coordinatewise label permutations", RelabelFormula(), false),
            Node("column_relabel", "Relabelling column coordinates", ColumnRelabelFormula(), true),
            Node("class_relabel", "Relabelling preserves equality classes", ClassRelabelFormula(), true),
            Node("class_rep", "Every column has a representative", ClassRepFormula(), true),
            Node("gridEquiv", "Grids as sequences of columns", GridEquivFormula(), false),
            Node("column_grid", "Recovering a grid entry", ColumnGridFormula(), true),
            Node("initial_values", "Eight initial pair-pattern counts", InitialFormula(), true),
            Node("recurrence", "The constant-adjusted pair-pattern recurrence",
                RecurrenceFormula(), true),
            Paragraph(Text("The continuation vectors satisfy the sextic "
                + "x^6-3*x^5-16*x^4+3*x^3+25*x^2-2*x-4 after one transition. "
                + "TransferMatrix.tabulatedPowers verifies the first eight vectors and "
                + "TransferMatrix.scalarRelationShift propagates the finite relation. "
                + "Subtracting consecutive sextic relations multiplies by x-1 and "
                + "also annihilates the constant six.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, bool theorem) =>
        Describe.Lean(DescribeId.Create(name == "gridEquiv" ? "grid-equiv"
                : name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(title + "."))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula ColFormula() =>
        Eq(Own("Col"), Product(Fin(D(3)), Product(Fin(D(3)), Product(Fin(D(3)), Fin(D(3))))));

    private static Formula ColumnFormula()
    {
        var c = V("c");
        return All("c", Own("Col"), Eq(Own("column", c),
            Typed(Vector(Call("Prod.fst", c), Call("Prod.fst", Call("Prod.snd", c)),
                Call("Prod.fst", Call("Prod.snd", Call("Prod.snd", c))),
                Call("Prod.snd", Call("Prod.snd", Call("Prod.snd", c)))),
                Arrow(Fin(D(4)), Fin(D(3))))));
    }

    private static Formula ClassFormula()
    {
        var a = V("a"); var b = V("b"); var d = V("d"); var e = V("e"); var c = V("c");
        var body = If(Eq(a, b), If(Eq(a, d), If(Eq(a, e), D(0), D(1)),
            If(Eq(a, e), D(2), If(Eq(d, e), D(3), D(4)))),
            If(Eq(a, d), If(Eq(a, e), D(5), If(Eq(b, e), D(6), D(7))),
            If(Eq(b, d), If(Eq(a, e), D(8), If(Eq(b, e), D(9), D(1,0))),
            If(Eq(a, e), D(1,1), If(Eq(b, e), D(1,2), D(1,3))))));
        body = Let("a", Fin(D(3)), Call("Prod.fst", c),
            Let("b", Fin(D(3)), Call("Prod.fst", Call("Prod.snd", c)),
            Let("d", Fin(D(3)), Call("Prod.fst", Call("Prod.snd", Call("Prod.snd", c))),
            Let("e", Fin(D(3)), Call("Prod.snd", Call("Prod.snd", Call("Prod.snd", c))), body))));
        return All("c", Own("Col"), Eq(Own("cls", c), Typed(body, Fin(D(1,4)))));
    }

    private static Formula RepresentativesFormula() => Eq(Own("representatives"),
        Typed(Vector(Column(0,0,0,0), Column(0,0,0,1), Column(0,0,1,0), Column(0,0,1,1),
            Column(0,0,1,2), Column(0,1,0,0), Column(0,1,0,1), Column(0,1,0,2),
            Column(0,1,1,0), Column(0,1,1,1), Column(0,1,1,2), Column(0,1,2,0),
            Column(0,1,2,1), Column(0,1,2,2)), Arrow(Fin(D(1,4)), Own("Col"))));

    private static Formula RelabelFormula()
    {
        var e = V("e");
        return All("e", Perm(), Eq(Own("relabel", e),
            Call("Equiv.prodCongr", e, Call("Equiv.prodCongr", e, Call("Equiv.prodCongr", e, e)))));
    }

    private static Formula ColumnRelabelFormula()
    {
        var e = V("e"); var c = V("c"); var r = V("r");
        return All("e", Perm(), All("c", Own("Col"), All("r", Fin(D(4)),
            Eq(Own("column", ApplyRelabel(e, c), r),
                App(Typed(e, Arrow(Fin(D(3)), Fin(D(3)))), Own("column", c, r))))));
    }

    private static Formula ClassRelabelFormula() =>
        All("e", Perm(), All("c", Own("Col"),
            Eq(Own("cls", ApplyRelabel(V("e"), V("c"))), Own("cls", V("c")))));

    private static Formula ClassRepFormula() =>
        All("c", Own("Col"), Ex("e", Perm(),
            Eq(ApplyRelabel(V("e"), V("c")), Own("representatives", Own("cls", V("c"))))));

    private static Formula GridEquivFormula()
    {
        var n = V("n"); var p = V("P"); var j = V("j"); var f = V("f"); var cell = V("p");
        var arrays = Arrow(Cells(n), Fin(D(3))); var columns = Arrow(Fin(n), Own("Col"));
        var forward = Fn("P", arrays, Fn("j", Fin(n),
            Pair(App(p, Pair(D(0), j)), Pair(App(p, Pair(D(1), j)),
                Pair(App(p, Pair(D(2), j)), App(p, Pair(D(3), j)))))));
        var inverse = Fn("f", columns, Fn("p", Cells(n),
            Own("column", App(f, Call("Prod.snd", cell)), Call("Prod.fst", cell))));
        var leftInverse = Fn("P", arrays, Seq(V("by"), Sp, V("funext"), Sp, cell, Semi, Sp,
            V("rcases"), Sp, cell, Sp, V("with"), Sp, Langle, Sp, V("r"), Comma, j, Rangle, Semi, Sp,
            Q("fin_cases"), Sp, V("r"), Sp, F.Lt, Semi, F.Gt, Sp, V("rfl")));
        var rightInverse = Fn("f", columns, Call("Eq.refl", f));
        return All("n", Q("Nat"), Eq(Own("gridEquiv", n),
            Call("Equiv.mk", forward, inverse, leftInverse, rightInverse)));
    }

    private static Formula ColumnGridFormula()
    {
        var n = V("n"); var p = V("P"); var j = V("j"); var r = V("r");
        return All("n", Q("Nat"), All("P", Arrow(Cells(n), Fin(D(3))),
            All("j", Fin(n), All("r", Fin(D(4)),
                Eq(Own("column", App(Typed(Own("gridEquiv", n),
                    Arrow(Arrow(Cells(n), Fin(D(3))), Arrow(Fin(n), Own("Col")))), p, j), r),
                    App(p, Pair(r, j)))))));
    }

    private static Formula Perm() => Call("Equiv.Perm", Fin(D(3)));
    private static Formula ApplyRelabel(Formula e, Formula c) =>
        App(Typed(Own("relabel", e), Arrow(Own("Col"), Own("Col"))), c);
    private static Formula Column(byte a, byte b, byte c, byte d) =>
        Typed(Pair(D(a), Pair(D(b), Pair(D(c), D(d)))), Own("Col"));
    private static Formula Vector(params Formula[] entries) => Seq(Bang, OpenBracket,
        Seq(entries.SelectMany((entry, i) => i == 0
            ? new[] { entry } : new[] { Comma, Sp, entry }).ToArray()), CloseBracket);
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Parenthesized(Seq(V("if"), Sp, condition, Sp, V("then"), Sp, yes, Sp, V("else"), Sp, no));
    private static Formula Let(string name, Formula type, Formula value, Formula body) =>
        Parenthesized(Seq(V("let"), Sp, V(name), Colon, Sp, type, Sp, Colon, F.Eq, Sp,
            value, Semi, Sp, body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));

    private static Formula ProperFormula()
    {
        var n = V("n"); var p = V("P"); var j = V("j"); var r = V("r"); var s = V("s");
        var next = Call("Fin.mk", Add(Val(j), D(1)), V("h"));
        var body = All("j", Fin(n), All("h", Lt(Add(Val(j), D(1)), n),
            All("r", Fin(D(4)), All("s", Fin(D(4)), Imp(
                And(Le(Val(r), Add(Val(s), D(1))), Le(Val(s), Add(Val(r), D(1)))),
                Ne(App(p, Pair(r, j)), App(p, Pair(s, next))))))));
        return All("n", Q("Nat"), All("P", Arrow(Cells(n), Fin(D(3))),
            Eq(Own("Proper", p), Parenthesized(body))));
    }

    private static Formula CountFormula()
    {
        var n = V("n"); var p = V("P"); var arrays = Arrow(Cells(n), Fin(D(3)));
        return All("n", Q("Nat"), Eq(Own("L", n), Call("Finset.card",
            Call("Finset.filter", Fn("P", arrays, Own("Proper", p)),
                Typed(Q("Finset.univ"), Call("Finset", arrays))))));
    }

    private static Formula InitialFormula()
    {
        var k = V("k");
        var values = Seq(Bang, OpenBracket, D(1,6,2), Comma, Sp, D(1,1,2,2), Comma, Sp,
            D(5,8,0,8), Comma, Sp, D(3,3,7,0,2), Comma, Sp, D(1,8,6,7,2,0), Comma, Sp,
            D(1,0,5,4,4,4,6), Comma, Sp, D(5,9,0,7,4,4,4), Comma, Sp,
            D(3,3,2,0,6,8,6,2), CloseBracket);
        return All("k", Fin(D(8)), Eq(Typed(Own("L", Add(Val(k), D(2))), Q("Int")),
            App(Typed(values, Arrow(Fin(D(8)), Q("Int"))), k)));
    }

    private static Formula RecurrenceFormula()
    {
        var n = V("n");
        Formula B(int i) => Add(Typed(Own("L", Add(n, Num(i))), Q("Int")), D(6));
        var rhs = Sub(Add(Add(Sub(Sub(Add(Mul(D(4), B(9)), Mul(D(1,3), B(8))),
            Mul(D(1,9), B(7))), Mul(D(2,2), B(6))), Mul(D(2,7), B(5))),
            Mul(D(2), B(4))), Mul(D(4), B(3)));
        return All("n", Q("Nat"), Eq(B(10), rhs));
    }

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
    private static Formula Cells(Formula n) => Product(Fin(D(4)), Fin(n));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Own(string name, params Formula[] args) =>
        Call(LeanPrefix + name, args);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Q(name) : App(Q(name), args);
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
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
}
