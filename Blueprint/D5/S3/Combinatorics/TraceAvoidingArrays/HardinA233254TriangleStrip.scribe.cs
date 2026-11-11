using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233254TriangleStripDocument : IScribeDocumentDefinition
{
    private const string Root =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233254TriangleStrip";
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233254TriangleStrip.";
    private const string Scanner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.";
    private const string Transfer =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.";
    private const string Beta = "D5.S3.Observer.Separation.BooleanRankThreeK4.beta";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233254");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barker's generating function for the literal normalized six-column strip.",
        H("Six-column complementary-pair exclusion"), Blocks(
            Paragraph(Text(
                "The coefficient at zero is zero. Only horizontal and antidiagonal bonds "
                + "are constrained. Vertical and main-diagonal neighbours are unconstrained. "
                + "The first cell is zero. In row-major order, each 2, 3 or 4 has an earlier "
                + "1, and each 3 an earlier 2. Fin.val is the coercion to natural numbers; "
                + "Fin.mk constructs a bounded index with the displayed proof. Nat.div is "
                + "natural quotient division and Nat.mod its nonnegative remainder. Neither "
                + "operation occurs in these definitions.")),
            Def("row", "Row", "A row", Eq(N("Row"), Arrow(Fin(6), Fin(6))),
                "Rows are functions on six ordered column indices."),
            Def("boundary", "Boundary", "A boundary",
                Eq(N("Boundary"), Arrow(Fin(5), Fin(3))),
                "The five labels record complementary pairs at column indices 1 through 5."),
            Def("horizontal", "rowLegal", "Horizontal exclusions", RowFormula(),
                "The conjunction excludes equality and a natural-number sum of five."),
            Def("decidablerowlegal", "instDecidableRowLegal", "Deciding horizontal exclusions",
                DecidableRowLegalFormula(),
                "The defining lambda uses inferInstanceAs for the finite conjunction of "
                + "the two horizontal exclusions."),
            Def("pairs", "pairs", "Boundary labels", PairsFormula(),
                "The lambda retains the ordered five-column boundary."),
            Def("compatible", "compatible", "Antidiagonal exclusions", CompatibleFormula(),
                "Each old boundary label excludes the corresponding next-row label."),
            Def("count", "a", "The literal finite count", CountFormula(),
                "The filter ranges over every array function and directly uses "
                + "HardinA233251TriangleStrip.widthLegal at width six, with rowLegal and "
                + "the displayed antidiagonal row relation. The displayed equality expands "
                + "that owner predicate. Its published decidability instances and the "
                + "published pair-strip allowed-colour instance supply the decisions. "
                + "The existential first-cell "
                + "condition is false when n is zero. The final predicate is the original "
                + "row-major scanner predicate at both false flags.", true),
            Def("valid", "Valid", "Reachable boundaries", ValidFormula(),
                "The first flag is true. Adjacent boundary labels differ. If colour two "
                + "has not occurred, none of the boundary labels is its pair label two."),
            Def("shape", "shape", "Boundary equality shapes", ShapeFormula(),
                "The labels A, B, C in the shapes are distinct. In order the shapes are "
                + "ABABA, ABABC, ABACA, ABACB, ABCAB, ABCAC, ABCBA and ABCBC."),
            Def("moment", "moment", "Boundary transfer moments", MomentFormula(),
                "The four entries are the constant one and the first three moments of "
                + "the label transfer. The published HardinA233255ShapeSymmetry.full_row, "
                + "used with HardinA233255LiteralBridge.scanner_fibres, gives 64 colour "
                + "lifts at width six when both scanner flags are true. More generally "
                + "each column has a factor of zero, "
                + "one or two: pair zero has two choices; pair one has one choice before "
                + "the first one, then two; pair two is forbidden before one, has one "
                + "choice before the first two, then two. Multiplying these factors "
                + "along the label row reproduces the original colour scanner."),
            Def("classcount", "classCount", "Unweighted row counts", ClassCountFormula(),
                "The final second flag distinguishes the two seen-colour sectors."),
            Def("momentcount", "momentCount", "Weighted row counts", MomentCountFormula(),
                "The weight is a moment of the new boundary in the fully seen sector."),
            Def("firstcount", "firstCount", "First-row counts", FirstCountFormula(),
                "The scanner starts with both flags false and the first colour fixed to zero."),
            Def("firstmoment", "firstMoment", "First-row weighted count", FirstMomentFormula(),
                "Only fully seen first rows contribute the chosen boundary moment."),
            Thm("sumrows", "sum_rows", "Summing six-cell functions", SumRowsFormula(),
                "The sum over functions equals the six iterated sums of their coordinates."),
            Thm("certificate", "finite_certificate", "One-row transfer counts",
                CertificateFormula(),
                "Write r, t, u for moments one, two and three. A fully seen boundary has "
                + "64r continuations, with moment sums 64t, 64u and 64(81r-90t+25u). "
                + "Before colour two has appeared, 64 continuations stay in that sector "
                + "and 800 enter the fully seen sector. Their moment sums are 17216, "
                + "360576 and 7530048. Initially the two counts are 16 and 120, with "
                + "moment sums 2384, 49344 and 1028832."),
            Resolution("result", "result", "Barker's identity", ResultFormula(),
                "After one continuation row the fully seen count has form rU+tZ+uW. "
                + "Initially (F,U,Z,W)=(864,64,0,0), where F is the other sector. "
                + "The one-row formulas give F'=64F+17216U+360576Z+7530048W, "
                + "U'=5184W, Z'=64U-5760W and W'=64Z+1600W. The three latter "
                + "coordinates have characteristic polynomial "
                + "z^3-1600z^2+368640z-21233664. The shared literal counting bridge gives "
                + "a(n+2)=16F(n)+2384U(n)+49344Z(n)+1028832W(n). The initial count "
                + "a(1)=136 is 16+120. Thus a(n+6)=1664a(n+5)-471040a(n+4) "
                + "+44826624a(n+3)-1358954496a(n+2). The first terms are 136, 166400, "
                + "220626944, 294517735424 and 393427728465920. Coefficient comparison "
                + "in integer power series proves the identity, including the zero-index "
                + "convention. The initial constant function can have a zero-eigenvalue "
                + "part; taking one row first gives the three-dimensional nonzero part."))));

    private static DocumentBlock Def(string id, string name, string title, Formula formula,
        string prose, bool literature = false) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Thm(string id, string name, string title, Formula formula,
        string prose) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Resolution(string id, string name, string title,
        Formula formula, string prose) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233254"),
                ResolutionKind.Proved));

    private static Formula SumRowsFormula()
    {
        var m = V("m"); var f = V("f");
        var fm = Call("Fin", m);
        Formula rhs = App(f, Vector(V("a"), V("b"), V("c"), V("d"), V("e"), V("g")));
        foreach (var n in new[] { "g", "e", "d", "c", "b", "a" })
            rhs = SumOver(n, fm, rhs);
        return All("m", Q("Nat"), All("f", Arrow(Arrow(Fin(6), fm), Q("Int")),
            Eq(SumOver("c", Arrow(Fin(6), fm), App(f, V("c"))), rhs)));
    }

    private static Formula RowFormula()
    {
        var c = V("c"); var j = V("j");
        var x = App(c, Call("Fin.castSucc", j));
        var y = App(c, Call("Fin.succ", j));
        return All("c", N("Row"), Eq(CallLocal("rowLegal", c), All("j", Fin(5),
            And(Ne(x, y), Ne(Add(Val(x), Val(y)), Num(5))))));
    }
    private static Formula DecidableRowLegalFormula()
    {
        var c = V("c"); var j = V("j");
        var x = App(c, Call("Fin.castSucc", j));
        var y = App(c, Call("Fin.succ", j));
        var body = All("j", Fin(5), And(Ne(x, y), Ne(Add(Val(x), Val(y)), Num(5))));
        return Eq(Typed(N("instDecidableRowLegal"), Call("DecidablePred", N("rowLegal"))),
            Parenthesized(Fn("c", N("Row"),
                Call("inferInstanceAs", Parenthesized(Call("Decidable", Parenthesized(body)))))));
    }
    private static Formula PairsFormula() => All("c", N("Row"),
        Eq(CallLocal("pairs", V("c")), Fn("j", Fin(5),
            Call(Beta, App(V("c"), Call("Fin.succ", V("j")))))));
    private static Formula CompatibleFormula() => All("p", N("Boundary"),
        All("c", N("Row"), Eq(CallLocal("compatible", V("p"), V("c")),
            All("j", Fin(5), Ne(App(V("p"), V("j")),
                Call(Beta, App(V("c"), Call("Fin.castSucc", V("j")))))))));
    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A"); var i = V("i"); var j = V("j");
        Formula Cell(Formula r, Formula k) => App(a, Pair(r, k));
        var first = Ex("i", Call("Fin", n),
            And(Eq(Val(i), Num(0)), Eq(Cell(i, Index(0, 6)), Index(0, 6))));
        var horizontal = All("i", Call("Fin", n),
            CallLocal("rowLegal", Fn("j", Fin(6), Cell(i, j))));
        var next = Call("Fin.mk", Add(Val(i), Num(1)), V("h"));
        var x = Cell(i, Call("Fin.succ", j));
        var y = Cell(next, Call("Fin.castSucc", j));
        var anti = All("i", Call("Fin", n), All("h", Lt(Add(Val(i), Num(1)), n),
            All("j", Fin(5), And(Ne(x, y), Ne(Add(Val(x), Val(y)), Num(5))))));
        var normal = Call(Transfer + "widthNormal", Pair(V("false"), V("false")),
            Fn("i", Call("Fin", n), Fn("j", Fin(6), Cell(i, j))));
        var arrays = Arrow(Product(Call("Fin", n), Fin(6)), Fin(6));
        var c = V("c"); var d = V("d");
        var oldCell = App(c, Call("Fin.succ", j));
        var newCell = App(d, Call("Fin.castSucc", j));
        var bonds = Fn("c", N("Row"), Fn("d", N("Row"), All("j", Fin(5),
            And(Ne(oldCell, newCell), Ne(Add(Val(oldCell), Val(newCell)), Num(5))))));
        var owner = Call(Transfer + "widthLegal", N("rowLegal"), bonds, a);
        var literal = And(first, And(horizontal, And(anti, normal)));
        var filter = Call("Finset.filter", Fn("A", arrays, owner), Q("Finset.univ"));
        return All("n", Q("Nat"), And(All("A", arrays, Eq(owner, Parenthesized(literal))),
            Eq(CallLocal("a", n), Call("Finset.card", filter))));
    }
    private static Formula ValidFormula()
    {
        var s = V("s"); var p = V("p"); var j = V("j");
        var adjacent = All("j", Fin(4),
            Ne(App(p, Call("Fin.castSucc", j)), App(p, Call("Fin.succ", j))));
        var absent = Imp(Eq(Proj(s, 2), V("false")),
            All("j", Fin(5), Ne(App(p, j), Index(2, 3))));
        return All("s", Q(Scanner + "Seen"), All("p", N("Boundary"),
            Eq(CallLocal("Valid", s, p),
                Parenthesized(And(Eq(Proj(s, 1), V("true")), And(adjacent, absent))))));
    }
    private static Formula ShapeFormula()
    {
        Formula At(byte i) => App(V("p"), Index(i, 5));
        Formula I(byte i) => Index(i, 8);
        return All("p", N("Boundary"), Eq(CallLocal("shape", V("p")),
            Conditional(Eq(At(2), At(0)),
                Conditional(Eq(At(3), At(1)),
                    Conditional(Eq(At(4), At(0)), I(0), I(1)),
                    Conditional(Eq(At(4), At(0)), I(2), I(3))),
                Conditional(Eq(At(3), At(0)),
                    Conditional(Eq(At(4), At(1)), I(4), I(5)),
                    Conditional(Eq(At(4), At(0)), I(6), I(7))))));
    }
    private static Formula MomentFormula()
    {
        var shape = CallLocal("shape", V("p"));
        return All("p", N("Boundary"), Eq(CallLocal("moment", V("p")), Vector(
            Cast(Num(1)),
            App(IntVector(26, 22, 24, 18, 12, 18, 20, 22), shape),
            App(IntVector(564, 456, 516, 354, 222, 366, 426, 462), shape),
            App(IntVector(11832, 9510, 10812, 7320, 4542, 7620, 8922, 9660), shape))));
    }
    private static Formula RowCondition(Formula s, Formula p, Formula c, Formula b) =>
        And(CallLocal("rowLegal", c), And(CallLocal("compatible", p, c),
            And(Call(Scanner + "good", s, c), Eq(Proj(Call(Scanner + "finish", s, c), 2), b))));
    private static Formula FirstCondition(Formula c, Formula b)
    {
        var s = Pair(V("false"), V("false"));
        return And(Eq(App(c, Index(0, 6)), Index(0, 6)),
            And(CallLocal("rowLegal", c), And(Call(Scanner + "good", s, c),
                Eq(Proj(Call(Scanner + "finish", s, c), 2), b))));
    }
    private static Formula ClassCountFormula() =>
        All("s", Q(Scanner + "Seen"), All("p", N("Boundary"), All("b", Q("Bool"),
            Eq(CallLocal("classCount", V("s"), V("p"), V("b")), SumOver("c", N("Row"),
                Conditional(RowCondition(V("s"), V("p"), V("c"), V("b")),
                    Cast(Num(1)), Cast(Num(0))))))));
    private static Formula MomentCountFormula() =>
        All("s", Q(Scanner + "Seen"), All("p", N("Boundary"), All("i", Fin(4),
            Eq(CallLocal("momentCount", V("s"), V("p"), V("i")), SumOver("c", N("Row"),
                Conditional(RowCondition(V("s"), V("p"), V("c"), V("true")),
                    CallLocal("moment", CallLocal("pairs", V("c")), V("i")), Cast(Num(0))))))));
    private static Formula FirstCountFormula() => All("b", Q("Bool"),
        Eq(CallLocal("firstCount", V("b")), SumOver("c", N("Row"),
            Conditional(FirstCondition(V("c"), V("b")), Cast(Num(1)), Cast(Num(0))))));
    private static Formula FirstMomentFormula() => All("i", Fin(4),
        Eq(CallLocal("firstMoment", V("i")), SumOver("c", N("Row"),
            Conditional(FirstCondition(V("c"), V("true")),
                CallLocal("moment", CallLocal("pairs", V("c")), V("i")), Cast(Num(0))))));
    private static Formula CertificateFormula()
    {
        var s = V("s"); var p = V("p"); var i = V("i");
        Formula M(byte k) => CallLocal("moment", p, Index(k, 4));
        var last = Add(Sub(Mul(Cast(Num(81)), M(1)), Mul(Cast(Num(90)), M(2))),
            Mul(Cast(Num(25)), M(3)));
        var moments = All("i", Fin(3),
            Eq(CallLocal("momentCount", s, p, Call("Fin.succ", i)), Conditional(Proj(s, 2),
                Mul(Cast(Num(64)), App(Vector(M(2), M(3), last), i)),
                App(IntVector(17216, 360576, 7530048), i))));
        var rows = All("s", Q(Scanner + "Seen"), All("p", N("Boundary"),
            Imp(CallLocal("Valid", s, p), And(
                Eq(CallLocal("classCount", s, p, V("true")), Conditional(Proj(s, 2),
                    Mul(Cast(Num(64)), M(1)), Cast(Num(800)))), And(
                Eq(CallLocal("classCount", s, p, V("false")),
                    Conditional(Proj(s, 2), Cast(Num(0)), Cast(Num(64)))), moments)))));
        return And(rows, And(Eq(CallLocal("firstCount", V("true")), Cast(Num(120))),
            And(Eq(CallLocal("firstCount", V("false")), Cast(Num(16))),
                All("i", Fin(3), Eq(CallLocal("firstMoment", Call("Fin.succ", i)),
                    App(IntVector(2384, 49344, 1028832), i))))));
    }
    private static Formula ResultFormula()
    {
        var x = Q("PowerSeries.X");
        var cubic = Sub(Add(Sub(Num(1), Mul(Num(1600), x)),
            Mul(Num(368640), Pow(x, Num(2)))), Mul(Num(21233664), Pow(x, Num(3))));
        var left = Mul(Mul(Sub(Num(1), Mul(Num(64), x)), cubic),
            Call("PowerSeries.mk", Fn("n", Q("Nat"), Cast(CallLocal("a", V("n"))))));
        var right = Mul(Mul(Num(8), x), Sub(Add(Sub(Num(17), Mul(Num(7488), x)),
            Mul(Num(974848), Pow(x, Num(2)))), Mul(Num(40108032), Pow(x, Num(3)))));
        return Eq(Typed(left, Call("PowerSeries", Q("Int"))), right);
    }
    private static Formula IntVector(params int[] values) =>
        Vector(values.Select(n => Cast(Num(n))).ToArray());
    private static Formula Vector(params Formula[] values) => values.Reverse().Aggregate(
        Q("Matrix.vecEmpty"), (tail, head) => Call("Matrix.vecCons", head, tail));

    private static Formula N(string name) => Q(Root + "." + name);
    private static Formula CallLocal(string name, params Formula[] args) => App(N(name), args);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { Word(part) } : new[] { Dot, Word(part) }).ToArray());
    private static Formula Word(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(int n) =>
        D(n.ToString(System.Globalization.CultureInfo.InvariantCulture)
            .Select(c => (byte)(c - '0')).ToArray());
    private static Formula Fin(byte n) => Call("Fin", Num(n));
    private static Formula Index(byte n, byte bound) => Typed(Num(n), Fin(bound));
    private static Formula App(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula type) =>
        Parenthesized(Seq(f, Colon, Sp, type));
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Proj(Formula a, byte i) => Call(i == 1 ? "Prod.fst" : "Prod.snd", a);
    private static Formula Cast(Formula a) => Typed(a, Q("Int"));
    private static Formula Val(Formula a) => Call("Fin.val", a);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Parenthesized(Seq(Word("if"), Sp, Parenthesized(condition), Sp, Word("then"), Sp,
            yes, Sp, Word("else"), Sp, no));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(name), Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => Seq(Parenthesized(a), Caret, Grp(b));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Fn(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, Parenthesized(body));
}
