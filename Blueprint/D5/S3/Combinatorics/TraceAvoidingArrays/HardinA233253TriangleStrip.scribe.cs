using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233253TriangleStripDocument : IScribeDocumentDefinition
{
    private const string Root =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233253TriangleStrip";
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233253TriangleStrip.";
    private const string Scanner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.";
    private const string Transfer =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.";
    private const string Beta = "D5.S3.Observer.Separation.BooleanRankThreeK4.beta";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233253");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barker's generating function for the literal normalized five-column strip.",
        H("Five-column complementary-pair exclusion"), Blocks(
            Paragraph(Text(
                "The coefficient at zero is zero. Only horizontal and antidiagonal bonds "
                + "are constrained. Vertical and main-diagonal neighbours are unconstrained. "
                + "The first cell is zero. In row-major order, each 2, 3 or 4 has an earlier "
                + "1, and each 3 an earlier 2. Fin.val is the coercion to natural numbers; "
                + "Fin.mk constructs a bounded index with the displayed proof. Nat.div is "
                + "natural quotient division and Nat.mod its nonnegative remainder. Neither "
                + "operation occurs in these definitions.")),
            Def("row", "Row", "A row", Eq(N("Row"), Arrow(Fin(5), Fin(6))),
                "Rows are functions on five ordered column indices."),
            Def("boundary", "Boundary", "A boundary",
                Eq(N("Boundary"), Arrow(Fin(4), Fin(3))),
                "The four labels record complementary pairs at column indices 1 through 4."),
            Def("horizontal", "rowLegal", "Horizontal exclusions", RowFormula(),
                "The conjunction excludes equality and a natural-number sum of five."),
            Def("decidable-rowlegal", "instDecidableRowLegal", "Deciding horizontal exclusions",
                DecidableRowFormula(), "The horizontal predicate has a finite decision procedure."),
            Def("pairs", "pairs", "Boundary labels", PairsFormula(),
                "The lambda retains the ordered four-column boundary."),
            Def("compatible", "compatible", "Antidiagonal exclusions", CompatibleFormula(),
                "Each old boundary label excludes the corresponding next-row label."),
            Def("count", "a", "The literal finite count", CountFormula(),
                "The filter ranges over every array function. The existential first-cell "
                + "condition is false when n is zero. The final predicate is the original "
                + "row-major scanner predicate at both false flags.", true),
            Def("valid", "Valid", "Reachable boundaries", ValidFormula(),
                "The first flag is true. Adjacent boundary labels differ. If colour two "
                + "has not occurred, none of the boundary labels is its pair label two."),
            Def("rank", "rank", "A boundary statistic", RankFormula(),
                "The shapes ABAB, ABAC, ABCA and ABCB have ranks 3, 2, 0 and 2."),
            Def("classcount", "classCount", "Unweighted row counts", ClassCountFormula(),
                "The final second flag distinguishes the two seen-colour sectors."),
            Def("rankcount", "rankCount", "Weighted row counts", RankCountFormula(),
                "The weight is the rank of the new boundary in the fully seen sector."),
            Def("firstcount", "firstCount", "First-row counts", FirstCountFormula(),
                "The scanner starts with both flags false and the first colour fixed to zero."),
            Def("firstrank", "firstRank", "First-row weighted count", FirstRankFormula(),
                "Only fully seen first rows contribute their boundary rank."),
            Thm("certificate", "finite_certificate", "One-row transfer counts",
                CertificateFormula(),
                "At a fully seen boundary of rank r, the row count is 320+64r and the "
                + "rank sum is 512+160r. From the other sector, 32 rows stay there, "
                + "240 enter the fully seen sector and their rank sum is 448. The "
                + "initial counts are eight and 28, with fully seen rank sum 44."),
            Resolution("result", "result", "Barker's identity", ResultFormula(),
                "The continuations from length zero have form F without colour two, and U+rZ "
                + "in the fully seen sector. At length zero, F=U=1 and Z=0. The one-row "
                + "identities give F'=32F+240U+448Z, U'=320U+512Z and Z'=64U+160Z. "
                + "The shared strip counting theorem gives a(n+1)=8F(n)+28U(n)+44Z(n). "
                + "Consequently a(n+4)=512a(n+3)-33792a(n+2)+589824a(n+1), "
                + "and a(1), a(2), a(3) are 36, 13952, 6049792. Comparing coefficients "
                + "in integer power series proves the displayed identity."))));

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
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233253"),
                ResolutionKind.Proved));

    private static Formula DecidableRowFormula()
    {
        var c = V("c"); var j = V("j");
        var x = App(c, Call("Fin.castSucc", j));
        var y = App(c, Call("Fin.succ", j));
        var body = All("j", Fin(4), And(Ne(x, y), Ne(Add(Val(x), Val(y)), Num(5))));
        return All("c", N("Row"), Eq(
            Typed(CallLocal("instDecidableRowLegal", c),
                Call("Decidable", Parenthesized(CallLocal("rowLegal", c)))),
            Call("inferInstanceAs", Parenthesized(Call("Decidable", Parenthesized(body))))));
    }

    private static Formula RowFormula()
    {
        var c = V("c"); var j = V("j");
        var x = App(c, Call("Fin.castSucc", j));
        var y = App(c, Call("Fin.succ", j));
        return All("c", N("Row"), Eq(CallLocal("rowLegal", c), All("j", Fin(4),
            And(Ne(x, y), Ne(Add(Val(x), Val(y)), Num(5))))));
    }
    private static Formula PairsFormula() => All("c", N("Row"),
        Eq(CallLocal("pairs", V("c")), Fn("j", Fin(4),
            Call(Beta, App(V("c"), Call("Fin.succ", V("j")))))));
    private static Formula CompatibleFormula() => All("p", N("Boundary"),
        All("c", N("Row"), Eq(CallLocal("compatible", V("p"), V("c")),
            All("j", Fin(4), Ne(App(V("p"), V("j")),
                Call(Beta, App(V("c"), Call("Fin.castSucc", V("j")))))))));
    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A"); var i = V("i"); var j = V("j");
        Formula Cell(Formula r, Formula k) => App(a, Pair(r, k));
        var first = Ex("i", Call("Fin", n),
            And(Eq(Val(i), Num(0)), Eq(Cell(i, Index(0, 5)), Index(0, 6))));
        var horizontal = All("i", Call("Fin", n),
            CallLocal("rowLegal", Fn("j", Fin(5), Cell(i, j))));
        var next = Call("Fin.mk", Add(Val(i), Num(1)), V("h"));
        var x = Cell(i, Call("Fin.succ", j));
        var y = Cell(next, Call("Fin.castSucc", j));
        var anti = All("i", Call("Fin", n), All("h", Lt(Add(Val(i), Num(1)), n),
            All("j", Fin(4), And(Ne(x, y), Ne(Add(Val(x), Val(y)), Num(5))))));
        var normal = Call(Transfer + "widthNormal", Pair(V("false"), V("false")),
            Fn("i", Call("Fin", n), Fn("j", Fin(5), Cell(i, j))));
        var arrays = Arrow(Product(Call("Fin", n), Fin(5)), Fin(6));
        var filter = Call("Finset.filter", Fn("A", arrays,
            And(first, And(horizontal, And(anti, normal)))), Call("Finset.univ"));
        return All("n", Q("Nat"), Eq(CallLocal("a", n), Call("Finset.card", filter)));
    }
    private static Formula ValidFormula()
    {
        var s = V("s"); var p = V("p"); var j = V("j");
        var adjacent = All("j", Fin(3),
            Ne(App(p, Call("Fin.castSucc", j)), App(p, Call("Fin.succ", j))));
        var absent = Imp(Eq(Proj(s, 2), V("false")),
            All("j", Fin(4), Ne(App(p, j), Index(2, 3))));
        return All("s", Q(Scanner + "Seen"), All("p", N("Boundary"),
            Eq(CallLocal("Valid", s, p),
                Parenthesized(And(Eq(Proj(s, 1), V("true")), And(adjacent, absent))))));
    }
    private static Formula RankFormula()
    {
        Formula At(byte i) => App(V("p"), Index(i, 4));
        return All("p", N("Boundary"), Eq(CallLocal("rank", V("p")),
            Conditional(Eq(At(0), At(2)),
                Conditional(Eq(At(1), At(3)), Cast(Num(3)), Cast(Num(2))),
                Conditional(Eq(At(1), At(3)), Cast(Num(2)), Cast(Num(0))))));
    }
    private static Formula RowCondition(Formula s, Formula p, Formula c, Formula b) =>
        And(CallLocal("rowLegal", c), And(CallLocal("compatible", p, c),
            And(Call(Scanner + "good", s, c), Eq(Proj(Call(Scanner + "finish", s, c), 2), b))));
    private static Formula FirstCondition(Formula c, Formula b)
    {
        var s = Pair(V("false"), V("false"));
        return And(Eq(App(c, Index(0, 5)), Index(0, 6)),
            And(CallLocal("rowLegal", c), And(Call(Scanner + "good", s, c),
                Eq(Proj(Call(Scanner + "finish", s, c), 2), b))));
    }
    private static Formula ClassCountFormula() =>
        All("s", Q(Scanner + "Seen"), All("p", N("Boundary"), All("b", Q("Bool"),
            Eq(CallLocal("classCount", V("s"), V("p"), V("b")), SumOver("c", N("Row"),
                Conditional(RowCondition(V("s"), V("p"), V("c"), V("b")),
                    Cast(Num(1)), Cast(Num(0))))))));
    private static Formula RankCountFormula() =>
        All("s", Q(Scanner + "Seen"), All("p", N("Boundary"),
            Eq(CallLocal("rankCount", V("s"), V("p")), SumOver("c", N("Row"),
                Conditional(RowCondition(V("s"), V("p"), V("c"), V("true")),
                    CallLocal("rank", CallLocal("pairs", V("c"))), Cast(Num(0)))))));
    private static Formula FirstCountFormula() => All("b", Q("Bool"),
        Eq(CallLocal("firstCount", V("b")), SumOver("c", N("Row"),
            Conditional(FirstCondition(V("c"), V("b")), Cast(Num(1)), Cast(Num(0))))));
    private static Formula FirstRankFormula() => Eq(N("firstRank"), SumOver("c", N("Row"),
        Conditional(FirstCondition(V("c"), V("true")),
            CallLocal("rank", CallLocal("pairs", V("c"))), Cast(Num(0)))));
    private static Formula CertificateFormula()
    {
        var s = V("s"); var p = V("p"); var r = CallLocal("rank", p);
        var rows = All("s", Q(Scanner + "Seen"), All("p", N("Boundary"),
            Imp(CallLocal("Valid", s, p), And(
                Eq(CallLocal("classCount", s, p, V("true")), Conditional(Proj(s, 2),
                    Add(Cast(Num(320)), Mul(Cast(Num(64)), r)), Cast(Num(240)))), And(
                Eq(CallLocal("classCount", s, p, V("false")),
                    Conditional(Proj(s, 2), Cast(Num(0)), Cast(Num(32)))),
                Eq(CallLocal("rankCount", s, p), Conditional(Proj(s, 2),
                    Add(Cast(Num(512)), Mul(Cast(Num(160)), r)), Cast(Num(448)))))))));
        return And(rows, And(Eq(CallLocal("firstCount", V("true")), Cast(Num(28))),
            And(Eq(CallLocal("firstCount", V("false")), Cast(Num(8))),
                Eq(N("firstRank"), Cast(Num(44))))));
    }
    private static Formula ResultFormula()
    {
        var x = Q("PowerSeries.X");
        var left = Mul(Mul(Sub(Num(1), Mul(Num(32), x)),
            Add(Sub(Num(1), Mul(Num(480), x)), Mul(Num(18432), Pow(x, Num(2))))),
            Call("PowerSeries.mk", Fn("n", Q("Nat"), Cast(CallLocal("a", V("n"))))));
        var right = Mul(Mul(Num(4), x), Add(Sub(Num(9), Mul(Num(1120), x)),
            Mul(Num(30720), Pow(x, Num(2)))));
        return Eq(Typed(left, Call("PowerSeries", Q("Int"))), right);
    }

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
