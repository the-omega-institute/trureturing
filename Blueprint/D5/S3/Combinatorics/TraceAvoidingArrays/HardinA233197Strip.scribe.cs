using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233197StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233197Strip.";
    private const string Root = "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233197Strip.";
    private const string ScannerRoot =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233196Strip.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233197");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barker's generating function for eight-colour three-column arrays.",
        H("The literal complementary-pair strip"),
        Blocks(
            Paragraph(Text(
                "OEIS A233197, revision 8, specifies horizontal, vertical and antidiagonal "
                + "bonds, with the main diagonal unconstrained. A bond forbids equal colours "
                + "and colours summing to seven. The first colour is zero. Before any "
                + "2,3,4,5,6 there is a 1; before any 3,4,5 there is a 2; before any 4 "
                + "there is a 3. Earlier means strict row-major order. The imported scanner "
                + "uses exactly these restrictions. Fin.val is the natural value of a Fin "
                + "index; all indices start at zero. Nat.sub is truncated subtraction. "
                + "Nat.div is natural quotient division; Nat.mod is its nonnegative "
                + "remainder. The imported beta uses Fin.ofNat 4, hence reduction modulo "
                + "four, on min(c.val,7-c.val). No quotient occurs in the displayed identity.")),
            Def("row", "Row", "A three-column row",
                Eq(Name("Row"), Arrow(Fin(D(3)), Fin(D(8)))),
                "Rows are functions, with the three distinct column indices 0,1,2."),
            Def("rowlegal", "rowLegal", "Horizontal bonds", RowLegalFormula(),
                "The horizontal bonds are 0--1 and 1--2."),
            Def("bonds", "bonds", "Bonds between consecutive rows", BondsFormula(),
                "There are three vertical and two antidiagonal bonds."),
            Def("count", "a", "The literal filtered finite count", CountFormula(),
                "The filter uses HardinA233196Strip.widthLegal rowLegal bonds directly, "
                + "with the owner's widthInstDecidableLegal instance. The displayed "
                + "predicate unfolds its row, bond and initial widthNormal conditions; "
                + "the initial seen-colour flags are all false. The first-cell "
                + "existential fails at height zero, so a(0)=0.", true),
            Def("pairs", "pairs", "The preceding row's pair labels", PairsFormula(),
                "All three column labels are retained, with fibres {0,7},{1,6},{2,5},{3,4}."),
            Def("compatible", "compatible", "Pair-label bond constraints", CompatibleFormula(),
                "The same three vertical and two antidiagonal inequalities are imposed."),
            Def("valid", "Valid", "Reachable boundary invariant", ValidFormula(),
                "The invariant includes legal horizontal labels and prefix-ordered flags."),
            Def("class", "seenClass", "Five boundary classes", ClassFormula(),
                "Class 0 has not seen colour 2. Classes 1 and 2 have seen 2 but not 3, "
                + "and distinguish equal and unequal outer labels. Classes 3 and 4 have "
                + "seen 3 and make the same outer-label distinction. Class 1 is included "
                + "in the invariant although the initial vector never reaches it."),
            Def("matrix", "T", "The finite transfer matrix", Eq(Name("T"), MatrixFormula()),
                "Both indices have type Fin 5. The fully seen block is [[16,16],[8,40]], "
                + "with characteristic polynomial t^2-56t+512. The not-yet-fully-seen "
                + "sector has eigenvalue 8 and transient zero eigenvalues."),
            Def("classcount", "classCount", "Single-row class counts", ClassCountFormula(),
                "The sum tests all 512 colour rows and their terminal boundary class."),
            Def("firstcount", "firstCount", "Initial class counts", FirstCountFormula(),
                "The first rows (0,1,0),(0,1,7),(0,1,2) give vector [2,0,1,0,0]."),
            Thm("certificate", "finite_certificate", "The finite certificate",
                CertificateFormula(),
                "The rows of T are [0,0,0,2,2], [0,0,0,8,8], [0,0,8,4,16], "
                + "[0,0,0,16,16], [0,0,0,8,40]. The vector identity removes the "
                + "transient zero eigenspace before applying the cubic relation."),
            Resolution("result", "result", "Barker's generating function", ResultFormula(),
                "Let w(n)=Matrix.mulVec (T^n) 1. The imported width_counting_bridge "
                + "and induction through the finite class counts give a(n+1)=2w(n)(0) "
                + "+w(n)(2). This is iteration of the normalized one-step class map, "
                + "the Function.Semiconj.iterate_right pattern. The finite vector relation "
                + "and TransferMatrix.scalarRelationShift give a(n+5)=64a(n+4)-960a(n+3) "
                + "+4096a(n+2). The first four counts are 3,36,1440,62720. Coefficient "
                + "comparison, including a(0)=0, proves the identity. Natural counts are "
                + "cast to Int before forming the series. This is a formal combinatorial "
                + "identity; no assertion of a physical realization is required."))));

    private static DocumentBlock Def(string id, string name, string title, Formula formula,
        string prose, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Thm(string id, string name, string title, Formula formula,
        string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Resolution(string id, string name, string title,
        Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233197"),
                ResolutionKind.Proved));

    private static Formula Boundary() => Arrow(Fin(D(3)), Fin(D(4)));
    private static Formula Bond(Formula x, Formula y) =>
        And(Ne(x, y), Ne(Add(Val(x), Val(y)), D(7)));
    private static Formula RowLegalFormula()
    {
        var c = V("c");
        return All("c", Name("Row"), Eq(Call("rowLegal", c),
            And(Bond(At(c, Index(0)), At(c, Index(1))),
                Bond(At(c, Index(1)), At(c, Index(2))))));
    }
    private static Formula BondsFormula()
    {
        var c = V("c"); var d = V("d"); var j = V("j");
        return All("c", Name("Row"), All("d", Name("Row"), Eq(Call("bonds", c, d),
            And(All("j", Fin(D(3)), Bond(At(c, j), At(d, j))),
                And(Bond(At(c, Index(1)), At(d, Index(0))),
                    Bond(At(c, Index(2)), At(d, Index(1))))))));
    }
    private static Formula PairsFormula()
    {
        var c = V("c"); var j = V("j");
        return All("c", Name("Row"), Eq(Call("pairs", c),
            Fn("j", Fin(D(3)), Call("beta", At(c, j)))));
    }
    private static Formula CompatibleFormula()
    {
        var p = V("p"); var c = V("c"); var j = V("j");
        return All("p", Boundary(), All("c", Name("Row"), Eq(Call("compatible", p, c),
            And(All("j", Fin(D(3)), Ne(At(p, j), Call("beta", At(c, j)))),
                And(Ne(At(p, Index(1)), Call("beta", At(c, Index(0)))),
                    Ne(At(p, Index(2)), Call("beta", At(c, Index(1)))))))));
    }
    private static Formula ValidFormula()
    {
        var s = V("s"); var p = V("p"); var j = V("j");
        Formula Below(byte d) => All("j", Fin(D(3)), Lt(Val(At(p, j)), D(d)));
        return All("s", Name("Seen"), All("p", Boundary(), Eq(Call("Valid", s, p),
            And(Eq(First(s), Q("Bool.true")),
                And(Ne(At(p, Index(0)), At(p, Index(1))),
                    And(Ne(At(p, Index(1)), At(p, Index(2))),
                        And(Imp(Eq(Second(s), Q("Bool.false")), Below(2)),
                            And(Imp(Eq(Third(s), Q("Bool.false")), Below(3)),
                                Imp(Eq(Third(s), Q("Bool.true")),
                                    Eq(Second(s), Q("Bool.true")))))))))));
    }
    private static Formula ClassFormula()
    {
        var s = V("s"); var p = V("p");
        var eq = Eq(At(p, Index(0)), At(p, Index(2)));
        Formula C(byte n) => Typed(D(n), Fin(D(5)));
        return All("s", Name("Seen"), All("p", Boundary(), Eq(Call("seenClass", s, p),
            Conditional(Second(s), Conditional(Third(s), Conditional(eq, C(3), C(4)),
                Conditional(eq, C(1), C(2))), C(0)))));
    }
    private static Formula MatrixFormula() => Vector(
        Vector(Z(0), Z(0), Z(0), Z(2), Z(2)),
        Vector(Z(0), Z(0), Z(0), Z(8), Z(8)),
        Vector(Z(0), Z(0), Z(8), Z(4), Z(16)),
        Vector(Z(0), Z(0), Z(0), Z(16), Z(16)),
        Vector(Z(0), Z(0), Z(0), Z(8), Z(40)));
    private static Formula InitialVector() => Vector(Z(2), Z(0), Z(1), Z(0), Z(0));
    private static Formula CertificateFormula()
    {
        var s = V("s"); var p = V("p"); var b = V("b"); var j = V("j");
        Formula W(Formula n) => At(Q("Matrix.mulVec"), Power(Name("T"), n),
            Typed(D(1), Arrow(Fin(D(5)), Q("Int"))));
        var counts = All("s", Name("Seen"), All("p", Boundary(),
            Imp(Call("Valid", s, p), All("b", Fin(D(5)),
                Eq(Call("classCount", s, p, b),
                    At(Name("T"), Call("seenClass", s, p), b))))));
        var first = All("b", Fin(D(5)), Eq(Call("firstCount", b), At(InitialVector(), b)));
        var vector = Eq(W(Add(D(1), D(3))), SumOver("j", Fin(D(3)),
            At(Q("HSMul.hSMul"), At(Vector(Z(4096), new Formula.Negate(Z(960)), Z(64)), j),
                W(Add(D(1), Val(j))))));
        return And(counts, And(first, vector));
    }
    private static Formula ResultFormula()
    {
        var ps = At(Q("PowerSeries"), Q("Int"));
        var x = Typed(Q("PowerSeries.X"), ps);
        Formula N(long n) => Typed(new Formula.Number(n), ps);
        var series = At(Q("PowerSeries.mk"), Fn("n", NatType(),
            Typed(At(Q("Nat.cast"), Call("a", V("n"))), Q("Int"))));
        var left = Mul(Mul(Sub(N(1), Mul(N(8), x)),
            Add(Sub(N(1), Mul(N(56), x)), Mul(N(512), Power(x, D(2))))), series);
        var right = Mul(x, Sub(Add(Sub(N(3), Mul(N(156), x)),
            Mul(N(2016), Power(x, D(2)))), Mul(N(7168), Power(x, D(3)))));
        return Eq(left, right);
    }

    private static Formula ArrayConditions(Formula n, Formula a)
    {
        var i = V("i"); var j = V("j"); var r = V("r"); var k = V("k");
        Formula Cell(Formula row, Formula column) => At(a, Pair(row, column));
        Formula Earlier(byte colour) => Ex("r", Fin(n), Ex("k", Fin(D(3)),
            And(Or(Lt(r, i), And(Eq(r, i), Lt(k, j))),
                Eq(Cell(r, k), Colour(colour)))));
        var first = Ex("i", Fin(n), And(Eq(Val(i), D(0)),
            Eq(Cell(i, Index(0)), Colour(0))));
        var rows = All("i", Fin(n),
            And(Bond(Cell(i, Index(0)), Cell(i, Index(1))),
                Bond(Cell(i, Index(1)), Cell(i, Index(2)))));
        var next = Typed(At(Q("Fin.mk"), Add(Val(i), D(1)), V("h")), Fin(n));
        var edges = All("i", Fin(n), All("h", Lt(Add(Val(i), D(1)), n),
            And(All("j", Fin(D(3)), Bond(Cell(i, j), Cell(next, j))),
                And(Bond(Cell(i, Index(1)), Cell(next, Index(0))),
                    Bond(Cell(i, Index(2)), Cell(next, Index(1)))))));
        var cell = Cell(i, j);
        var norm = All("i", Fin(n), All("j", Fin(D(3)),
            And(Imp(Or(Eq(cell, Colour(2)), Or(Eq(cell, Colour(3)),
                    Or(Eq(cell, Colour(4)), Or(Eq(cell, Colour(5)), Eq(cell, Colour(6)))))),
                    Earlier(1)),
                And(Imp(Or(Eq(cell, Colour(3)),
                        Or(Eq(cell, Colour(4)), Eq(cell, Colour(5)))), Earlier(2)),
                    Imp(Eq(cell, Colour(4)), Earlier(3))))));
        return And(first, And(rows, And(edges, norm)));
    }
    private static Formula CountFormula()
    {
        var n = V("n"); var arrays = Arrow(Product(Fin(n), Fin(D(3))), Fin(D(8)));
        return All("n", NatType(), Eq(Call("a", n), At(Q("Finset.card"),
            At(Q("Finset.filter"), Fn("A", arrays, ArrayConditions(n, V("A"))),
                Typed(Q("Finset.univ"), At(Q("Finset"), arrays))))));
    }
    private static Formula ClassCountFormula()
    {
        var s = V("s"); var p = V("p"); var b = V("b"); var c = V("c");
        var condition = And(Call("rowLegal", c), And(Call("compatible", p, c),
            And(Call("good", s, c),
                Eq(Call("seenClass", Call("finish", s, c), Call("pairs", c)), b))));
        return All("s", Name("Seen"), All("p", Boundary(),
            All("b", Fin(D(5)), Eq(Call("classCount", s, p, b),
                SumOver("c", Name("Row"), Conditional(condition, Z(1), Z(0)))))));
    }
    private static Formula FirstCountFormula()
    {
        var b = V("b"); var c = V("c");
        var condition = And(Eq(At(c, Index(0)), Colour(0)), And(Call("rowLegal", c),
            And(Call("good", Initial(), c),
                Eq(Call("seenClass", Call("finish", Initial(), c), Call("pairs", c)), b))));
        return All("b", Fin(D(5)), Eq(Call("firstCount", b),
            SumOver("c", Name("Row"), Conditional(condition, Z(1), Z(0)))));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { Seq(Operatorname, Grp(V(part))) }
            : new[] { Dot, Seq(Operatorname, Grp(V(part))) }).ToArray());
    private static Formula Name(string name) => Q(
        name is "Seen" or "beta" or "good" or "finish" or "widthNormal"
            ? ScannerRoot + name : Root + name);
    private static Formula Call(string name, params Formula[] args) => At(Name(name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula NatType() => Q("Nat");
    private static Formula Fin(Formula n) => At(Q("Fin"), n);
    private static Formula Typed(Formula f, Formula type) =>
        Parenthesized(Seq(f, Colon, Sp, type));
    private static Formula Colour(byte d) => Typed(D(d), Fin(D(8)));
    private static Formula Index(byte d) => Typed(D(d), Fin(D(3)));
    private static Formula Z(long n) => Typed(new Formula.Number(n), Q("Int"));
    private static Formula First(Formula s) => At(Q("Prod.fst"), s);
    private static Formula Second(Formula s) => First(At(Q("Prod.snd"), s));
    private static Formula Third(Formula s) => At(Q("Prod.snd"), At(Q("Prod.snd"), s));
    private static Formula Val(Formula f) => At(Q("Fin.val"), f);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) =>
        Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Triple(Formula a, Formula b, Formula c) => Pair(a, Pair(b, c));
    private static Formula Initial() => Triple(Q("Bool.false"), Q("Bool.false"), Q("Bool.false"));
    private static Formula Vector(params Formula[] entries) => entries.Reverse().Aggregate(
        Q("Matrix.vecEmpty"), (tail, head) => At(Q("Matrix.vecCons"), head, tail));
    private static Formula Arrow(Formula a, Formula b) =>
        new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) =>
        new Formula.Power(Parenthesized(a), Parenthesized(b));
    private static Formula Bound(string n, Formula t) => Parenthesized(Seq(V(n), Colon, Sp, t));
    private static Formula All(string n, Formula t, Formula body) =>
        Seq(Forall, Sp, Bound(n, t), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string n, Formula t, Formula body) =>
        Seq(Exists, Sp, Bound(n, t), Comma, Sp, Parenthesized(body));
    private static Formula Fn(string n, Formula t, Formula body) =>
        Parenthesized(Seq(Bound(n, t), Sp, Mapsto, Sp, body));
    private static Formula Conditional(Formula p, Formula y, Formula n) => Parenthesized(
        Seq(Q("if"), Sp, Parenthesized(p), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));
    private static Formula SumOver(string n, Formula t, Formula body) =>
        Seq(Sum, Underscore, Grp(Bound(n, t)), Sp, Parenthesized(body));
}
