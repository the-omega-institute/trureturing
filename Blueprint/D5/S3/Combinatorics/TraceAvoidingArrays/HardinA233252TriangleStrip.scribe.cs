using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233252TriangleStripDocument : IScribeDocumentDefinition
{
    private const string Root =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233252TriangleStrip.";
    private const string Owner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.";
    private const string Scanner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.";
    private const string RowOwner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233125SquareStrip.";
    private const string BoundaryOwner =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip.";
    private const string Beta =
        "D5.S3.Observer.Separation.BooleanRankThreeK4.beta";
    private const string Gid =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233252TriangleStrip.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233252");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barker's recurrence, generating function, and closed form for the literal normalized four-column strip.",
        H("Six-colour horizontal and antidiagonal exclusion"),
        Blocks(
            Paragraph(Text(
                "OEIS A233252 revision 8 defines n by 4 arrays with horizontal and "
                + "antidiagonal exclusions. The first cell is zero. In row-major order, "
                + "each 2, 3 or 4 has an earlier 1, and each 3 an earlier 2. The coefficient "
                + "at index zero is zero. The three complementary-pair labels are the fibres "
                + "of the existing BooleanRankThreeK4.beta.")),
            Paragraph(Text(
                "Rows and horizontal exclusions use HardinA233125SquareStrip.Row and "
                + "HardinA233125SquareStrip.rowLegal. A row contains four colours; consecutive "
                + "colours are unequal and are not complementary.")),
            Paragraph(Text(
                "Reachable boundary states use HardinA233124SquareStrip.Valid: the first "
                + "scanner flag is true, adjacent boundary labels are distinct, and label two "
                + "is absent before colour two is seen. HardinA233124SquareStrip.boundaryClass "
                + "assigns class zero before colour two appears; after it appears, classes one "
                + "and two distinguish equal and unequal endpoints.")),
            Entry("boundarytype", "Boundary", "Boundary label type",
                Eq(Name(Root + "Boundary"), Arrow(Fin(3), Fin(3))),
                "The antidiagonal boundary carries three complementary-pair labels."),
            Entry("count", "a", "The literal finite count", Count(),
                "The owner widthLegal predicate combines the first-cell, horizontal, "
                + "antidiagonal, and row-major scanner clauses. The empty-height filter is empty.", true),
            Entry("pairs", "pairs", "Boundary pair labels", Pairs(),
                "The boundary records the labels at columns one, two, and three."),
            Entry("compatible", "compatible", "Antidiagonal label compatibility", Compatible(),
                "Each preceding boundary label excludes the corresponding next-row colour label."),
            Entry("transfer", "transfer", "Class transition matrix", Transfer(),
                "Rows are source classes and columns are destination classes."),
            Entry("classcount", "classCount", "One-row class counts", ClassCount(),
                "The integer sum counts legal rows by their destination boundary class."),
            Entry("firstcount", "firstCount", "First-row class counts", FirstCount(),
                "The first cell is fixed to zero and both scanner flags start false."),
            Describe.Lean(DescribeId.Create("certificate"),
                DeclarationHandle.Create(Gid + "finite_certificate"), H("Finite certificate"),
                StatementSource.FromAuthor(Disp(Certificate())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The exact scanner-fibre calculation gives the displayed transition "
                    + "matrix and first-row vector. HardinA233125SquareStrip.label_sum "
                    + "reindexes the four-label sum as four successive sums over Fin 3."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"),
                DeclarationHandle.Create(Gid + "result"), H("Barker's three identities"),
                StatementSource.FromAuthor(Disp(Result())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The finite certificate and the width-generic counting bridge reduce every "
                    + "height to the three-state transfer. Its spectrum has factors 1-16X "
                    + "and 1-144X, yielding the recurrence and exact integer power-series "
                    + "identity. The same transfer induction gives Barker's closed form."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233252"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, bool literature = false) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Gid + name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        literature ? AssessedProvenance.FromLiterature(Source)
            : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Count()
    {
        var n = V("n"); var a = V("A"); var i = V("i"); var j = V("j");
        var arrays = Arrow(Product(Call("Fin", n), Fin(4)), Fin(6));
        var first = Ex("i", Call("Fin", n), And(Eq(Val(i), D(0)),
            Eq(At(a, Pair(i, Typed(D(0), Fin(4)))), Typed(D(0), Fin(6)))));
        var horizontal = All("i", Call("Fin", n), Call(RowOwner + "rowLegal",
            Fn("j", Fin(4), At(a, Pair(i, j)))));
        var next = Call("Fin.mk", Add(Val(i), D(1)), V("h"));
        var upper = At(a, Pair(i, Call("Fin.succ", j)));
        var lower = At(a, Pair(next, Call("Fin.castSucc", j)));
        var anti = All("i", Call("Fin", n), All("h", Lt(Add(Val(i), D(1)), n),
            All("j", Fin(3), And(Ne(upper, lower),
                Ne(Add(Val(upper), Val(lower)), D(5))))));
        var normal = Call(Owner + "widthNormal", Pair(Name("Bool.false"), Name("Bool.false")),
            Fn("i", Call("Fin", n), Fn("j", Fin(4), At(a, Pair(i, j)))));
        var predicate = Fn("A", arrays, And(first, And(horizontal, And(anti, normal))));
        var universe = Typed(Name("Finset.univ"), Call("Finset", arrays));
        return All("n", Name("Nat"), Eq(Call(Root + "a", n),
            Call("Finset.card", Call("Finset.filter", predicate, universe))));
    }

    private static Formula BoundaryType() => Name(Root + "Boundary");

    private static Formula Pairs()
    {
        var c = V("c"); var j = V("j");
        return All("c", Name(RowOwner + "Row"), Eq(Call(Root + "pairs", c),
            Fn("j", Fin(3), Call(Beta, At(c, Call("Fin.succ", j))))));
    }

    private static Formula Compatible()
    {
        var p = V("p"); var c = V("c"); var j = V("j");
        return All("p", BoundaryType(), All("c", Name(RowOwner + "Row"),
            Eq(Call(Root + "compatible", p, c), All("j", Fin(3),
                Ne(At(p, j), Call(Beta, At(c, Call("Fin.castSucc", j))))))));
    }

    private static Formula Transfer()
    {
        var table = Vector(Vector(D(1, 6), D(3, 2), D(4, 0)),
            Vector(D(0), D(8, 0), D(8, 0)), Vector(D(0), D(6, 4), D(6, 4)));
        return All("i", Fin(3), All("k", Fin(3),
            Eq(Call(Root + "transfer", V("i"), V("k")), At(table, V("i"), V("k")))));
    }

    private static Formula ClassCondition()
    {
        var s = V("s"); var p = V("p"); var k = V("k"); var c = V("c");
        return And(Call(RowOwner + "rowLegal", c), And(Call(Root + "compatible", p, c),
            And(Call(Scanner + "good", s, c), Eq(Call(BoundaryOwner + "boundaryClass",
                Call(Scanner + "finish", s, c), Call(Root + "pairs", c)), k))));
    }

    private static Formula ClassCount()
    {
        return All("s", Name(Scanner + "Seen"), All("p", BoundaryType(),
            All("k", Fin(3), Eq(Call(Root + "classCount", V("s"), V("p"), V("k")),
                SumOver("c", Name(RowOwner + "Row"),
                    Typed(Conditional(ClassCondition(), D(1), D(0)), Name("Int")))))));
    }

    private static Formula FirstCount()
    {
        var c = V("c"); var k = V("k"); var flags = Pair(Name("Bool.false"), Name("Bool.false"));
        var condition = And(Eq(At(c, Typed(D(0), Fin(4))), Typed(D(0), Fin(6))),
            And(Call(RowOwner + "rowLegal", c), And(Call(Scanner + "good", flags, c),
                Eq(Call(BoundaryOwner + "boundaryClass", Call(Scanner + "finish", flags, c),
                    Call(Root + "pairs", c)), k))));
        return All("k", Fin(3), Eq(Call(Root + "firstCount", k),
            SumOver("c", Name(RowOwner + "Row"),
                Typed(Conditional(condition, D(1), D(0)), Name("Int")))));
    }

    private static Formula Certificate()
    {
        var s = V("s"); var p = V("p"); var k = V("k");
        var rows = All("s", Name(Scanner + "Seen"), All("p", BoundaryType(),
            Imp(Call(BoundaryOwner + "Valid", s, p), All("k", Fin(3),
                Eq(Call(Root + "classCount", s, p, k),
                    Call(Root + "transfer", Call(BoundaryOwner + "boundaryClass", s, p), k))))));
        return And(rows, All("k", Fin(3), Eq(Call(Root + "firstCount", k),
            At(Vector(D(4), D(2), D(4)), k))));
    }

    private static Formula Result()
    {
        var x = Typed(Name("PowerSeries.X"), Call("PowerSeries", Name("Int")));
        var series = Call("PowerSeries.mk", Fn("n", Name("Nat"),
            Typed(Call(Root + "a", V("n")), Name("Int"))));
        var recurrence = All("n", Name("Nat"), Imp(Le(D(1), V("n")),
            Eq(Typed(Call(Root + "a", Add(V("n"), D(2))), Name("Int")),
                Sub(Mul(D(1, 6, 0), Typed(Call(Root + "a", Add(V("n"), D(1))), Name("Int"))),
                    Mul(D(2, 3, 0, 4), Typed(Call(Root + "a", V("n")), Name("Int")))))));
        var gf = Eq(Mul(Mul(Sub(D(1), Mul(D(1, 6), x)), Sub(D(1), Mul(D(1, 4, 4), x))), series),
            Mul(Mul(D(2), x), Sub(D(5), Mul(D(2, 0, 8), x))));
        var closed = All("n", Name("Nat"), Eq(
            Mul(D(9), Typed(Call(Root + "a", Add(V("n"), D(1))), Name("Int"))),
            Mul(Pow(Typed(D(2), Name("Int")), Add(Mul(D(4), V("n")), D(1))),
                Add(Mul(D(4), Pow(Typed(D(9), Name("Int")), Add(V("n"), D(1)))), D(9)))));
        return And(recurrence, And(gf, closed));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(
        name.Split('.').SelectMany((p, i) =>
            (i == 0 ? Array.Empty<Formula>() : new Formula[] { Dot }).Append(
                Seq(Operatorname, Grp(V(p))))).ToArray());
    private static Formula Call(string name, params Formula[] args) => At(Name(name), args);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula type) =>
        Parenthesized(Seq(f, Colon, Sp, type));
    private static Formula Fin(byte k) => Call("Fin", D(k));
    private static Formula Val(Formula f) => Call("Fin.val", f);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Pair(Formula a, Formula b) =>
        Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Vector(params Formula[] entries) => Seq(
        new Formula[] { Bang, OpenBracket }.Concat(entries.SelectMany((f, i) =>
            i == 0 ? new[] { f } : new[] { Comma, Sp, f }))
            .Append(CloseBracket).ToArray());
    private static Formula Conditional(Formula test, Formula yes, Formula no) =>
        Parenthesized(Seq(Name("if"), Sp, Parenthesized(test), Sp, Name("then"), Sp,
            Parenthesized(yes), Sp, Name("else"), Sp, Parenthesized(no)));
    private static Formula SumOver(string n, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(n), Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Pow(Formula a, Formula b) =>
        new Formula.Power(Parenthesized(a), Parenthesized(b));
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(n), type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string n, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(n), type), Comma, Sp, Parenthesized(body));
    private static Formula Fn(string n, Formula type, Formula body) =>
        Parenthesized(Seq(Typed(V(n), type), Sp, Mapsto, Sp, Parenthesized(body)));
}
