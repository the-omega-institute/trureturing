using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA228502KingsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA228502Kings.";
    private const string Note = "D5/L/RecurrenceComposition/hardinbarker2013a228502";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Corner-occupied configurations of non-attacking kings on four-column strips.",
        H("Hardin and Barker's four-column king configurations"),
        Blocks(
            Paragraph(Text("OEIS A228502, revision 12, NAME: \"Number of n X 4 binary arrays with top left value 1 and no two ones adjacent horizontally, vertically, diagonally or antidiagonally.\" Rows and columns are labeled and the boundary is open. True denotes an occupied cell. The distance Nat.dist is absolute difference on natural numbers, and king adjacency is exactly maximum coordinate distance one. The projections p.1 and p.2 are row and column indices; val is the natural-valued projection from Fin.")),
            Describe.Lean(DescribeId.Create("a"), DeclarationHandle.Create(Prefix + "a"),
                H("The literal filtered board count"),
                StatementSource.FromAuthor(Disp(CountFormula())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The filter ranges over every function from Fin n × Fin 4 to Bool. Its first conjunct requires an occupied cell in column zero of row zero. The existential row index makes a 0 = 0, since Fin 0 has no elements. For positive n it is exactly A(0,0) = true. Its second conjunct forbids two true values on distinct cells at king distance one, including diagonal contacts. No modular arithmetic or division is used. Natural subtraction in the recurrence indices is truncated subtraction; all subtraction between counts is performed after casting to integers."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("row"), DeclarationHandle.Create(Prefix + "Row"),
                H("Binary rows"),
                StatementSource.FromAuthor(Disp(Eq(V("Row"), Arrow(Call("Fin", D(4)), V("Bool"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A row assigns a Boolean to each of four columns. There are sixteen such functions. The row representation is used to calculate the board count."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("valid-row"), DeclarationHandle.Create(Prefix + "ValidRow"),
                H("Exclusion within one row"),
                StatementSource.FromAuthor(Disp(RowPredicateFormula(false))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A valid row has no occupied pair in consecutive columns. Exactly eight rows are valid: the empty row, the four singleton rows, and the three pairs of zero-based columns {0,2}, {0,3} and {1,3}."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("compatible"), DeclarationHandle.Create(Prefix + "Compatible"),
                H("Exclusion between consecutive rows"),
                StatementSource.FromAuthor(Disp(RowPredicateFormula(true))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Compatibility forbids occupied cells in consecutive rows whose column distance is zero or one. This accounts for vertical and both diagonal contacts. Rows at distance at least two impose no constraints on each other."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("step"), DeclarationHandle.Create(Prefix + "step"),
                H("The linear continuation operator"),
                StatementSource.FromAuthor(Disp(StepFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("For a valid current row r, step w r sums w s over compatible next rows s. An invalid current row contributes zero. This is an integer-linear operator on functions of the sixteen binary rows."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("v"), DeclarationHandle.Create(Prefix + "v"),
                H("Continuation counts"),
                StatementSource.FromAuthor(Disp(VectorFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The initial vector is the indicator of valid rows. The value v k r counts the ways to append k rows after r while keeping the whole strip free of attacking occupied cells. An invalid row r always contributes zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-certificate"), DeclarationHandle.Create(Prefix + "finite_certificate"),
                H("The four-step continuation identity"),
                StatementSource.FromAuthor(Disp(CertificateFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The displayed equality holds for every one of the sixteen binary rows. Applying the same linear continuation operator propagates it to every shift. The invalid rows contribute zero on both sides."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The recurrence and formal generating series"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("OEIS A228502, revision 12, first FORMULA: \"Empirical: a(n) = 2*a(n-1) + 7*a(n-2) - 2*a(n-3) - 3*a(n-4).\" Its second FORMULA is \"Empirical g.f.: x*(1 - x)*(3 + 2*x) / (1 - 2*x - 7*x^2 + 2*x^3 + 3*x^4).\" The generating function is attributed to Colin Barker. The recurrence holds at every height n at least five. PowerSeries.mk assigns the integer count a n to coefficient n; since a 0 = 0, this series begins at degree one. The formal product identity clears a denominator with constant coefficient one and needs no convergence hypothesis.")),
                    Paragraph(Text("Splitting a board into its first row and its remaining rows preserves the literal king-adjacency predicate: only the first two rows can interact across the split. The equivalence between functions on the cell product and functions of rows, followed by the first-row decomposition of finite function spaces, expresses the count as the sum of v k r over rows r with r 0 = true, at height k + 1. Induction on k proves this equality for every height, including height one. The finite four-step identity and linearity yield the recurrence. The initial counts at heights zero through four are 0, 3, 5, 29 and 87; coefficient comparison with these initial values proves the formal product identity."))),
                DescribeRole.Theorem))));

    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A"); var p = V("p"); var q = V("q"); var i = V("i");
        var corner = Ex("i", Call("Fin", n), AndOf(Eq(Call("val", i), D(0)),
            Eq(App(a, Pair(i, D(0))), V("true"))));
        var adjacency = Eq(Call("max", Call("dist", Coordinate(p, 1), Coordinate(q, 1)),
            Call("dist", Coordinate(p, 2), Coordinate(q, 2))), D(1));
        var notBoth = Seq(Neg, Sp, Parenthesized(AndOf(Eq(App(a, p), V("true")),
            Eq(App(a, q), V("true")))));
        var safe = All("p", Cells(n), All("q", Cells(n),
            Imp(Seq(p, Sp, Neq, Sp, q), Imp(adjacency, notBoth))));
        var predicate = Lambda("A", Arrow(Cells(n), V("Bool")), AndOf(corner, safe));
        var filtered = App(Q("Finset", "filter"), predicate, Q("Finset", "univ"));
        return All("n", V("Nat"), Eq(Call("a", n), App(Q("Finset", "card"), filtered)));
    }

    private static Formula RowPredicateFormula(bool compatible)
    {
        var r = V("r"); var s = V("s"); var j = V("j"); var k = V("k");
        var distance = Call("dist", Call("val", j), Call("val", k));
        var condition = compatible ? Seq(distance, Sp, Leq, Sp, D(1)) : Eq(distance, D(1));
        var body = All("j", Call("Fin", D(4)), All("k", Call("Fin", D(4)),
            Imp(condition, Imp(Eq(App(r, j), V("true")), Eq(App(compatible ? s : r, k), V("false"))))));
        var equation = Seq(compatible ? Call("Compatible", r, s) : Call("ValidRow", r), Sp, F.Iff, Sp,
            Parenthesized(body));
        return All("r", V("Row"), compatible ? All("s", V("Row"), equation) : equation);
    }

    private static Formula StepFormula()
    {
        var w = V("w"); var r = V("r"); var s = V("s");
        var sum = Seq(Sum, Underscore, Grp(s, Colon, Sp, V("Row")), Sp,
            Parenthesized(Conditional(Call("Compatible", r, s), App(w, s), D(0))));
        return All("w", Arrow(V("Row"), V("Int")), All("r", V("Row"),
            Eq(Call("step", w, r), Conditional(Call("ValidRow", r), sum, D(0)))));
    }

    private static Formula VectorFormula()
    {
        var k = V("k"); var r = V("r");
        return new Formula.Aligned([
            All("r", V("Row"), Eq(Call("v", D(0), r), Conditional(Call("ValidRow", r), D(1), D(0)))),
            All("k", V("Nat"), All("r", V("Row"),
                Eq(Call("v", Add(k, D(1)), r), Call("step", Call("v", k), r))))
        ]);
    }

    private static Formula CertificateFormula()
    {
        var r = V("r");
        Formula Vector(byte k) => Call("v", D(k), r);
        var rhs = Sub(Sub(Add(Mul(D(2), Vector(3)), Mul(D(7), Vector(2))),
            Mul(D(2), Vector(1))), Mul(D(3), Vector(0)));
        return All("r", V("Row"), Eq(Vector(4), rhs));
    }

    private static Formula ResultFormula()
    {
        var n = V("n"); var x = Q("PowerSeries", "X");
        Formula A(Formula k) => Cast(Call("a", k), V("Int"));
        var rhs = Sub(Sub(Add(Mul(D(2), A(Sub(n, D(1)))), Mul(D(7), A(Sub(n, D(2))))),
            Mul(D(2), A(Sub(n, D(3))))), Mul(D(3), A(Sub(n, D(4)))));
        var recurrence = All("n", V("Nat"), Imp(Seq(D(5), Sp, Leq, Sp, n), Eq(A(n), rhs)));
        var denominator = Add(Add(Sub(Sub(D(1), Mul(D(2), x)), Mul(D(7), Pow(x, D(2)))),
            Mul(D(2), Pow(x, D(3)))), Mul(D(3), Pow(x, D(4))));
        var series = App(Q("PowerSeries", "mk"), Lambda("n", V("Nat"), A(n)));
        var numerator = Mul(Mul(x, Parenthesized(Sub(D(1), x))), Parenthesized(Add(D(3), Mul(D(2), x))));
        return AndOf(recurrence, Eq(Mul(Parenthesized(denominator), series), numerator));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Cells(Formula n) => Seq(Call("Fin", n), Sp, Times, Sp, Call("Fin", D(4)));
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, b);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Coordinate(Formula p, byte i) => Call("val", Seq(p, Dot, D(i)));
    private static Formula Cast(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula All(string name, Formula t, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, t, Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula t, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, t, Comma, Sp, Parenthesized(body));
    private static Formula Lambda(string name, Formula t, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, V(name), Colon, Sp, t, Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula AndOf(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Seq(Operatorname, Grp(V("if")), Sp, Parenthesized(condition), Sp,
            Operatorname, Grp(V("then")), Sp, yes, Sp, Operatorname, Grp(V("else")), Sp, no);
}
