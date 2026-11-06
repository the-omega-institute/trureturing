using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA240513LadderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240513Ladder.";
    private const string Note = "D5/L/RecurrenceComposition/hardinbarker2014a240513";
    private const string NameQuote = "Number of n X 2 0..1 arrays with no element equal to exactly two horizontal and vertical neighbors, with new values 0..1 introduced in row major order.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal two-column binary ladder counts, their recurrence and formal generating series.",
        H("Hardin and Barker's binary ladder formulas"),
        Blocks(
            Paragraph(Text("OEIS A240513, revision 11, NAME: \"" + NameQuote + "\" The entry has no page numbers. Rows and columns are labeled, boundaries are open, and diagonal cells are not neighbors. For a binary alphabet, introduction of new values in row-major order means precisely that the first entry is zero. The value one need not occur.")),
            Describe.Lean(DescribeId.Create("equal-bit"), DeclarationHandle.Create(Prefix + "equalBit"),
                H("The equal-bit indicator"),
                StatementSource.FromAuthor(Disp(EqualBitFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The natural-valued indicator is one for equal bits and zero otherwise. It contributes one for each equal-valued neighbor in the local conditions."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("row"), DeclarationHandle.Create(Prefix + "Row"),
                H("A binary row"),
                StatementSource.FromAuthor(Disp(Eq(V("Row"), Arrow(Call("Fin", D(2)), V("Bool"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A row assigns a bit to each of the two labeled columns. There are four rows and sixteen ordered row-pair states."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("boundary"), DeclarationHandle.Create(Prefix + "Boundary"),
                H("The boundary-row condition"),
                StatementSource.FromAuthor(Disp(BoundaryFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Boundary r s checks row r when s is its only neighboring row. The other column and the adjacent row provide its two possible neighbors."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("interior"), DeclarationHandle.Create(Prefix + "Interior"),
                H("The interior-row condition"),
                StatementSource.FromAuthor(Disp(InteriorFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Interior r s t checks the middle row s between r and t. The sum of its three equal-bit indicators must differ from two at each column."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("step"), DeclarationHandle.Create(Prefix + "step"),
                H("The continuation step"),
                StatementSource.FromAuthor(Disp(StepFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("For an integer-valued function w on row pairs, step w r s sums w s t over all four rows t satisfying Interior r s t. Rows failing that condition contribute zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("v"), DeclarationHandle.Create(Prefix + "v"),
                H("The continuation vectors"),
                StatementSource.FromAuthor(Disp(VectorFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The zero-length continuation checks the terminal boundary row s against r. Each successor applies step to the previous vector, so v k r s counts the legal choices of k further rows with integer values."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a"), DeclarationHandle.Create(Prefix + "a"),
                H("The literal array count"),
                StatementSource.FromAuthor(Disp(CountFormula())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The cell type is Fin n × Fin 2 and each board is a function from this type to Bool. False is zero. The displayed finite-set cardinality is the filter cardinality in a: its local neighbor count adds the equal-valued cell in the other column, the previous row when the row index is positive, and the next row when that row remains in the board. In width two, Fin.rev exchanges the two columns. The existential first-row condition makes a 0 = 0; for every positive height it is exactly A(0,0) = false. In height one the two choices for the other entry are both legal, so a 1 = 2."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-certificate"), DeclarationHandle.Create(Prefix + "finite_certificate"),
                H("The finite continuation identity"),
                StatementSource.FromAuthor(Disp(CertificateFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Here r and s range over binary rows Fin 2 → Bool. The integer continuation vector starts with v 0 r s = 1 when the last row s satisfies its boundary condition against r, and zero otherwise. Its step sums v k s t over the binary rows t for which s satisfies its interior condition against r and t. The equality holds on every ordered row pair. Applying this same linear step propagates the equality to every shift; taking the boundary-weighted total then gives the recurrence in result. The finite equality is checked by kernel reduction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The signed recurrence and formal generating function"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("OEIS A240513, revision 11, first FORMULA: \"Empirical: a(n) = 2*a(n-1) + a(n-2) - a(n-3) - 2*a(n-4) + a(n-5).\" Its second FORMULA, attributed to Colin Barker, is \"Empirical g.f.: x*(2 - x)*(1 - x^2 - 2*x^3) / ((1 - x)*(1 - x - 2*x^2 - x^3 + x^4)).\" The recurrence holds for every natural n at least six, after casting all counts to integers. The series is PowerSeries.mk of these integer coefficients. Its constant coefficient is zero, so it is the source's series beginning at height one. The denominator has constant coefficient one; the asserted identity clears that denominator and requires no convergence assumption.")),
                    Paragraph(Text("An internal state is an ordered pair of binary rows, giving sixteen states without a symmetry quotient. A boundary row compares its two available neighbors, and an interior row compares its three available neighbors. Splitting the finite function space at the first row gives the continuation sum. Induction on the number of remaining rows proves that this sum counts the literal boards, including the first-entry constraint and both end boundaries. The terminal continuation vectors satisfy v5 = 2 v4 + v3 - v2 - 2 v1 + v0 at every state. Linearity propagates this identity to all subsequent vectors. The initial counts 0, 2, 3, 6, 10, 21 and 42 supply the height-six case and the low coefficients. Comparing coefficients of the formal series proves the displayed product identity."))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin240513"), ResolutionKind.Proved)))));

    private static Formula EqualBitFormula()
    {
        var x = V("x"); var y = V("y");
        return All("x", V("Bool"), All("y", V("Bool"),
            Eq(Call("equalBit", x, y), Conditional(Eq(x, y), D(1), D(0)))));
    }

    private static Formula BoundaryFormula()
    {
        var r = V("r"); var s = V("s"); var j = V("j");
        var neighbors = Add(Call("equalBit", App(r, Call("rev", j)), App(r, j)),
            Call("equalBit", App(s, j), App(r, j)));
        return All("r", V("Row"), All("s", V("Row"),
            Seq(Call("Boundary", r, s), Sp, F.Iff, Sp,
                Parenthesized(All("j", Call("Fin", D(2)), Seq(neighbors, Sp, Neq, Sp, D(2)))))));
    }

    private static Formula InteriorFormula()
    {
        var r = V("r"); var s = V("s"); var t = V("t"); var j = V("j");
        var neighbors = Add(Add(Call("equalBit", App(s, Call("rev", j)), App(s, j)),
            Call("equalBit", App(r, j), App(s, j))), Call("equalBit", App(t, j), App(s, j)));
        return All("r", V("Row"), All("s", V("Row"), All("t", V("Row"),
            Seq(Call("Interior", r, s, t), Sp, F.Iff, Sp,
                Parenthesized(All("j", Call("Fin", D(2)), Seq(neighbors, Sp, Neq, Sp, D(2))))))));
    }

    private static Formula StepFormula()
    {
        var w = V("w"); var r = V("r"); var s = V("s"); var t = V("t");
        var sum = Seq(Sum, Underscore, Grp(t, Colon, Sp, V("Row")), Sp,
            Parenthesized(Conditional(Call("Interior", r, s, t), App(w, s, t), D(0))));
        return All("w", Arrow(V("Row"), Arrow(V("Row"), V("Int"))),
            All("r", V("Row"), All("s", V("Row"), Eq(Call("step", w, r, s), sum))));
    }

    private static Formula VectorFormula()
    {
        var k = V("k"); var r = V("r"); var s = V("s");
        return new Formula.Aligned([
            All("r", V("Row"), All("s", V("Row"),
                Eq(Call("v", D(0), r, s), Conditional(Call("Boundary", s, r), D(1), D(0))))),
            All("k", V("Nat"), All("r", V("Row"), All("s", V("Row"),
                Eq(Call("v", Add(k, D(1)), r, s), Call("step", Call("v", k), r, s)))))
        ]);
    }

    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A"); var p = V("p"); var q = V("q");
        var i = V("i");
        var first = Ex("i", Call("Fin", n), AndOf(Eq(Call("val", i), D(0)),
            Eq(App(a, Pair(i, D(0))), V("false"))));
        var neighbors = SetOf("q", Cells(n), AndOf(Adjacent(p, q), Eq(App(a, q), App(a, p))));
        var legal = All("p", Cells(n), Seq(Call("card", neighbors), Sp, Neq, Sp, D(2)));
        var boards = SetOf("A", Arrow(Cells(n), V("Bool")), AndOf(first, legal));
        return All("n", V("Nat"), Eq(Call("a", n), Call("card", boards)));
    }

    private static Formula Adjacent(Formula p, Formula q)
    {
        var pr = Coordinate(p, 1); var pc = Coordinate(p, 2);
        var qr = Coordinate(q, 1); var qc = Coordinate(q, 2);
        var columnStep = OrOf(Eq(pc, Add(qc, D(1))), Eq(qc, Add(pc, D(1))));
        var rowStep = OrOf(Eq(pr, Add(qr, D(1))), Eq(qr, Add(pr, D(1))));
        return OrOf(AndOf(Eq(pr, qr), columnStep), AndOf(Eq(pc, qc), rowStep));
    }

    private static Formula CertificateFormula()
    {
        var r = V("r"); var s = V("s");
        Formula Vector(byte k) => Call("v", D(k), r, s);
        var rhs = Add(Mul(D(2), Vector(4)), Vector(3));
        rhs = Sub(rhs, Vector(2));
        rhs = Sub(rhs, Mul(D(2), Vector(1)));
        rhs = Add(rhs, Vector(0));
        var row = Arrow(Call("Fin", D(2)), V("Bool"));
        return All("r", row, All("s", row, Eq(Vector(5), rhs)));
    }

    private static Formula ResultFormula()
    {
        var n = V("n"); var x = Q("PowerSeries", "X");
        Formula A(Formula k) => Cast(Call("a", k), V("Int"));
        var rhs = Add(Mul(D(2), A(Sub(n, D(1)))), A(Sub(n, D(2))));
        rhs = Sub(rhs, A(Sub(n, D(3))));
        rhs = Sub(rhs, Mul(D(2), A(Sub(n, D(4)))));
        rhs = Add(rhs, A(Sub(n, D(5))));
        var recurrence = All("n", V("Nat"), Imp(Seq(D(6), Sp, Leq, Sp, n), Eq(A(n), rhs)));
        var quartic = Add(Sub(Sub(Sub(D(1), x), Mul(D(2), Pow(x, D(2)))), Pow(x, D(3))),
            Pow(x, D(4)));
        var series = App(Q("PowerSeries", "mk"),
            Parenthesized(Seq(LambdaLower, Sp, V("k"), Colon, Sp, V("Nat"), Sp, Mapsto, Sp, A(V("k")))));
        var numerator = Mul(Mul(x, Parenthesized(Sub(D(2), x))),
            Parenthesized(Sub(Sub(D(1), Pow(x, D(2))), Mul(D(2), Pow(x, D(3))))));
        return AndOf(recurrence,
            Eq(Mul(Mul(Parenthesized(Sub(D(1), x)), Parenthesized(quartic)), series), numerator));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Seq(Operatorname, Grp(V("if")), Sp, Parenthesized(condition), Sp,
            Operatorname, Grp(V("then")), Sp, yes, Sp, Operatorname, Grp(V("else")), Sp, no);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Cells(Formula n) => Seq(Call("Fin", n), Sp, Times, Sp, Call("Fin", D(2)));
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, b);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Coordinate(Formula p, byte i) => Call("val", Seq(p, Dot, D(i)));
    private static Formula Cast(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula SetOf(string name, Formula t, Formula body) =>
        Seq(OpenBrace, V(name), Colon, Sp, t, Sp, Mid, Sp, body, CloseBrace);
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
    private static Formula AndOf(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula OrOf(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
}
