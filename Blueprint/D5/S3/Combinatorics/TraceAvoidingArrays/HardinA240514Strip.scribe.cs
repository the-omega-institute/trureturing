using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA240514StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.";
    private const string Note = "D5/L/RecurrenceComposition/hardin2014a240514";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal three-column binary strip count and Hardin's order-twenty recurrence.",
        H("Hardin's three-column binary strips"),
        Blocks(
            Paragraph(Text("OEIS A240514, revision 6, NAME: \"Number of nX3 0..1 arrays with no element equal to exactly two horizontal and vertical neighbors, with new values 0..1 introduced in row major order.\" The entry has no page numbers. Rows and columns are labeled. All four orthogonal neighbors are counted when in the board; the boundaries are open and there are no diagonals. For a binary alphabet the row-major introduction convention is equivalent to a false first entry. The value true need not occur.")),
            Describe.Lean(DescribeId.Create("row"), DeclarationHandle.Create(Prefix + "Row"),
                H("A three-bit row"),
                StatementSource.FromAuthor(Disp(Eq(V("Row"), Arrow(Call("Fin", D(3)), V("Bool"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A row has three labeled columns. Eight rows give sixty-four ordered row pairs."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("horizontal"), DeclarationHandle.Create(Prefix + "horizontal"),
                H("Horizontal neighbors"),
                StatementSource.FromAuthor(Disp(HorizontalFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The two conditional indicators count precisely the left and right neighbors that remain within the three columns. The equalBit indicator is the public indicator from HardinA240513Ladder: it is one for equal bits and zero otherwise."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("boundary"), DeclarationHandle.Create(Prefix + "Boundary"),
                H("An end row"),
                StatementSource.FromAuthor(Disp(BoundaryFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Boundary r s checks the horizontal neighbors of row r and its single adjacent row s."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("interior"), DeclarationHandle.Create(Prefix + "Interior"),
                H("An interior row"),
                StatementSource.FromAuthor(Disp(InteriorFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Interior r s t checks row s between r and t. The middle column can have four neighbors, and either outer column can have three."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a"), DeclarationHandle.Create(Prefix + "a"),
                H("The literal filtered count"),
                StatementSource.FromAuthor(Disp(CountFormula())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The set in this cardinality is the filter of every function from Fin n × Fin 3 to Bool. The displayed predicate expands the local board condition: horizontal neighbors and in-bounds preceding and succeeding rows contribute their equal-bit indicators. The first-row existential requires A(0,0) = false at every positive height; it makes the empty-board count zero. The first six positive counts are 3, 6, 10, 28, 73 and 196."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("step"), DeclarationHandle.Create(Prefix + "step"),
                H("The continuation operator"),
                StatementSource.FromAuthor(Disp(StepFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Each successor sums over all eight choices for the next row t. Its coefficient is one precisely when the middle row satisfies the local condition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("v"), DeclarationHandle.Create(Prefix + "v"),
                H("Continuation vectors"),
                StatementSource.FromAuthor(Disp(VectorFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The terminal vector checks the final row boundary. The vector v k counts continuations by k further rows after an ordered initial row pair."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-certificate"), DeclarationHandle.Create(Prefix + "finite_certificate"),
                H("The finite vector identity"),
                StatementSource.FromAuthor(Disp(CertificateFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The identity holds on all sixty-four ordered pairs of three-bit rows. An integer table for continuation lengths zero through twenty is checked against the terminal boundary and every transfer step by kernel reduction. The displayed relation is checked on that table. Applying the linear continuation operator propagates it to every later length."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The signed recurrence"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The FORMULA field of OEIS A240514, revision 6, labels this twenty-term recurrence Empirical. All counts are cast from natural numbers to integers before multiplication or subtraction. The index is a natural number at least twenty-one, equivalently a positive integer in that range. Splitting a finite board into its initial two rows and remaining rows gives a continuation count. Induction on the remaining length identifies it with v. The first-row boundary and first-entry constraint define a weighted sum of v, which therefore equals a(k+2). The finite vector identity and linearity yield the recurrence for heights at least twenty-two. The same checked continuation table and the literal singleton count a(1)=3 give the height-twenty-one boundary case."))),
                DescribeRole.Theorem))));

    private static Formula HorizontalFormula()
    {
        var r = V("r"); var j = V("j");
        var jv = Call("val", j);
        var left = Conditional(Seq(D(0), Sp, Lt, Sp, jv),
            Call("equalBit", App(r, Sub(jv, D(1))), App(r, j)), D(0));
        var right = Conditional(Seq(Add(jv, D(1)), Sp, Lt, Sp, D(3)),
            Call("equalBit", App(r, Add(jv, D(1))), App(r, j)), D(0));
        return All("r", V("Row"), All("j", Call("Fin", D(3)),
            Eq(Call("horizontal", r, j), Add(left, right))));
    }

    private static Formula BoundaryFormula()
    {
        var r = V("r"); var s = V("s"); var j = V("j");
        return All("r", V("Row"), All("s", V("Row"),
            Seq(Call("Boundary", r, s), Sp, F.Iff, Sp, Parenthesized(
                All("j", Call("Fin", D(3)), DifferentTwo(Add(Call("horizontal", r, j),
                    Call("equalBit", App(s, j), App(r, j))))))));
    }

    private static Formula InteriorFormula()
    {
        var r = V("r"); var s = V("s"); var t = V("t"); var j = V("j");
        var neighbors = Add(Add(Call("horizontal", s, j), Call("equalBit", App(r, j), App(s, j))),
            Call("equalBit", App(t, j), App(s, j)));
        return All("r", V("Row"), All("s", V("Row"), All("t", V("Row"),
            Seq(Call("Interior", r, s, t), Sp, F.Iff, Sp,
                Parenthesized(All("j", Call("Fin", D(3)), DifferentTwo(neighbors)))))));
    }

    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A"); var i = V("i"); var j = V("j");
        var iv = Call("val", i);
        var row = Parenthesized(Seq(LambdaLower, Sp, V("c"), Sp, Mapsto, Sp,
            App(a, Pair(i, V("c")))));
        var first = Ex("i", Call("Fin", n), AndOf(Eq(iv, D(0)),
            Eq(App(a, Pair(i, D(0))), V("false"))));
        var before = Conditional(Seq(D(0), Sp, Lt, Sp, iv),
            Call("equalBit", App(a, Pair(Sub(iv, D(1)), j)), App(a, Pair(i, j))), D(0));
        var after = Conditional(Seq(Add(iv, D(1)), Sp, Lt, Sp, n),
            Call("equalBit", App(a, Pair(Add(iv, D(1)), j)), App(a, Pair(i, j))), D(0));
        var legal = All("i", Call("Fin", n), All("j", Call("Fin", D(3)),
            DifferentTwo(Add(Add(Call("horizontal", row, j), before), after))));
        var cells = Seq(Call("Fin", n), Sp, Times, Sp, Call("Fin", D(3)));
        var boards = Seq(OpenBrace, a, Colon, Sp, Arrow(cells, V("Bool")), Sp, Mid, Sp,
            AndOf(first, legal), CloseBrace);
        return All("n", V("Nat"), Eq(Call("a", n), Call("card", boards)));
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

    private static readonly int[] Coefficients = [4,-3,-2,2,2,-7,-8,15,4,-8,-4,15,8,-7,-2,2,2,-3,-4,-1];

    private static Formula Recurrence(Func<byte, Formula> term)
    {
        Formula? result = null;
        for (byte i = 0; i < Coefficients.Length; i++)
        {
            var c = Coefficients[i];
            var value = term((byte)(i + 1));
            var magnitude = Math.Abs(c) == 1 ? value : Mul(D((byte)Math.Abs(c)), value);
            result = result is null ? magnitude : c > 0 ? Add(result, magnitude) : Sub(result, magnitude);
        }
        return result!;
    }

    private static Formula CertificateFormula()
    {
        var r = V("r"); var s = V("s");
        var row = Arrow(Call("Fin", D(3)), V("Bool"));
        return All("r", row, All("s", row, Eq(Call("v", D(20), r, s),
            Recurrence(j => Call("v", D((byte)(20 - j)), r, s)))));
    }

    private static Formula ResultFormula()
    {
        var n = V("n");
        return All("n", V("Nat"), Imp(Seq(D(21), Sp, Leq, Sp, n),
            Eq(Cast(Call("a", n)), Recurrence(j => Cast(Call("a", Sub(n, D(j))))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Seq(Operatorname, Grp(V("if")), Sp, Parenthesized(condition), Sp,
            Operatorname, Grp(V("then")), Sp, yes, Sp, Operatorname, Grp(V("else")), Sp, no);
    private static Formula DifferentTwo(Formula f) => Seq(f, Sp, Neq, Sp, D(2));
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, b);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Cast(Formula a) => Parenthesized(Seq(a, Colon, Sp, V("Int")));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string name, Formula t, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, t, Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula t, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, t, Comma, Sp, Parenthesized(body));
    private static Formula AndOf(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
}
