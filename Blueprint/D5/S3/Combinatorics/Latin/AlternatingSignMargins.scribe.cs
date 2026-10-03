using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Latin;

internal sealed class AlternatingSignMarginsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Latin/AlternatingSignMargins.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/ernst2026italiansquares");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed row and column margins admit an alternating signed square matrix exactly when their total sums agree.",
        H("Margins of alternating signed matrices"),
        Blocks(
            Node("signed", "Signed integer entries", "Signed", SignedFormula(),
                "A signed integer is precisely one of minus one, zero and one.", true, DescribeRole.Definition),
            Node("alternates", "Alternation along a line", "Alternates", AlternatesFormula(),
                "The line is indexed by Fin n in its natural order. Two nonzero entries with only zeros strictly between them must differ. For signed entries this means opposite signs; there is no restriction on the first or last sign.", true, DescribeRole.Definition),
            Node("class", "The matrix class W", "W", WFormula(),
                "Section 8, p. 27: “Section 4 introduces the set W_n consisting of all (0, ±1)-matrices in which the non-zero entries of each row and column alternate in sign, and the sum of each row/column is in {0, ±1}.” The encoding uses integer matrices with rows and columns indexed by Fin n. The setOf expression includes signed entries, row alternation, column alternation, signed row sums and signed column sums, in that order. A row function is j ↦ X(i,j), and a column function is i ↦ X(i,j). Empty lines satisfy alternation.", true, DescribeRole.Definition),
            Node("claim", "Problem 8.3 and its exact answer", "claim", ClaimFormula(),
                "Section 8, p. 27: “Problem 8.3. For which (0, ±1)-vectors R and S of order n does there exist X ∈ W_n with row-sums R and column-sums S?” Section 8, p. 27: “Section 4 introduces the set W_n consisting of all (0, ±1)-matrices in which the non-zero entries of each row and column alternate in sign, and the sum of each row/column is in {0, ±1}.” The quantified proposition encodes the complete answer: equality of the two total sums is necessary and sufficient. Both vectors have integer entries in {−1,0,1}; every sum ranges over all of Fin n. All natural orders, including zero, are included.", true, DescribeRole.Definition),
            Node("result", "Equal totals are the only obstruction", "result", Disp(ClaimBody()),
                "Summing all entries in either order gives necessity. For sufficiency, orient the margins so that the positive row count is at least the positive column count. Equality of totals makes the positive and negative row surpluses equal. Match the required signed columns to rows of the same sign and place each remaining positive-negative row pair in its own zero-margin column. The zero-column capacity follows from the three sign-class counts. Rows then have at most one nonzero entry, and columns at most one of each sign, so every line alternates. Transposition handles the other orientation.", false, DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, bool literature, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-sign-margins-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Different(Formula a, Formula b) => Rel(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Less(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var k = clauses.Length - 2; k >= 0; k--)
            result = Logic(clauses[k], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Int() => new Formula.NamedConstant(FormulaIdentifier.Create("Int"));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Vector(Formula n) => Seq(Fin(n), Sp, To, Sp, Int());
    private static Formula Matrix(Formula n) => Call("Matrix", Fin(n), Fin(n), Int());
    private static Formula SumOver(string variable, Formula n, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(variable), Sp, InMacro, Sp, Fin(n)), Sp,
            Parenthesized(body));
    private static Formula Lambda(string variable, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, F.Id(variable), Colon, Sp, type, Dot, Sp, Parenthesized(body));

    private static Formula SignedFormula()
    {
        var x = F.Id("x");
        var minusOne = Seq(Minus, D(1));
        return Disp(All("x", Int(), Iff(Call("Signed", x),
            Logic(Equal(x, minusOne), FormulaLogicOperator.Or,
                Logic(Equal(x, D(0)), FormulaLogicOperator.Or, Equal(x, D(1)))))));
    }

    private static Formula AlternatesFormula()
    {
        var n = F.Id("n"); var v = F.Id("v");
        var a = F.Id("a"); var b = F.Id("b"); var c = F.Id("c");
        var intervening = All("c", Fin(n), Imp(Less(a, c),
            Imp(Less(c, b), Equal(Call("v", c), D(0)))));
        var body = All("a", Fin(n), All("b", Fin(n), Imp(Less(a, b),
            Imp(Different(Call("v", a), D(0)), Imp(Different(Call("v", b), D(0)),
                Imp(intervening, Different(Call("v", a), Call("v", b))))))));
        return Disp(All("n", Nat(), All("v", Vector(n), Iff(Call("Alternates", v), body))));
    }

    private static Formula WFormula()
    {
        var n = F.Id("n"); var i = F.Id("i"); var j = F.Id("j");
        var conditions = And(
            All("i", Fin(n), All("j", Fin(n), Call("Signed", Call("X", i, j)))),
            All("i", Fin(n), Call("Alternates", Lambda("j", Fin(n), Call("X", i, j)))),
            All("j", Fin(n), Call("Alternates", Lambda("i", Fin(n), Call("X", i, j)))),
            All("i", Fin(n), Call("Signed", SumOver("j", n, Call("X", i, j)))),
            All("j", Fin(n), Call("Signed", SumOver("i", n, Call("X", i, j)))));
        return Disp(All("n", Nat(), Equal(Call("W", n),
            Call("setOf", Lambda("X", Matrix(n), conditions)))));
    }

    private static Formula ClaimFormula() => Disp(Iff(F.Id("claim"), ClaimBody()));

    private static Formula ClaimBody()
    {
        var n = F.Id("n"); var x = F.Id("X");
        var i = F.Id("i"); var j = F.Id("j");
        var realization = Ex("X", Matrix(n), And(
            Rel(x, FormulaRelationOperator.MemberOf, Call("W", n)),
            All("i", Fin(n), Equal(SumOver("j", n, Call("X", i, j)), Call("R", i))),
            All("j", Fin(n), Equal(SumOver("i", n, Call("X", i, j)), Call("S", j)))));
        var totals = Equal(SumOver("i", n, Call("R", i)), SumOver("j", n, Call("S", j)));
        return All("n", Nat(), All("R", Vector(n), All("S", Vector(n),
            Imp(All("i", Fin(n), Call("Signed", Call("R", i))),
                Imp(All("j", Fin(n), Call("Signed", Call("S", j))), Iff(realization, totals))))));
    }
}
