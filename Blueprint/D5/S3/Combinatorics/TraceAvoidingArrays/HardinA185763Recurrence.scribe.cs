using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA185763RecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/hardin2011tracearrays");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal binary arrays, their neighboring block traces, and the exact recurrence for A185763.",
        H("Trace-avoiding binary arrays: A185763"),
        Blocks(
            Node("block", "Contiguous blocks", "block", BlockFormula(), "Number of (n+1) X 4 binary arrays with no 2 X 2 subblock trace equal to any horizontal or vertical neighbor 2 X 2 subblock trace. OEIS A185763, name field (unpaginated). A block selects adjacent rows and columns; its entries are embedded in the integers.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("valid", "Unequal neighboring traces", "valid", ValidFormula(), "Number of (n+1) X 4 binary arrays with no 2 X 2 subblock trace equal to any horizontal or vertical neighbor 2 X 2 subblock trace. OEIS A185763, name field (unpaginated). Matrix.trace is the sum of the two main-diagonal entries. Neighbors have origins differing by one in exactly one coordinate. Every array is labeled; no symmetry or boundary identification is imposed.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("count", "The literal array count", "count", CountFormula(), "Number of (n+1) X 4 binary arrays with no 2 X 2 subblock trace equal to any horizontal or vertical neighbor 2 X 2 subblock trace. OEIS A185763, name field (unpaginated). The index n counts one fewer than the number of rows; the width is 4 and entries lie in Fin 2.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("series", "The zero-constant generating series", "generatingSeries", SeriesFormula(), "The source has offset 1. The coefficient at zero is zero, and its coefficient at every positive index is the count of those arrays.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The published formulas", "claim", Disp(IffF(V("claim"), ClaimBody())), "Empirical: a(n) = a(n-1) + 10*a(n-2) + 3*a(n-3) - 5*a(n-4) + a(n-5) for n>6. Empirical g.f.: 8*x*(13 + 33*x - 16*x^3 + 7*x^4 - x^5) / (1 - x - 10*x^2 - 3*x^3 + 5*x^4 - x^5). - _Colin Barker_, Apr 16 2018 OEIS A185763, formula field (unpaginated). Counts in the recurrence are embedded in Int, and the formal series has coefficients in Rat.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The formulas hold", "result", Disp(ClaimBody()), "A bijection encodes each binary row by a finite integer. The adjacent-trace tests give pair and triple conditions on consecutive rows. Weighted classes of row pairs preserve all continuation counts. An exact matrix-vector identity propagates to every length and gives the recurrence; coefficient comparison gives the formal generating series. This result settles OEIS A185763 (external question #21315) as a member of the shared Hardin problem resolution recorded with A185761.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))), []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(DescribeId.Create("hardin-a185763-" + id), DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula ArrayType(Formula n) => MatrixF(Fin(PlusF(n, Num(1))), Fin(Num(4)), Fin(Num(2)));
    private static Formula Val(Formula a) => Call("val", a);
    private static Formula BlockFormula()
    {
        var n = V("n"); var a = V("a"); var i = V("i"); var j = V("j"); var u = V("u"); var v = V("v");
        var row = IfF(Eq(u, Num(0)), App(Qualified("Fin", "castSucc"), i), App(Qualified("Fin", "succ"), i));
        var col = IfF(Eq(v, Num(0)), App(Qualified("Fin", "castSucc"), j), App(Qualified("Fin", "succ"), j));
        return Disp(All("n", NatF(), All("a", ArrayType(n), All("i", Fin(n), All("j", Fin(Num(3)), Eq(Call("block", a, i, j), Fn("u", Fin(Num(2)), Fn("v", Fin(Num(2)), Cast(Val(App(a, Parenthesized(row), Parenthesized(col))), IntF())))))))));
    }
    private static Formula ValidBody(Formula n, Formula a)
    {
        var i = V("i"); var k = V("k"); var j = V("j"); var l = V("l");
        Formula Trace(Formula r, Formula c) => App(Qualified("Matrix", "trace"), Call("block", a, r, c));
        return AndF(All("i", Fin(n), All("k", Fin(n), All("j", Fin(Num(3)), Imp(Eq(Val(k), PlusF(Val(i), Num(1))), Ne(Trace(i, j), Trace(k, j)))))), All("i", Fin(n), All("j", Fin(Num(3)), All("l", Fin(Num(3)), Imp(Eq(Val(l), PlusF(Val(j), Num(1))), Ne(Trace(i, j), Trace(i, l)))))));
    }
    private static Formula ValidFormula() => Disp(All("n", NatF(), All("a", ArrayType(V("n")), IffF(Call("valid", V("a")), ValidBody(V("n"), V("a"))))));
    private static Formula CountFormula() => Disp(All("n", NatF(), Eq(Call("count", V("n")), App(Qualified("Nat", "card"), Seq(OpenBrace, V("a"), Colon, Sp, ArrayType(V("n")), Sp, Mid, Sp, Call("valid", V("a")), CloseBrace)))));
    private static Formula SeriesFormula() => Disp(Eq(V("generatingSeries"), App(Qualified("PowerSeries", "mk"), Fn("n", NatF(), IfF(Eq(V("n"), Num(0)), Num(0), Cast(Call("count", V("n")), RatF()))))));
    private static Formula ClaimBody()
    {
        var n = V("n");
        return AndF(Eq(Call("count", Num(1)), Num(104)), AndF(Eq(Call("count", Num(2)), Num(368)), AndF(Eq(Call("count", Num(3)), Num(1408)), AndF(Eq(Call("count", Num(4)), Num(5272)), AndF(Eq(Call("count", Num(5)), Num(19992)), AndF(Eq(Call("count", Num(6)), Num(75192)), AndF(All("n", NatF(), Imp(LeqF(Num(7), n), Eq(Cast(Call("count", n), IntF()), PlusF(Sub(PlusF(PlusF(Cast(Call("count", Sub(n, Num(1))), IntF()), Mul(Num(10), Cast(Call("count", Sub(n, Num(2))), IntF()))), Mul(Num(3), Cast(Call("count", Sub(n, Num(3))), IntF()))), Mul(Num(5), Cast(Call("count", Sub(n, Num(4))), IntF()))), Cast(Call("count", Sub(n, Num(5))), IntF()))))), Seq(Op("let"), Sp, V("X"), Colon, Sp, Call("PowerSeries", RatF()), Colon, F.Eq, Sp, Qualified("PowerSeries", "X"), Semi, Sp, Eq(V("generatingSeries"), Mul(Mul(Mul(Num(8), V("X")), Parenthesized(Sub(PlusF(Sub(PlusF(Num(13), Mul(Num(33), V("X"))), Mul(Num(16), Pow(V("X"), Num(3)))), Mul(Num(7), Pow(V("X"), Num(4)))), Pow(V("X"), Num(5))))), Pow(Sub(PlusF(Sub(Sub(Sub(Num(1), V("X")), Mul(Num(10), Pow(V("X"), Num(2)))), Mul(Num(3), Pow(V("X"), Num(3)))), Mul(Num(5), Pow(V("X"), Num(4)))), Pow(V("X"), Num(5))), Num(-1))))))))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Num(int n) => n < 0 ? Seq(Minus, Num(-n)) : D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string owner, string name) => Seq(Op(owner), Dot, Op(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LeqF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula AndF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Fn(string name, Formula type, Formula body) => Seq(Op("fun"), Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula IfF(Formula cond, Formula yes, Formula no) => Seq(Op("if"), Sp, cond, Sp, Op("then"), Sp, yes, Sp, Op("else"), Sp, no);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula NatF() => Op("Nat");
    private static Formula IntF() => Op("Int");
    private static Formula RatF() => Op("Rat");
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula PlusF(Formula a, Formula b) => Add(a, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula MatrixF(Formula rows, Formula cols, Formula field) => Call("Matrix", rows, cols, field);

}
