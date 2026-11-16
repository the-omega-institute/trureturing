using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA185761RecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185761Recurrence.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/hardin2011tracearrays");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal binary arrays, their neighboring block traces, and the exact recurrence for A185761.",
        H("Trace-avoiding binary arrays: A185761"),
        Blocks(
            Node("block", "Contiguous blocks", "block", BlockFormula(), "Number of (n+1) X 2 binary arrays with no 2 X 2 subblock trace equal to any horizontal or vertical neighbor 2 X 2 subblock trace. OEIS A185761, name field (unpaginated). A block selects adjacent rows and columns; its entries are embedded in the integers.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("valid", "Unequal neighboring traces", "valid", ValidFormula(), "Number of (n+1) X 2 binary arrays with no 2 X 2 subblock trace equal to any horizontal or vertical neighbor 2 X 2 subblock trace. OEIS A185761, name field (unpaginated). Matrix.trace is the sum of the two main-diagonal entries. Neighbors have origins differing by one in exactly one coordinate. Every array is labeled; no symmetry or boundary identification is imposed.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("count", "The literal array count", "count", CountFormula(), "Number of (n+1) X 2 binary arrays with no 2 X 2 subblock trace equal to any horizontal or vertical neighbor 2 X 2 subblock trace. OEIS A185761, name field (unpaginated). The index n counts one fewer than the number of rows; the width is 2 and entries lie in Fin 2.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("series", "The zero-constant generating series", "generatingSeries", SeriesFormula(), "The source has offset 1. The coefficient at zero is zero, and its coefficient at every positive index is the count of those arrays.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The published formulas", "claim", Disp(IffF(V("claim"), ClaimBody())), "Empirical: a(n) = a(n-1) + 4*a(n-2). G.f.: 8*x*(2 + 3*x) / (1 - x - 4*x^2). a(n) = (2^(-n)*((1-sqrt(17))^n*(-13+3*sqrt(17)) + (1+sqrt(17))^n*(13+3*sqrt(17)))) / sqrt(17). OEIS A185761, formula field (unpaginated). Counts in the recurrence are embedded in Int, the formal series has coefficients in Rat, and the square root in the closed form is the positive real square root.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The formulas hold", "result", Disp(ClaimBody()), "A bijection encodes each binary row by a finite integer. The adjacent-trace tests give pair and triple conditions on consecutive rows. Weighted classes of row pairs preserve all continuation counts. An exact matrix-vector identity propagates to every length and gives the recurrence; coefficient comparison gives the formal generating series.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("hardin1857-traceavoid"), ResolutionKind.Proved,
                [
                    DeclarationHandle.Create("D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185762Recurrence.result"),
                    DeclarationHandle.Create("D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185763Recurrence.result"),
                    DeclarationHandle.Create("D5/S3/Combinatorics/TraceAvoidingArrays/HardinA185764Recurrence.result")
                ]))), []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(DescribeId.Create("hardin-a185761-" + id), DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula ArrayType(Formula n) => MatrixF(Fin(PlusF(n, Num(1))), Fin(Num(2)), Fin(Num(2)));
    private static Formula Val(Formula a) => Call("val", a);
    private static Formula BlockFormula()
    {
        var n = V("n"); var a = V("a"); var i = V("i"); var j = V("j"); var u = V("u"); var v = V("v");
        var row = IfF(Eq(u, Num(0)), App(Qualified("Fin", "castSucc"), i), App(Qualified("Fin", "succ"), i));
        var col = IfF(Eq(v, Num(0)), App(Qualified("Fin", "castSucc"), j), App(Qualified("Fin", "succ"), j));
        return Disp(All("n", NatF(), All("a", ArrayType(n), All("i", Fin(n), All("j", Fin(Num(1)), Eq(Call("block", a, i, j), Fn("u", Fin(Num(2)), Fn("v", Fin(Num(2)), Cast(Val(App(a, Parenthesized(row), Parenthesized(col))), IntF())))))))));
    }
    private static Formula ValidBody(Formula n, Formula a)
    {
        var i = V("i"); var k = V("k"); var j = V("j"); var l = V("l");
        Formula Trace(Formula r, Formula c) => App(Qualified("Matrix", "trace"), Call("block", a, r, c));
        return AndF(All("i", Fin(n), All("k", Fin(n), All("j", Fin(Num(1)), Imp(Eq(Val(k), PlusF(Val(i), Num(1))), Ne(Trace(i, j), Trace(k, j)))))), All("i", Fin(n), All("j", Fin(Num(1)), All("l", Fin(Num(1)), Imp(Eq(Val(l), PlusF(Val(j), Num(1))), Ne(Trace(i, j), Trace(i, l)))))));
    }
    private static Formula ValidFormula() => Disp(All("n", NatF(), All("a", ArrayType(V("n")), IffF(Call("valid", V("a")), ValidBody(V("n"), V("a"))))));
    private static Formula CountFormula() => Disp(All("n", NatF(), Eq(Call("count", V("n")), App(Qualified("Nat", "card"), Seq(OpenBrace, V("a"), Colon, Sp, ArrayType(V("n")), Sp, Mid, Sp, Call("valid", V("a")), CloseBrace)))));
    private static Formula SeriesFormula() => Disp(Eq(V("generatingSeries"), App(Qualified("PowerSeries", "mk"), Fn("n", NatF(), IfF(Eq(V("n"), Num(0)), Num(0), Cast(Call("count", V("n")), RatF()))))));
    private static Formula ClaimBody()
    {
        var n = V("n");
        return AndF(Eq(Call("count", Num(1)), Num(16)), AndF(Eq(Call("count", Num(2)), Num(40)), AndF(All("n", NatF(), Imp(LeqF(Num(3), n), Eq(Cast(Call("count", n), IntF()), PlusF(Cast(Call("count", Sub(n, Num(1))), IntF()), Mul(Num(4), Cast(Call("count", Sub(n, Num(2))), IntF())))))), AndF(Seq(Op("let"), Sp, V("X"), Colon, Sp, Call("PowerSeries", RatF()), Colon, F.Eq, Sp, Qualified("PowerSeries", "X"), Semi, Sp, Eq(V("generatingSeries"), Mul(Mul(Mul(Num(8), V("X")), Parenthesized(PlusF(Num(2), Mul(Num(3), V("X"))))), Pow(Sub(Sub(Num(1), V("X")), Mul(Num(4), Pow(V("X"), Num(2)))), Num(-1))))), All("n", NatF(), Imp(LeqF(Num(1), n), Eq(Cast(Call("count", n), RealF()), new Formula.Fraction(Mul(Pow(Pow(Cast(Num(2), RealF()), Num(-1)), n), Parenthesized(PlusF(Mul(Pow(Sub(Num(1), App(Qualified("Real", "sqrt"), Num(17))), n), Parenthesized(PlusF(Num(-13), Mul(Num(3), App(Qualified("Real", "sqrt"), Num(17)))))), Mul(Pow(PlusF(Num(1), App(Qualified("Real", "sqrt"), Num(17))), n), Parenthesized(PlusF(Num(13), Mul(Num(3), App(Qualified("Real", "sqrt"), Num(17))))))))), App(Qualified("Real", "sqrt"), Num(17))))))))));
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
    private static Formula RealF() => Op("Real");
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula PlusF(Formula a, Formula b) => Add(a, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula MatrixF(Formula rows, Formula cols, Formula field) => Call("Matrix", rows, cols, field);

}
