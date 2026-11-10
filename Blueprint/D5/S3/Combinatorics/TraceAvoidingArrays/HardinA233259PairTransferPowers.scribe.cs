using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233259PairTransferPowersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferPowers.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233259");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The finite transfer-power table.", H("Transfer powers"), Blocks(
        Node("W", "Power table", WFormula(), DescribeRole.Definition),
        Node("coefficients", "Recurrence coefficients", CoefficientsFormula(), DescribeRole.Definition),
        Node("table_zero", "Power table base", TableZero(), DescribeRole.Theorem),
        Node("table_steps", "Power table steps", TableSteps(), DescribeRole.Theorem),
        Node("powers_table", "Power table", PowersTable(), DescribeRole.Theorem),
        Node("power_polynomial", "Power polynomial", PowerPolynomial(), DescribeRole.Theorem))));
    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role) => Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(title + "."))), role);
    private static Formula WFormula() => Eq(Own("W"), Typed(MatrixRows(), Arrow(Fin(D(9)), Arrow(Fin(D(14)), Q("Int")))));
    private static Formula CoefficientsFormula() => Eq(Own("coefficients"), Typed(Ints(-6, 21, -24, 10), Arrow(Fin(D(4)), Q("Int"))));
    private static Formula TableZero() => Eq(App(Own("W"), D(0)), Typed(Ints(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1), Arrow(Fin(D(14)), Q("Int"))));
    private static Formula TableSteps()
    {
        var k = V("k");
        var lhs = App(Own("W"), App(Q("Fin.succ"), k));
        var rhs = App(Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore.Q.mulVec"), App(Own("W"), App(Q("Fin.castSucc"), k)));
        return All("k", Fin(D(8)), Eq(lhs, rhs));
    }
    private static Formula PowersTable() => All("k", Fin(D(9)), Eq(App(Q("Matrix.mulVec"), Power(Own("Q"), Call("Fin.val", V("k"))), Ones()), App(Own("W"), V("k"))));
    private static Formula PowerPolynomial() => Eq(App(Q("Matrix.mulVec"), Power(Own("Q"), Add(D(4), D(4))), Ones()), Sum("j", Fin(D(4)), Mul(App(Own("coefficients"), V("j")), App(Q("Matrix.mulVec"), Power(Own("Q"), Add(D(4), Call("Fin.val", V("j")))), Ones()))));
    private static Formula MatrixRows() => Vector(
        Vector(2,2,2,2,0,2,2,0,2,2,0,0,0,0), Vector(1,1,0,1,1,1,0,1,0,1,1,0,0,0), Vector(1,1,0,0,0,0,0,0,1,1,0,0,0,0), Vector(1,1,1,1,0,0,0,0,0,1,1,0,1,1),
        Vector(0,0,0,1,1,0,0,0,0,0,0,1,0,1), Vector(1,1,1,1,0,0,0,0,0,0,0,0,0,0), Vector(1,1,0,0,0,0,0,0,0,0,0,0,0,0), Vector(0,0,0,1,1,0,0,0,0,0,0,0,0,0),
        Vector(1,1,0,0,0,1,0,1,0,0,0,0,0,0), Vector(1,1,1,1,0,1,1,0,1,1,0,0,0,0), Vector(0,0,0,1,1,0,0,0,0,1,1,0,0,0), Vector(0,0,0,0,0,0,0,0,0,0,0,1,0,1),
        Vector(0,0,0,0,0,0,0,0,1,1,0,0,0,0), Vector(0,0,0,0,0,0,0,0,0,1,1,0,1,1));
    private static Formula Ones() => Typed(Vector(1,1,1,1,1,1,1,1,1,1,1,1,1,1), Arrow(Fin(D(14)), Q("Int")));
    private static Formula Vector(params int[] xs) => Seq(Bang, OpenBracket, Seq(xs.SelectMany((x, i) => i == 0 ? new[] { Signed(x) } : new[] { Comma, Sp, Signed(x) }).ToArray()), CloseBracket);
    private static Formula Vector(params Formula[] xs) => Seq(Bang, OpenBracket, Seq(xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, Sp, x }).ToArray()), CloseBracket);
    private static Formula Ints(params int[] xs) => Vector(xs);
    private static Formula Signed(int x) => x < 0 ? Seq(Neg, Sp, D(-x)) : D(x);
    private static Formula Sum(string n, Formula domain, Formula body) => Seq(new Formula.Subscript(F.Sum, Seq(V(n), Sp, InMacro, Sp, domain)), Sp, Parenthesized(body));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Own(string n, params Formula[] args) => Call("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferPowers." + n, args);
    private static Formula Call(string n, params Formula[] args) => App(Q(n), args);
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((part, i) => i == 0 ? new[] { Operatorname, Grp(V(part)) } : new[] { Dot, Operatorname, Grp(V(part)) }).ToArray());
    private static Formula V(string n) => F.Id(n);
    private static Formula D(int n) => StrataLint.Scribe.FormulaDsl.D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());
    private static Formula Fin(Formula n) => App(Q("Fin"), n);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Typed(Formula x, Formula t) => Parenthesized(Seq(x, Colon, Sp, t));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
}
