using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233259PairTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransfer.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233259");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The four-row scalar pair-pattern recurrence.", H("Pair transfer recurrence"), Blocks(
        Describe.Lean(DescribeId.Create("recurrence"), DeclarationHandle.Create(Prefix + "recurrence"), H("Pair transfer recurrence"), StatementSource.FromAuthor(Disp(Formula())), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The adjusted scalar pair-pattern count satisfies the order-four recurrence."))), DescribeRole.Theorem))));
    private static Formula Formula()
    {
        var n = V("n");
        Formula L(int i) => Typed(Call("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore.L", Add(n, Num(i))), Op("Int"));
        Formula B(int i) => Add(L(i), Num(6));
        var rhs = Sub(Add(Sub(Mul(Num(10), B(8)), Mul(Num(24), B(7))), Mul(Num(21), B(6))), Mul(Num(6), B(5)));
        return All("n", Op("Nat"), Eq(B(9), rhs));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(int n) => D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Q(name) : App(Q(name), args);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { Op(part) } : new[] { Dot, Op(part) }).ToArray());
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Typed(Formula x, Formula t) => Parenthesized(Seq(x, Colon, Sp, t));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula All(string n, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, body);
}
