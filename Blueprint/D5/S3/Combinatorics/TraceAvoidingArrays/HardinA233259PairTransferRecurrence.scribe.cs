using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233259PairTransferRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferRecurrence.";
    private const string Core = "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233259");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The scalar order-four recurrence.", H("Scalar recurrence"), Blocks(Describe.Lean(DescribeId.Create("recurrence"), DeclarationHandle.Create(Prefix + "recurrence"), H("Scalar recurrence"), StatementSource.FromAuthor(Disp(Formula())), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The adjusted transfer scalar satisfies the order-four recurrence."))), DescribeRole.Theorem))));
    private static Formula Formula()
    {
        var n = V("n");
        Formula L(int i) => Typed(App(Q(Core + "L"), Add(n, D(i))), Q("Int"));
        Formula B(int i) => Add(L(i), D(6));
        return All("n", Q("Nat"), Eq(B(9), Sub(Add(Sub(Mul(D(10), B(8)), Mul(D(24), B(7))), Mul(D(21), B(6))), Mul(D(6), B(5)))));
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula D(int n) => StrataLint.Scribe.FormulaDsl.D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c=>(byte)(c-'0')).ToArray());
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((part,i)=>i==0?new[]{Operatorname,Grp(V(part))}:new[]{Dot,Operatorname,Grp(V(part))}).ToArray());
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f,[..args]);
    private static Formula Typed(Formula x, Formula t) => Parenthesized(Seq(x, Colon, Sp, t));
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Parenthesized(Formula x) => Seq(Open,x,Close);
}
