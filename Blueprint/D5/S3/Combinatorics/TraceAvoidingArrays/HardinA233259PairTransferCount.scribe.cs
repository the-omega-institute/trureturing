using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233259PairTransferCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233259");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The local transfer counting bridge.", H("Transfer count"), Blocks(
        Describe.Lean(DescribeId.Create("count-transfer"), DeclarationHandle.Create(Prefix + "count_transfer"), H("Transfer count"), StatementSource.FromAuthor(Disp(Formula())), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("The proper-pattern count equals the weighted transfer scalar."))), DescribeRole.Theorem))));
    private static Formula Formula() => All("n", Q("Nat"), Eq(Typed(App(Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore.L"), Add(V("n"), D(2))), Q("Int")), App(Q("dotProduct"), Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore.weights"), App(Q("Matrix.mulVec"), Power(Q("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore.Q"), V("n")), Ones()))));
    private static Formula Ones() => Typed(Vector(1,1,1,1,1,1,1,1,1,1,1,1,1,1), Arrow(Fin(D(14)), Q("Int")));
    private static Formula Vector(params int[] xs) => Seq(Bang, OpenBracket, Seq(xs.SelectMany((x,i)=>i==0?new[]{D(x)}:new[]{Comma,Sp,D(x)}).ToArray()), CloseBracket);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Typed(Formula x, Formula t) => Parenthesized(Seq(x, Colon, Sp, t));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a,b);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f,[..args]);
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((part,i)=>i==0?new[]{Operatorname,Grp(V(part))}:new[]{Dot,Operatorname,Grp(V(part))}).ToArray());
    private static Formula V(string n) => F.Id(n);
    private static Formula D(int n) => StrataLint.Scribe.FormulaDsl.D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c=>(byte)(c-'0')).ToArray());
    private static Formula Fin(Formula n) => App(Q("Fin"), n);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a,b);
}
