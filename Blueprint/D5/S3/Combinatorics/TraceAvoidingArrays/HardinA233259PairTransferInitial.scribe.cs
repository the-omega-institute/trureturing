using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233259PairTransferInitialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferInitial.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233259");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Initial class weights.", H("Initial weights"), Blocks(
        Describe.Lean(DescribeId.Create("initial-weights"), DeclarationHandle.Create(Prefix + "initial_weights"), H("Initial weights"), StatementSource.FromAuthor(Disp(Formula())), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Initial class-weight certificate."))), DescribeRole.Theorem))));
    private static Formula Formula() => All("s", Fin(D(14)), Eq(Sum("a", Q("Col"), Sum("b", Q("Col"), If(And(App(Q("compatible"), V("a"), V("b")), Eq(App(Q("cls"), V("b")), V("s"))), D(1), D(0)))), App(Q("weights"), V("s"))));
    private static Formula Sum(string name, Formula domain, Formula body) => Seq(new Formula.Subscript(F.Sum, Seq(V(name), Sp, InMacro, Sp, domain)), Sp, Parenthesized(body));
    private static Formula If(Formula c, Formula y, Formula n) => Parenthesized(Seq(V("if"), Sp, c, Sp, V("then"), Sp, y, Sp, V("else"), Sp, n));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) => i == 0 ? new[] { Operatorname, Grp(V(part)) } : new[] { Dot, Operatorname, Grp(V(part)) }).ToArray());
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula D(int n) => StrataLint.Scribe.FormulaDsl.D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => (byte)(c - '0')).ToArray());
    private static Formula Fin(Formula n) => App(Q("Fin"), n);
}
