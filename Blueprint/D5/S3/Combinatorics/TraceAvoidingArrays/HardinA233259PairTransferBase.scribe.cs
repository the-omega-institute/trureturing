using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;
internal sealed class HardinA233259PairTransferBaseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferBase.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Automata/hardin2013a233259");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Initial scalar transfer values.", H("Initial values"), Blocks(
        Describe.Lean(DescribeId.Create("initial-values"), DeclarationHandle.Create(Prefix + "initial_values"), H("Initial values"), StatementSource.FromAuthor(Disp(Formula())), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("Initial scalar transfer values."))), DescribeRole.Theorem))));
    private static Formula Formula()
    {
        var k = V("k");
        var values = Seq(Bang, OpenBracket, D(384), Comma, Sp, D(2592), Comma, Sp,
            D(17496), Comma, Sp, D(121176), Comma, Sp, D(842616), Comma, Sp,
            D(5871528), Comma, Sp, D(40931568), Comma, Sp, D(285366888), CloseBracket);
        return All("k", Fin(D(8)), Eq(Typed(Own("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore.L", Add(Val(k), D(2))), Q("Int")),
            App(Typed(values, Arrow(Fin(D(8)), Q("Int"))), k)));
    }
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Typed(Formula x, Formula t) => Parenthesized(Seq(x, Colon, Sp, t));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Own(string name, params Formula[] args) =>
        Call(name, args);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { NamePart(part) } : new[] { Dot, NamePart(part) }).ToArray());
    private static Formula NamePart(string name)
    {
        var words = name.Split('_');
        Formula result = V(words[^1]);
        for (var i = words.Length - 2; i >= 0; --i)
            result = Seq(V(words[i]), Underscore, Grp(result));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Q(name) : App(Q(name), args);
    private static Formula V(string n) => F.Id(n);
    private static Formula D(int n) => StrataLint.Scribe.FormulaDsl.D(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c=>(byte)(c-'0')).ToArray());
    private static Formula Fin(Formula n) => App(Q("Fin"), n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
}
