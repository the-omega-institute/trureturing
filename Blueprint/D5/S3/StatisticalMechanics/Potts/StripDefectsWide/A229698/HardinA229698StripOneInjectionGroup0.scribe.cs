using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698;
internal sealed class HardinA229698StripOneInjectionGroup0Document : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripOneInjectionGroup0.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five-row HA arrays with exactly two equal-colour bonds.",H("Five-row two-defect strips"),Blocks(
        Paragraph(Text("This segment evaluates suffix indices 0 through 3.")),
        Node("rows","rows",All("k",Fin(Num(4)),Eq(Add(Call("Matrix.mulVec",Old("R"),Old("U",Call("Fin.mk",Add(Num(0),Val(V("k")))))),Tab("SQ",Call("Fin.mk",Add(Num(0),Val(V("k")))))),Tab("J",Call("Fin.mk",Add(Num(0),Val(V("k"))))))),true,"These entries evaluate only the contribution to the two-defect coordinates."))));
    private static DocumentBlock Node(string name,string title,Formula f,bool theorem,string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_","-").ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),H(title),
          StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229698")),
          Blocks(Paragraph(Text(prose))),theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    private static Formula V(string name) => F.Id(name);
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
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula App(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula x, Formula type) =>
        Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula Num(long n) => n < 0 ? Parenthesized(Seq(Minus,Num(-n))) : new Formula.Number(n);
    private static Formula Old(string n, params Formula[] a) => Call("HardinA229590StripData."+n,a);
    private static Formula Tab(string n, params Formula[] a) => Call("HardinA229698StripTables."+n,a);
    private static Formula Val(Formula x) => Call("Fin.val",x);
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Add,Parenthesized(b));

}
