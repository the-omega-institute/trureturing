using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698;
internal sealed class HardinA229698StripTablesDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripTables.";
    private const string LeanPrefix="D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTables.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five-row HA arrays with exactly two equal-colour bonds.",H("Five-row two-defect strips"),Blocks(
        Paragraph(Text("These finite tables list integer vectors with columns indexed by the 41 colour classes.")),
        Node("SQ","SQ",Typed(Own("SQ"),Arrow(Fin(Num(19)),Vec())),false,"This 19 by 41 integer table is pinned by HardinA229698StripInjection.two_injection_powers: S applied to each zero-defect suffix vector."),
        Node("J","J",Typed(Own("J"),Arrow(Fin(Num(27)),Vec())),false,"This 27 by 41 integer table is pinned by HardinA229698StripInjection.injection_powers: B applied to each one-defect suffix vector."),
        Node("V","V",Typed(Own("V"),Arrow(Fin(Num(28)),Vec())),false,"This 28 by 41 integer table is pinned by HardinA229698StripPowers.powers_table: the coordinates in the two-defect sector."))));
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
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Num(long n) => n < 0 ? Parenthesized(Seq(Minus,Num(-n))) : new Formula.Number(n);
    private static Formula Own(string n, params Formula[] a) => Call(LeanPrefix+n,a);
    private static Formula Vec() => Arrow(Fin(Num(41)),Q("Int"));

}
