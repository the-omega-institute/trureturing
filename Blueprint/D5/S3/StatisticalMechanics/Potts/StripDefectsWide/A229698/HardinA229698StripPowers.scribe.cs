using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698;
internal sealed class HardinA229698StripPowersDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripPowers.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five-row HA arrays with exactly two equal-colour bonds.",H("Five-row two-defect strips"),Blocks(
        Paragraph(Text("The block structure separates the newly computed coordinates from the inherited suffix.")),
        Node("powers_table","powers table",All("k",Fin(Num(28)),Eq(Call("Matrix.mulVec",Power(Data("T"),Val(V("k"))),Data("terminal")),Call("Sum.elim",Tab("V",V("k")),Call("Matrix.mulVec",Power(Old("T"),Val(V("k"))),Old("terminal"))))),true,"The last 82 coordinates are the one-defect power vector. Only the first 41 coordinates are supplied by V."),
        Node("power_polynomial","power polynomial",Eq(Call("Matrix.mulVec",Power(Data("T"),Add(Num(6),Num(21))),Data("terminal")),Sum("j",Fin(Num(21)),Smul(Data("coefficients",V("j")),Call("Matrix.mulVec",Power(Data("T"),Add(Num(6),Val(V("j")))),Data("terminal"))))),true,"The new coordinates satisfy the degree-21 relation. On the last 82 coordinates, the one-defect degree-14 polynomial is multiplied by the zero-defect degree-seven factor."))));
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
    private static Formula Data(string n, params Formula[] a) => Call("HardinA229698StripData."+n,a);
    private static Formula Tab(string n, params Formula[] a) => Call("HardinA229698StripTables."+n,a);
    private static Formula Val(Formula x) => Call("Fin.val",x);
    private static Formula Sum(string n, Formula t, Formula x) => Seq(F.Sum,Underscore,Grp(V(n),Colon,Sp,t),Sp,Parenthesized(x));
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Add,Parenthesized(b));
    private static Formula Smul(Formula a,Formula b) => Call("HSMul.hSMul",a,b);
    private static Formula Power(Formula a,Formula b) => new Formula.Power(a,b);

}
