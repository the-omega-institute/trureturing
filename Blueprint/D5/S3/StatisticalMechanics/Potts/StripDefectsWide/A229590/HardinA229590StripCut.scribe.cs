using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590;
internal sealed class HardinA229590StripCutDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590StripCut.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five-row HA arrays with exactly one equal-colour bond.",H("Five-row one-defect strips"),Blocks(
        Paragraph(Text("The two summands retain the exact remaining budget. The terminal summand represents zero remaining defects.")),
        Node("column_sum","column sum",All("f",Arrow(Owner("Col"),Q("Int")),Eq(Sum("r",Row(),App(V("f"),Data("boundary",V("r")))),Sum("c",Owner("Col"),App(V("f"),V("c"))))),true,"Functions on five colours and five-component columns are in bijection, so their integer sums agree."),
        Node("column_boundary","column boundary",All("r",Row(),Eq(Owner("column" ,Data("boundary" ,V("r"))),V("r"))),true,"column boundary."),
        Node("transition_counts","transition counts",All("p",Owner("Col"),All("d",Fin(Num("2")),All("s",S(),Eq(Sum("r",Row(),If(And(Le(Data("cross" ,V("p"),V("r")),Val(V("d"))),Eq(Data("cl" ,Data("boundary" ,V("r")),Sub(Val(V("d")),Data("cross" ,V("p"),V("r")))),V("s"))),Typed(Num("1"),Q("Int")),Typed(Num("0"),Q("Int")))),Data("T" ,Data("cl" ,V("p"),Val(V("d"))),V("s")))))),true,"A zero-cost step preserves the remaining budget and uses Q; a step of cost one spends the budget and uses R. No other step is accepted."),
        Node("initial_counts","initial counts",All("s",S(),Eq(Sum("r",Row(),If(Eq(Data("cl" ,Data("boundary" ,V("r")),Num("1")),V("s")),Typed(Num("1"),Q("Int")),Typed(Num("0"),Q("Int")))),Data("initial" ,V("s")))),true,"Every initial column starts with one remaining defect. The class multiplicities are the five-row multiplicities."))));

    private static DocumentBlock Node(string name,string title,Formula f,bool theorem,string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_","-").ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),H(title),
          StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229590")),
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
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));

    private static Formula Sum(string n, Formula t, Formula b) => Seq(F.Sum,Underscore,Grp(V(n),Colon,Sp,t),Sp,Parenthesized(b));
    private static Formula If(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,y,Sp,Q("else"),Sp,n));
    private static Formula Num(string n) => D(n.Select(c => (byte)(c-'0')).ToArray());
    private static Formula Num(long n) => n < 0 ? Parenthesized(Seq(Minus,Num(-n))) : new Formula.Number(n);
    private static Formula Owner(string n, params Formula[] a) => Call("HardinA233260Literal."+n,a);
    private static Formula Data(string n, params Formula[] a) => Call("HardinA229590StripData."+n,a);
    private static Formula S() => Call("Sum",Fin(Num(41)),Fin(Num(41)));
    private static Formula Row() => Arrow(Fin(Num(5)),Fin(Num(3)));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a,Comma,Sp,b));
    private static Formula Tuple(params Formula[] a) => a.Length==2 ? Pair(a[0],a[1]) : Pair(a[0],Tuple(a.Skip(1).ToArray()));
}
