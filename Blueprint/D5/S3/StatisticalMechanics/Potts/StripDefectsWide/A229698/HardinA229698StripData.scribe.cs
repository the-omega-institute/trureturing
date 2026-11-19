using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698;
internal sealed class HardinA229698StripDataDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698StripData.";
    private const string LeanPrefix="D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five-row HA arrays with exactly two equal-colour bonds.",H("Five-row two-defect strips"),Blocks(
        Paragraph(Text("There are 123 states, with 41 colour classes in each exact remaining-budget sector. All bonds join adjacent columns: five horizontal bonds and four antidiagonal bonds.")),
        Node("S","S",Typed(Own("S"),Call("Matrix",Fin(Num(41)),Fin(Num(41)),Q("Int"))),false,"The 41 by 41 integer table counts successor columns with exactly two equal-colour HA bonds. Its entries are pinned by HardinA229698StripNew.quotient_rows."),
        Node("B","B",All("i",Fin(Num(41)),Eq(Typed(Own("B",V("i")),Arrow(OS(),Q("Int"))),Call("Sum.elim",Old("R",V("i")),Own("S",V("i"))))),false,"The rectangular block joins the one-bond and two-bond transitions."),
        Node("cl","cl",All("p",Owner("Col"),All("d",Q("Nat"),Eq(Typed(Own("cl",V("p"),V("d")),S()),If(Eq(V("d"),Num(2)),Call("Sum.inl",Owner("cls",V("p"))),Call("Sum.inr",Old("cl",V("p"),V("d"))))))),false,"The first summand has two defects left; the other summand keeps the one-defect classification."),
        Node("T","T",Eq(Typed(Own("T"),Call("Matrix",S(),S(),Q("Int"))),Call("Matrix.fromBlocks",Owner("Q"),Own("B"),Typed(Num(0),Call("Matrix",OS(),Fin(Num(41)),Q("Int"))),Old("T"))),false,"The diagonal block on the last 82 states is the one-defect matrix."),
        Node("initial","initial",Eq(Typed(Own("initial"),Arrow(S(),Q("Int"))),Call("Sum.elim",Fn("i",Fin(Num(41)),Old("initial",Call("Sum.inl",V("i")))),Typed(Num(0),Arrow(OS(),Q("Int"))))),false,"Initial columns begin with two defects left and retain the original class multiplicities."),
        Node("terminal","terminal",Eq(Typed(Own("terminal"),Arrow(S(),Q("Int"))),Call("Sum.elim",Typed(Num(0),Vec()),Old("terminal"))),false,"Only the zero-budget sector contributes at the terminal boundary."),
        Node("coefficients","coefficients",Eq(Typed(Own("coefficients"),Arrow(Fin(Num(21)),Q("Int"))),Matrix(new Formula[]{Num(-512L),Num("9216"),Num(-71424L),Num("307392"),Num(-774528L),Num("1014720"),Num(-28632L),Num(-2236608L),Num("3547332"),Num(-1660207L),Num(-1956780L),Num("3520224"),Num(-2005784L),Num(-166467L),Num("997536"),Num(-718624L),Num("282276"),Num(-68685L),Num("10468"),Num(-960L),Num("48")})),false,"Coefficients are listed from the smallest power to the largest power."))));
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
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula If(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,y,Sp,Q("else"),Sp,n));
    private static Formula Matrix(params Formula[][] rows)
    {
        var a=new List<Formula>{Begin,Grp(F.Id("pmatrix"))};
        for(int i=0;i<rows.Length;i++) {if(i>0)a.Add(RowBreak);for(int j=0;j<rows[i].Length;j++){if(j>0)a.Add(Amp);a.Add(rows[i][j]);}}
        a.AddRange([End,Grp(F.Id("pmatrix"))]);return Seq(a.ToArray());
    }

    private static Formula Num(string n) => D(n.Select(c => (byte)(c-'0')).ToArray());
    private static Formula Num(long n) => n < 0 ? Parenthesized(Seq(Minus,Num(-n))) : new Formula.Number(n);
    private static Formula Owner(string n, params Formula[] a) => Call("HardinA233260Literal."+n,a);
    private static Formula Old(string n, params Formula[] a) => Call("HardinA229590StripData."+n,a);
    private static Formula Own(string n, params Formula[] a) => Call(LeanPrefix+n,a);
    private static Formula Vec() => Arrow(Fin(Num(41)),Q("Int"));
    private static Formula OS() => Call("Sum",Fin(Num(41)),Fin(Num(41)));
    private static Formula S() => Call("Sum",Fin(Num(41)),OS());

}
