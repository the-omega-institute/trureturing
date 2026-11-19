using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698;
internal sealed class HardinA229698StripDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229698/HardinA229698Strip.";
    private const string LeanPrefix="D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698Strip.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five-row HA arrays with exactly two equal-colour bonds.",H("Five-row two-defect strips"),Blocks(
        Paragraph(Text("Bonds join (i,j) to (i,j+1) and (i,j+1) to (i+1,j), within the array. Exactly two bonds have equal endpoint colours. The canonical predicate reads cells in literal row-major order, of rank i*n+j.")),
        Node("a","a",All("n",Q("Nat"),Eq(Own("a" ,V("n")),Call("Finset.card" ,Call("Finset.filter" ,Fn("A",Arrow(Call("Prod" ,Fin(Num("5")),Fin(V("n"))),Fin(Num("3"))),And(Eq(Call("DefectTransfer.defects" ,Typed(Call("Finset.empty"),Call("Finset" ,Call("Prod" ,Fin(Num("5")),Fin(Num("5"))))),Old("between"),Call("List.ofFn" ,Fn("j",Fin(V("n")),Fn("i",Fin(Num("5")),App(V("A"),Pair(V("i"),V("j"))))))),Num("2")),All("p",Call("Prod" ,Fin(Num("5")),Fin(V("n"))),All("c",Fin(Num("3")),Imp(Lt(V("c"),App(V("A"),V("p"))),Ex("q",Call("Prod" ,Fin(Num("5")),Fin(V("n"))),And(Lt(Add(Mul(Val(Call("Prod.fst" ,V("q"))),V("n")),Val(Call("Prod.snd" ,V("q")))),Add(Mul(Val(Call("Prod.fst" ,V("p"))),V("n")),Val(Call("Prod.snd" ,V("p"))))),Eq(App(V("A"),V("q")),V("c"))))))))),Call("Finset.univ"))))),false,"All arrays are filtered by exactly two equal-colour bonds and literal row-major colour introduction. The rank of (i,j) is i*n+j."),
        Node("finite_certificate","finite certificate",And(All("p",Owner("Col"),All("d",Fin(Num(3)),All("s",S(),Eq(Sum("r",Row(),If(And(Le(Old("cross",V("p"),V("r")),Val(V("d"))),Eq(Data("cl",Old("boundary",V("r")),Sub(Val(V("d")),Old("cross",V("p"),V("r")))),V("s"))),Typed(Num(1),Q("Int")),Typed(Num(0),Q("Int")))),Data("T",Data("cl",V("p"),Val(V("d"))),V("s")))))),And(All("s",S(),Eq(Sum("r",Row(),If(Eq(Data("cl",Old("boundary",V("r")),Num(2)),V("s")),Typed(Num(1),Q("Int")),Typed(Num(0),Q("Int")))),Data("initial",V("s")))),Eq(Call("Matrix.mulVec",Power(Data("T"),Add(Num(6),Num(21))),Data("terminal")),Sum("j",Fin(Num(21)),Smul(Data("coefficients",V("j")),Call("Matrix.mulVec",Power(Data("T"),Add(Num(6),Val(V("j")))),Data("terminal"))))))),true,"The two counting identities and the terminal-vector polynomial determine the exact count."),
        Node("result","result",All("n",Q("Nat"),Eq(Call("Int.ofNat",Own("a",Add(V("n"),Num(28)))),Sub(Add(Sub(Add(Sub(Add(Sub(Sub(Add(Sub(Sub(Add(Sub(Sub(Add(Sub(Add(Sub(Add(Sub(Mul(Num(48),Call("Int.ofNat",Own("a",Add(V("n"),Num(27))))),Mul(Num(960),Call("Int.ofNat",Own("a",Add(V("n"),Num(26)))))),Mul(Num(10468),Call("Int.ofNat",Own("a",Add(V("n"),Num(25)))))),Mul(Num(68685),Call("Int.ofNat",Own("a",Add(V("n"),Num(24)))))),Mul(Num(282276),Call("Int.ofNat",Own("a",Add(V("n"),Num(23)))))),Mul(Num(718624),Call("Int.ofNat",Own("a",Add(V("n"),Num(22)))))),Mul(Num(997536),Call("Int.ofNat",Own("a",Add(V("n"),Num(21)))))),Mul(Num(166467),Call("Int.ofNat",Own("a",Add(V("n"),Num(20)))))),Mul(Num(2005784),Call("Int.ofNat",Own("a",Add(V("n"),Num(19)))))),Mul(Num(3520224),Call("Int.ofNat",Own("a",Add(V("n"),Num(18)))))),Mul(Num(1956780),Call("Int.ofNat",Own("a",Add(V("n"),Num(17)))))),Mul(Num(1660207),Call("Int.ofNat",Own("a",Add(V("n"),Num(16)))))),Mul(Num(3547332),Call("Int.ofNat",Own("a",Add(V("n"),Num(15)))))),Mul(Num(2236608),Call("Int.ofNat",Own("a",Add(V("n"),Num(14)))))),Mul(Num(28632),Call("Int.ofNat",Own("a",Add(V("n"),Num(13)))))),Mul(Num(1014720),Call("Int.ofNat",Own("a",Add(V("n"),Num(12)))))),Mul(Num(774528),Call("Int.ofNat",Own("a",Add(V("n"),Num(11)))))),Mul(Num(307392),Call("Int.ofNat",Own("a",Add(V("n"),Num(10)))))),Mul(Num(71424),Call("Int.ofNat",Own("a",Add(V("n"),Num(9)))))),Mul(Num(9216),Call("Int.ofNat",Own("a",Add(V("n"),Num(8)))))),Mul(Num(512),Call("Int.ofNat",Own("a",Add(V("n"),Num(7)))))))),true,"For every natural n the literal count at n+28 satisfies the stated twenty-one-lag recurrence. The colour action has six labelled arrays per canonical representative because a constant array has either zero or at least nine monochromatic bonds."))));
    private static DocumentBlock Node(string name,string title,Formula f,bool theorem,string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_","-").ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),H(title),
          StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229698")),
          Blocks(Paragraph(Text(prose))),theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    private static Formula Ex(string n, Formula t, Formula b) => Seq(Exists,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula Lt(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
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
    private static Formula Num(string n) => D(n.Select(c => (byte)(c-'0')).ToArray());
    private static Formula Num(long n) => n < 0 ? Parenthesized(Seq(Minus,Num(-n))) : new Formula.Number(n);
    private static Formula Owner(string n, params Formula[] a) => Call("HardinA233260Literal."+n,a);
    private static Formula Old(string n, params Formula[] a) => Call("HardinA229590StripData."+n,a);
    private static Formula Data(string n, params Formula[] a) => Call("HardinA229698StripData."+n,a);
    private static Formula Own(string n, params Formula[] a) => Call(LeanPrefix+n,a);
    private static Formula OS() => Call("Sum",Fin(Num(41)),Fin(Num(41)));
    private static Formula S() => Call("Sum",Fin(Num(41)),OS());
    private static Formula Row() => Arrow(Fin(Num(5)),Fin(Num(3)));
    private static Formula Val(Formula x) => Call("Fin.val",x);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a,Comma,Sp,b));
    private static Formula Sum(string n, Formula t, Formula x) => Seq(F.Sum,Underscore,Grp(V(n),Colon,Sp,t),Sp,Parenthesized(x));
    private static Formula And(Formula a,Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.And,Parenthesized(b));
    private static Formula Le(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Add,Parenthesized(b));
    private static Formula Sub(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Subtract,Parenthesized(b));
    private static Formula Mul(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Multiply,Parenthesized(b));
    private static Formula Smul(Formula a,Formula b) => Call("HSMul.hSMul",a,b);
    private static Formula Power(Formula a,Formula b) => new Formula.Power(a,b);

}
