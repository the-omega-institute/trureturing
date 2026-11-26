using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590;
internal sealed class HardinA229590StripDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/StatisticalMechanics/Potts/StripDefectsWide/A229590/HardinA229590Strip.";
    private const string LeanPrefix="D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590Strip.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five-row HA arrays with exactly one equal-colour bond.",H("Five-row one-defect strips"),Blocks(
        Paragraph(Text("Bonds join (i,j) to (i,j+1) and (i,j+1) to (i+1,j), within the array. The column sweep preserves these bonds; the canonical predicate always reads cells in row-major order. Exactly one bond has equal endpoint colours.")),
        Node("a","a",All("n",Q("Nat"),Eq(Own("a" ,V("n")),Call("Finset.card" ,Call("Finset.filter" ,Fn("A",Arrow(Call("Prod" ,Fin(Num("5")),Fin(V("n"))),Fin(Num("3"))),And(Eq(Call("DefectTransfer.defects" ,Typed(Call("Finset.empty"),Call("Finset" ,Call("Prod" ,Fin(Num("5")),Fin(Num("5"))))),Data("between"),Call("List.ofFn" ,Fn("j",Fin(V("n")),Fn("i",Fin(Num("5")),App(V("A"),Pair(V("i"),V("j"))))))),Num("1")),All("p",Call("Prod" ,Fin(Num("5")),Fin(V("n"))),All("c",Fin(Num("3")),Imp(Lt(V("c"),App(V("A"),V("p"))),Ex("q",Call("Prod" ,Fin(Num("5")),Fin(V("n"))),And(Lt(Add(Mul(Val(Call("Prod.fst" ,V("q"))),V("n")),Val(Call("Prod.snd" ,V("q")))),Add(Mul(Val(Call("Prod.fst" ,V("p"))),V("n")),Val(Call("Prod.snd" ,V("p"))))),Eq(App(V("A"),V("q")),V("c"))))))))),Call("Finset.univ"))))),false,"All arrays are filtered by exactly one equal-colour bond and literal row-major colour introduction. The rank of (i,j) is i*n+j."),
        Node("finite_certificate","finite certificate",And(All("p",Owner("Col"),All("d",Fin(Num("2")),All("s",S(),Eq(Sum("r",Row(),If(And(Le(Data("cross" ,V("p"),V("r")),Val(V("d"))),Eq(Data("cl" ,Data("boundary" ,V("r")),Sub(Val(V("d")),Data("cross" ,V("p"),V("r")))),V("s"))),Typed(Num("1"),Q("Int")),Typed(Num("0"),Q("Int")))),Data("T" ,Data("cl" ,V("p"),Val(V("d"))),V("s")))))),And(All("s",S(),Eq(Sum("r",Row(),If(Eq(Data("cl" ,Data("boundary" ,V("r")),Num("1")),V("s")),Typed(Num("1"),Q("Int")),Typed(Num("0"),Q("Int")))),Data("initial" ,V("s")))),Eq(Call("Matrix.mulVec" ,Power(Data("T"),Add(Num("4"),Num("14"))),Data("terminal")),Sum("j",Fin(Num("14")),Call("HSMul.hSMul" ,App(Vector(Parenthesized(Seq(Minus,Num("64"))),Num("768"),Parenthesized(Seq(Minus,Num("3648"))),Num("8336"),Parenthesized(Seq(Minus,Num("7472"))),Parenthesized(Seq(Minus,Num("5464"))),Num("18879"),Parenthesized(Seq(Minus,Num("14888"))),Parenthesized(Seq(Minus,Num("816"))),Num("9016"),Parenthesized(Seq(Minus,Num("6494"))),Num("2200"),Parenthesized(Seq(Minus,Num("384"))),Num("32")),V("j")),Call("Matrix.mulVec" ,Power(Data("T"),Add(Num("4"),Val(V("j")))),Data("terminal"))))))),true,"The transfer sums, initial multiplicities and terminal-vector polynomial give an exact finite counting identity."),
        Node("result","result",All("n",Q("Nat"),Eq(Typed(Own("a" ,Add(V("n"),Num("19"))),Q("Int")),Sub(Add(Sub(Add(Sub(Sub(Add(Sub(Sub(Add(Sub(Add(Sub(Mul(Num("32"),Typed(Own("a" ,Add(V("n"),Num("18"))),Q("Int"))),Mul(Num("384"),Typed(Own("a" ,Add(V("n"),Num("17"))),Q("Int")))),Mul(Num("2200"),Typed(Own("a" ,Add(V("n"),Num("16"))),Q("Int")))),Mul(Num("6494"),Typed(Own("a" ,Add(V("n"),Num("15"))),Q("Int")))),Mul(Num("9016"),Typed(Own("a" ,Add(V("n"),Num("14"))),Q("Int")))),Mul(Num("816"),Typed(Own("a" ,Add(V("n"),Num("13"))),Q("Int")))),Mul(Num("14888"),Typed(Own("a" ,Add(V("n"),Num("12"))),Q("Int")))),Mul(Num("18879"),Typed(Own("a" ,Add(V("n"),Num("11"))),Q("Int")))),Mul(Num("5464"),Typed(Own("a" ,Add(V("n"),Num("10"))),Q("Int")))),Mul(Num("7472"),Typed(Own("a" ,Add(V("n"),Num("9"))),Q("Int")))),Mul(Num("8336"),Typed(Own("a" ,Add(V("n"),Num("8"))),Q("Int")))),Mul(Num("3648"),Typed(Own("a" ,Add(V("n"),Num("7"))),Q("Int")))),Mul(Num("768"),Typed(Own("a" ,Add(V("n"),Num("6"))),Q("Int")))),Mul(Num("64"),Typed(Own("a" ,Add(V("n"),Num("5"))),Q("Int")))))),true,"For every natural n, the literal count at n+19 satisfies the stated fourteen-lag recurrence. Coordinate exchange counts the same labelled arrays. Colour relabelling gives six labelled arrays for each canonical representative."))));

    private static DocumentBlock Node(string name,string title,Formula f,bool theorem,string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_","-").ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),H(title),
          StatementSource.FromAuthor(Disp(f)),
          name == "a"
            ? AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229590"))
            : AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229590")),
          Blocks(Paragraph(Text(prose))),theorem ? DescribeRole.Theorem : DescribeRole.Definition,
          name == "result" ? new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin229590"), ResolutionKind.Proved) : null);
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
    private static Formula Own(string name, params Formula[] args) =>
        Call(LeanPrefix + name, args);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula App(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula x, Formula type) =>
        Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Vector(params Formula[] a) => Matrix(a);
    private static Formula Sum(string n, Formula t, Formula b) => Seq(F.Sum,Underscore,Grp(V(n),Colon,Sp,t),Sp,Parenthesized(b));
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
    private static Formula Data(string n, params Formula[] a) => Call("HardinA229590StripData."+n,a);
    private static Formula S() => Call("Sum",Fin(Num(41)),Fin(Num(41)));
    private static Formula Row() => Arrow(Fin(Num(5)),Fin(Num(3)));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a,Comma,Sp,b));
    private static Formula Tuple(params Formula[] a) => a.Length==2 ? Pair(a[0],a[1]) : Pair(a[0],Tuple(a.Skip(1).ToArray()));
}
