using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5a;

internal sealed class HardinA229641StripCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5a/HardinA229641StripCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite vector relation for two-defect HDA strips", H("Finite vector relation for two-defect HDA strips"), Blocks(
            Paragraph(Text("Continuation counts are resolved by the number of remaining monochromatic bonds. Zero-defect continuations follow the five-row proper-colouring transfer.")),
            Node("twoDefect", TwoDefect(), false, "This entry is one exactly when a cut contains two monochromatic bonds."),
            Node("transfer", Transfer(), false, "The left summand has budget two. The inherited right summand has budgets one and zero."),
            Node("terminal", Terminal(), false, "An empty continuation requires a remaining budget of zero."),
            Node("coefficients641",Coefficients(),false,"The entries are ordered from the smallest shift of the recurrence to the largest."),
            Node("vector_polynomial",Polynomial(),true,"The relation holds simultaneously for all boundary columns and all three residual budgets."))));

    private static DocumentBlock Node(string name, Formula statement, bool theorem, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_","-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name), H(name), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229641")),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula N(long n) => n<0 ? Parenthesized(Seq(Minus,N(-n))) : new Formula.Number(n);
    private static Formula V(string n) => F.Id(n);
    private static Formula Q(string n) => Seq(n.Split('.').SelectMany((p,i)=>i==0?new[]{Seq(Operatorname,Grp(V(p)))}:new[]{Dot,Seq(Operatorname,Grp(V(p)))}).ToArray());
    private static Formula Call(string n, params Formula[] a) => a.Length==0?Q(n):new Formula.Apply(Q(n),[..a]);
    private static Formula Parenthesized(Formula a) => Seq(Open,a,Close);
    private static Formula Typed(Formula a,Formula t) => Parenthesized(Seq(a,Colon,Sp,t));
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Fin(int n) => Call("Fin",N(n));
    private static Formula Val(Formula a) => Call("Fin.val",a);
    private static Formula Eq(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Add(Formula a,Formula b) => new Formula.Binary(Parenthesized(a),FormulaBinaryOperator.Add,Parenthesized(b));
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,Typed(V(n),t),Comma,Sp,Parenthesized(b));
    private static Formula If(Formula c,Formula a,Formula b) =>
        Parenthesized(Seq(Q("if"),Sp,Parenthesized(c),Sp,Q("then"),Sp,a,Sp,Q("else"),Sp,b));
    private static Formula AsInt(Formula a) => Typed(a,Q("Int"));
    private static Formula SumOver(string n,Formula t,Formula body) =>
        Seq(F.Sum,Underscore,Grp(Typed(V(n),t)),Sp,Parenthesized(body));
    private static Formula Pow(Formula a,Formula b) => Seq(Parenthesized(a),Caret,Grp(b));
    private static Formula VectorLiteral(long[] entries)
    {
        Formula tail = Q("Matrix.vecEmpty");
        for (int i = entries.Length - 1; i >= 0; i--)
            tail = Call("Matrix.vecCons", N(entries[i]), tail);
        return tail;
    }
    private static Formula Column() => Q("HardinA233178Chromatic.Column");
    private static Formula M(Formula s) => Call("Matrix",s,s,Q("Int"));
    private static Formula D(string n,params Formula[] a) => Call("HardinA229538StripData."+n,a);
    private static Formula C(string n,params Formula[] a) => Call("HardinA233178Chromatic."+n,a);

    private static Formula Cert(string n,params Formula[] a) => Call("HardinA229641StripCertificate."+n,a);
    private static Formula Coefficients() =>
        Eq(Typed(Cert("coefficients641"),Arrow(Fin(30),Q("Int"))),VectorLiteral([-46656, 279936, 186624, -4611168, 7359984, 21460464, -73617984, 9610272, 227616084, -273411640, -168525432, 522690894, -138135927, -412178619, 287096430, 147888798, -190067859, -12632640, 66347438, -7797810, -13478352, 2851598, 1614489, -424479, -108707, 31983, 3468, -1191, -15, 18]));
    private static Formula Polynomial() {
        Formula Power(Formula n)=>Call("Matrix.mulVec",Pow(Cert("transfer"),n),Cert("terminal"));
        return Eq(Power(N(33)),SumOver("k",Fin(30),
            Call("SMul.smul",Cert("coefficients641",V("k")),Power(Add(N(3),Val(V("k")))))));
    }

    private static Formula Budgets01() => Call("Sum",Column(),Column());
    private static Formula Budgets012() => Call("Sum",Column(),Budgets01());
    private static Formula TwoDefect() => All("p",Column(),All("q",Column(),
        Eq(AsInt(Cert("twoDefect",V("p"),V("q"))),If(Eq(D("cost",V("p"),V("q")),N(2)),N(1),N(0)))));
    private static Formula Transfer() => Eq(Typed(Cert("transfer"),M(Budgets012())),
        Call("Matrix.fromBlocks",C("T"),Call("Matrix.fromCols",D("oneDefect"),Cert("twoDefect")),
            Typed(N(0),Call("Matrix",Budgets01(),Column(),Q("Int"))),D("transfer")));
    private static Formula Terminal() => Eq(Typed(Cert("terminal"),Arrow(Budgets012(),Q("Int"))),
        Call("Sum.elim",Typed(N(0),Arrow(Column(),Q("Int"))),D("terminal")));
}
