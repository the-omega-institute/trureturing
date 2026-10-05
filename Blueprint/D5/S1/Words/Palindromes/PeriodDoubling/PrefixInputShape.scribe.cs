using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class PrefixInputShapeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/PrefixInputShape.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The marker modes recognize positive signed digits at positions separated by three.", H("Marked Input Shape"), Blocks(
        Describe.Lean(DescribeId.Create("pd-prefixinputshape-prefix-path-input-shape"),
            DeclarationHandle.Create(Prefix + "prefix_path_input_shape"), H("Input language of a completed marker"),
            StatementSource.FromAuthor(InputFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A path begins in marker mode zero and ends in mode four. Its input coefficients consist of an arbitrary lower tail, a nonempty repetition of the block [1,0,0], and at least one final zero. Coefficients are read least significant first. Modes one and two require the two zeros after a selected positive digit; mode three either starts the next block or ends the marker; mode four accepts only zeros."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula Fn(Formula from, Formula to) => Seq(from, Sp, To, Sp, to);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Prop() => Ty("Prop");
    private static Formula SetOf(Formula a) => Call("Set", a);
    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula NotF(Formula a) => new Formula.Not(a);
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula NegF(Formula a) => Call("neg", a);
    private static Formula At(Formula f, Formula x) => Call("val", f, x);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);
    private static Formula ListNil() => Seq(OpenBracket, CloseBracket);
    private static Formula Tuple(params Formula[] a) =>
        Parenthesized(a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Comma, Sp, y)));



    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula Entry(Formula f,int k) => Call("getD",Call("getElemOption",f,new Formula.Number(k)),D(0));
    private static Formula InputFormula()
    {
        var list=ListOf(Z());
        var q=V("q");
        var input=Entry(Call("fst",Call("baseTable",Call("toNat",Entry(q,0)))),10);
        var output=Call("pathOutputs",Seq(LambdaLower,Sp,OpenBracket,list,CloseBracket,Sp,
            OpenBracket,Alphabet(),CloseBracket,Sp,V("q"),Colon,list,Sp,Mapsto,Sp,input),V("p"));
        var block=Seq(OpenBracket,D(1),Comma,Sp,D(0),Comma,Sp,D(0),CloseBracket);
        var suffix=Call("flatten",Call("replicate",V("m"),block));
        var zeros=Call("replicate",Add(V("k"),D(1)),D(0));
        var shape=Call("append",Call("append",V("lower"),suffix),zeros);
        var conclusion=Ex("lower",list,Ex("m",N(),Ex("k",N(),And(LtF(D(0),V("m")),Eqn(output,shape)))));
        var path=Call("Path",Ty("prefixRawAutomaton"),V("s"),V("t"),V("xs"));
        return Disp(All("s",list,All("t",list,All("xs",ListOf(Alphabet()),All("p",path,
            Imp(And(Eqn(Entry(V("s"),1),D(0)),Eqn(Entry(V("t"),1),D(4))),conclusion))))));
    }
}
