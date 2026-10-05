using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class BaseLastSignMemoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/BaseLastSignMemory.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The most recent sign memory equals the last nonzero emitted coefficient.", H("Literal Most Recent Sign Memory"), Blocks(
        Describe.Lean(DescribeId.Create("pd-baselastsignmemory-base-path-last-sign"),
            DeclarationHandle.Create(Prefix + "base_path_last_sign"), H("The literal minimum-position transition law"),
            StatementSource.FromAuthor(CutFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For either emitted stream, each literal base edge updates the most recent sign when its new coefficient is nonzero. Induction along an arbitrary source path identifies the terminal memory with the last nonzero coefficient of the emitted stream. All source memories start at zero, and absent last entries use default zero. Acceptance and tightness are unnecessary; this statement also applies to the partial path before a marker is selected."))), DescribeRole.Theorem))));
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


    private static Formula Pair() => Product(N(),N());
    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula Ints(params Formula[] xs) => Seq(OpenBracket,xs.Skip(1).Aggregate(xs[0],(a,b)=>Seq(a,Comma,Sp,b)),CloseBracket);
    private static Formula Entry(Formula s, int k) => Call("getD",Call("getElemOption",s,new Formula.Number(k)),D(0));
    private static Formula Fold(Formula xs, Formula elem, Formula value, Formula term) =>
        Call("foldr",Seq(LambdaLower,Sp,V("a"),Colon,elem,Sp,V("x"),Colon,value,Sp,Mapsto,Sp,
            Add(term,Mul(D(2),V("x")))),D(0),xs);
    private static Formula CutFormula()
    {
        var fin=Call("Fin",D(1,4,9,2));
        var M=Call("baseAutomaton",V("charge"));
        Formula EntryAt(Formula x,Formula i) => Call("getD",Call("getElemOption",x,i),D(0));
        var coeff=EntryAt(Call("fst",Call("baseTable",Call("val",V("q")))),Ite(V("output"),new Formula.Number(12),new Formula.Number(10)));
        var stream=Call("pathOutputs",Seq(LambdaLower,Sp,OpenBracket,fin,CloseBracket,Sp,
            OpenBracket,Alphabet(),CloseBracket,Sp,V("q"),Colon,fin,Sp,Mapsto,Sp,coeff),V("p"));
        var nz=Call("filter",Lam("z",Z(),Call("bne",V("z"),D(0))),stream);
        var last=Call("getD",Call("getLastOption",nz),D(0));
        var memory=EntryAt(Call("fst",Call("baseTable",Call("val",V("t")))),Ite(V("output"),new Formula.Number(17),new Formula.Number(16)));
        var body=Imp(Mem(V("s"),Call("start",M)),All("p",Call("Path",M,V("s"),V("t"),V("xs")),Eqn(memory,last)));
        return Disp(All("charge",Ty("Bool"),All("output",Ty("Bool"),All("s",fin,All("t",fin,All("xs",ListOf(Alphabet()),body))))));
    }
}
