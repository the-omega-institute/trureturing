using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class BasePositionMemoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/BasePositionMemory.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Base states record the exact parity and recent signed digits of any path.", H("Base Position Memory"), Blocks(
        Describe.Lean(DescribeId.Create("pd-basepositionmemory-base-path-position-memory"),
            DeclarationHandle.Create(Prefix + "base_path_position_memory"), H("Exact position and digit memory"),
            StatementSource.FromAuthor(MemoryFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For a path starting in an initial state, slot one is the parity of the next signed-digit position. The first emitted digit is the dummy digit at position minus one, so the parity is the path length plus one modulo two. Slots two and three retain the endpoint parities. For either stream the current and previous digit slots are entries zero and one of the reversed emitted list, with zero used when an entry is absent. The last-sign slot is the last nonzero emitted digit, also with default zero. These identities apply at intermediate states as well as accepting states."))), DescribeRole.Theorem))));
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

    private static Formula MemoryFormula()
    {
        var fin=Call("Fin",D(1,4,9,2));
        var automaton=Call("baseAutomaton",V("charge"));
        var input=Ite(V("output"),D(1,2),D(1,0));
        var previous=Ite(V("output"),D(1,3),D(1,1));
        var last=Ite(V("output"),D(1,7),D(1,6));
        Formula Slot(Formula q, Formula k) => Call("getD",Call("getElemOption",Call("fst",Call("baseTable",Call("val",q))),k),D(0));
        var ds=Call("pathOutputs",Seq(LambdaLower,Sp,OpenBracket,fin,CloseBracket,Sp,
            OpenBracket,Alphabet(),CloseBracket,Sp,V("q"),Colon,fin,Sp,Mapsto,Sp,Slot(V("q"),input)),V("p"));
        Formula LastDigit(int k) => Call("getD",Call("getElemOption",Call("reverse",ds),new Formula.Number(k)),D(0));
        var filtered=Call("filter",Lam("z",Z(),Ne(V("z"),D(0))),ds);
        var stream=All("output",Ty("Bool"),And(Eqn(Slot(V("t"),input),LastDigit(0)),
            Eqn(Slot(V("t"),previous),LastDigit(1)),
            Eqn(Slot(V("t"),last),Call("getD",Call("getLastOption",filtered),D(0)))));
        var result=And(Eqn(Slot(V("t"),D(1)),Cast(Call("mod",Add(Call("length",V("xs")),D(1)),D(2)),Z())),
            Eqn(Slot(V("t"),D(2)),Slot(V("s"),D(2))),Eqn(Slot(V("t"),D(3)),Slot(V("s"),D(3))),stream);
        return Disp(All("charge",Ty("Bool"),All("s",fin,All("t",fin,All("xs",ListOf(Alphabet()),
            All("p",Call("Path",automaton,V("s"),V("t"),V("xs")),
                Imp(Mem(V("s"),Call("start",automaton)),result)))))));
    }
}
