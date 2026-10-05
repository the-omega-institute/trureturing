using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class BaseClassStreamsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/BaseClassStreams.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both signed streams of any path ending at a valid charge-mode goal forbid opposite digits at distance two.", H("Class Spacing of Transducer Outputs"), Blocks(
        Describe.Lean(DescribeId.Create("pd-baseclassstreams-classrowcheck"),
            DeclarationHandle.Create(Prefix + "classRowCheck"), H("Digit memories and persistent class flag"),
            StatementSource.FromAuthor(RowFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The checker tests both shifted digit memories, immediate rejection of an input violation, and backward propagation of the output violation flag on every base edge."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-baseclassstreams-base-path-class-spacing"),
            DeclarationHandle.Create(Prefix + "base_path_class_spacing"), H("No opposite signs two digit positions apart"),
            StatementSource.FromAuthor(ClassFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("output selects target component 12 when true and component 10 when false. Zip the digit stream with its tail. Consecutive pairs (a,b) and (b,c) satisfy a times c unequal to minus one. Together with the sparse signed-digit property, this is the class S condition that consecutive nonzero digits of opposite signs have gap at least three. The input transducer rejects violations immediately. The output stores a persistent violation flag, which is zero at every charge-mode accepting goal. Induction propagates that flag backwards and reconstructs each triple from the two digit memories. This result does not assert completeness for actual palindrome cuts."))), DescribeRole.Theorem))));

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


    private static Formula Alphabet() => Product(Z(), Z(), Z(), Z());
    private static Formula Entry(Formula s,int k) => Call("getD",Call("getElemOption",s,new Formula.Number(k)),D(0));
    private static Formula RowFormula()
    {
        var state=Call("fst",Call("baseTable",V("i")));
        var target=Call("fst",Call("baseTable",Call("fst",V("e"))));
        var rule=And(Eqn(Entry(target,11),Entry(state,10)),Eqn(Entry(target,13),Entry(state,12)),
            Ne(Mul(Entry(target,10),Entry(state,11)),NegF(D(1))),
            Imp(Eqn(Entry(target,18),D(0)),And(Eqn(Entry(state,18),D(0)),
                Ne(Mul(Entry(target,12),Entry(state,13)),NegF(D(1))))));
        var edges=Call("fst",Call("snd",Call("baseTable",V("i"))));
        return Disp(All("i",N(),Eqn(Call("classRowCheck",V("i")),
            Call("all",Lam("e",Product(N(),Z(),Z(),Z(),Z()),Call("decide",rule)),edges))));
    }
    private static Formula ClassFormula()
    {
        var auto = Call("baseAutomaton", Ty("true"));
        var state = Call("fst", Call("baseTable", Call("val", V("q"))));
        var digit = Call("getD", Call("getElemOption", state, Ite(V("output"), D(1,2), D(1,0))), D(0));
        var emit = Seq(LambdaLower, Sp, OpenBracket, Call("Fin", D(1,4,9,2)), CloseBracket, Sp,
            OpenBracket, Alphabet(), CloseBracket, Sp, V("q"), Colon, Call("Fin", D(1,4,9,2)),
            Sp, Mapsto, Sp, digit);
        var stream = Call("pathOutputs", auto, emit, V("p"));
        var rel = Lam("a", Product(Z(),Z()), Lam("b", Product(Z(),Z()),
            Ne(Mul(Call("fst", V("a")), Call("snd", V("b"))), NegF(D(1)))));
        var body = All("p", Call("Path", auto, V("s"), V("t"), V("xs")),
            Call("IsChain", Call("zip", stream, Call("tail", stream)), rel));
        body = Imp(Mem(V("t"), Call("accept", auto)), body);
        return Disp(All("output", Ty("Bool"), All("s", Call("Fin", D(1,4,9,2)),
            All("t", Call("Fin", D(1,4,9,2)), All("xs", ListOf(Alphabet()), body)))));
    }
}
