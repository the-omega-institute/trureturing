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
            Blocks(Paragraph(Text("For a path starting in an initial state, slot one is the parity of the next signed-digit position. The first emitted digit is the dummy digit at position minus one, so the parity is the path length plus one modulo two. Slots two and three retain the endpoint parities. For either stream the current and previous digit slots are entries zero and one of the reversed emitted list, with zero used when an entry is absent. The last-sign slot is the last nonzero emitted digit, also with default zero. These identities apply at intermediate states as well as accepting states. The last-option expression is none for an empty list and some(List.getLast(...)) otherwise; the nonempty proof argument is implicit."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula DottedCall(string owner, string member, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(member))), [.. args]);
    private static Formula OptionalIndex(Formula xs, Formula i) =>
        Call("ite", new Formula.Relation(i, FormulaRelationOperator.LessThan,
            DottedCall("List", "length", xs)),
            Call("some", DottedCall("GetElem", "getElem", xs, i)), Call("none"));

    private static Formula LastOption(Formula xs) =>
        Ite(Eqn(xs, ListNil()), Ty("none"), Call("some",
            new Formula.Apply(Seq(Operatorname, Grp(V("List"), Dot, V("getLast"))), [xs])));
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);
    private static Formula ListNil() => Seq(
        OpenBracket, CloseBracket);



    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());

    private static Formula MemoryFormula()
    {
        var fin=Call("Fin",D(1,4,9,2));
        var automaton=Call("baseAutomaton",V("charge"));
        var input=Ite(V("output"),D(1,2),D(1,0));
        var previous=Ite(V("output"),D(1,3),D(1,1));
        var last=Ite(V("output"),D(1,7),D(1,6));
        Formula Slot(Formula q, Formula k) => Call("getD",OptionalIndex(Call("fst",Call("baseTable",Call("val",q))),k),D(0));
        var ds=Call("pathOutputs",Seq(LambdaLower,Sp,OpenBracket,fin,CloseBracket,Sp,
            OpenBracket,Alphabet(),CloseBracket,Sp,V("q"),Colon,fin,Sp,Mapsto,Sp,Slot(V("q"),input)),V("p"));
        Formula LastDigit(int k) => Call("getD",OptionalIndex(Call("reverse",ds),new Formula.Number(k)),D(0));
        var filtered=Call("filter",Lam("z",Z(),Ne(V("z"),D(0))),ds);
        var stream=All("output",Ty("Bool"),And(Eqn(Slot(V("t"),input),LastDigit(0)),
            Eqn(Slot(V("t"),previous),LastDigit(1)),
            Eqn(Slot(V("t"),last),Call("getD",LastOption(filtered),D(0)))));
        var result=And(Eqn(Slot(V("t"),D(1)),Cast(Call("mod",Add(Call("length",V("xs")),D(1)),D(2)),Z())),
            Eqn(Slot(V("t"),D(2)),Slot(V("s"),D(2))),Eqn(Slot(V("t"),D(3)),Slot(V("s"),D(3))),stream);
        return Disp(All("charge",Ty("Bool"),All("s",fin,All("t",fin,All("xs",ListOf(Alphabet()),
            All("p",Call("Path",automaton,V("s"),V("t"),V("xs")),
                Imp(Mem(V("s"),Call("start",automaton)),result)))))));
    }
}
