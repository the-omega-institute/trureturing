using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class MarkedSuffixAgreementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/MarkedSuffixAgreement.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A good terminal marker flag forces higher input and output coefficients to agree.", H("Marked Suffix Agreement"), Blocks(
        Describe.Lean(DescribeId.Create("pd-markedsuffixagreement-marked-suffix-agreement"),
            DeclarationHandle.Create(Prefix + "marked_suffix_agreement"), H("Agreement above the selected marker"),
            StatementSource.FromAuthor(AgreementFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The starting marker has already selected its lowest positive digit, so its mode is one, two, three or four. If the final bad flag is zero, every later input coefficient equals its output coefficient and the starting bad flag is zero. Slots three through six, which store the marker parity, retention flag and the two tail phases, keep their starting values throughout the path."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula DottedCall(string owner, string member, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(member))), [.. args]);
    private static Formula OptionalIndex(Formula xs, Formula i) =>
        Call("ite", new Formula.Relation(i, FormulaRelationOperator.LessThan,
            DottedCall("List", "length", xs)),
            Call("some", DottedCall("GetElem", "getElem", xs, i)), Call("none"));

    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));



    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula Entry(Formula f,int k) => Call("getD",OptionalIndex(f,new Formula.Number(k)),D(0));

    private static Formula AgreementFormula()
    {
        var list=ListOf(Z());
        Formula Output(int k) => Call("pathOutputs",Seq(LambdaLower,Sp,OpenBracket,list,CloseBracket,Sp,
            OpenBracket,Alphabet(),CloseBracket,Sp,V("q"),Colon,list,Sp,Mapsto,Sp,
            Entry(Call("fst",Call("baseTable",Call("toNat",Entry(V("q"),0)))),k)),V("p"));
        var mode=Entry(V("s"),1);
        var marked=new Formula.Logic(Eqn(mode,D(1)),FormulaLogicOperator.Or,
            new Formula.Logic(Eqn(mode,D(2)),FormulaLogicOperator.Or,
            new Formula.Logic(Eqn(mode,D(3)),FormulaLogicOperator.Or,Eqn(mode,D(4)))));
        var data=All("k",N(),Imp(And(LeF(D(3),V("k")),LeF(V("k"),D(6))),
            Eqn(Call("getD",OptionalIndex(V("t"),V("k")),D(0)),
                Call("getD",OptionalIndex(V("s"),V("k")),D(0)))));
        var conclusion=And(Eqn(Entry(V("s"),7),D(0)),Eqn(Output(10),Output(12)),data);
        var path=Call("Path",Ty("prefixRawAutomaton"),V("s"),V("t"),V("xs"));
        return Disp(All("s",list,All("t",list,All("xs",ListOf(Alphabet()),All("p",path,
            Imp(And(marked,Eqn(Entry(V("t"),7),D(0))),conclusion))))));
    }
}
