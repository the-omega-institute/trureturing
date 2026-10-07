using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class UnmarkedFlipSemanticsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/UnmarkedFlipSemantics.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unmarked flip flag records pointwise negation of the lower signed streams.", H("Unmarked Flip Semantics"), Blocks(
        Describe.Lean(DescribeId.Create("pd-unmarkedflipsemantics-unmarked-path-flip-semantics"),
            DeclarationHandle.Create(Prefix + "unmarked_path_flip_semantics"), H("Exact meaning of the persistent flip flag"),
            StatementSource.FromAuthor(FlipFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A path ending in marker mode zero has remained unmarked throughout. Its final flip flag is nonzero exactly when the starting flag is nonzero and every emitted input/output coefficient pair sums to zero. The two streams have the same length because each transition emits one coefficient on each side. Starting with flip flag one therefore records exact negation of the whole lower signed tail."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula DottedCall(string owner, string member, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(member))), [.. args]);
    private static Formula OptionalIndex(Formula xs, Formula i) =>
        Call("ite", new Formula.Relation(i, FormulaRelationOperator.LessThan,
            DottedCall("List", "length", xs)),
            Call("some", DottedCall("GetElem", "getElem", xs, i)), Call("none"));

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
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));



    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula Entry(Formula f,int k) => Call("getD",OptionalIndex(f,new Formula.Number(k)),D(0));


    private static Formula FlipFormula()
    {
        var list=ListOf(Z());
        Formula Output(int k) => Call("pathOutputs",Seq(LambdaLower,Sp,OpenBracket,list,CloseBracket,Sp,
            OpenBracket,Alphabet(),CloseBracket,Sp,V("q"),Colon,list,Sp,Mapsto,Sp,
            Entry(Call("fst",Call("baseTable",Call("toNat",Entry(V("q"),0)))),k)),V("p"));
        var pairs=Call("zip",Output(10),Output(12));
        var negation=All("z",Product(Z(),Z()),Imp(Mem(V("z"),pairs),
            Eqn(Add(Call("fst",V("z")),Call("snd",V("z"))),D(0))));
        var body=IffF(Ne(Entry(V("t"),2),D(0)),And(Ne(Entry(V("s"),2),D(0)),negation));
        var path=Call("Path",Ty("prefixRawAutomaton"),V("s"),V("t"),V("xs"));
        return Disp(All("s",list,All("t",list,All("xs",ListOf(Alphabet()),All("p",path,
            Imp(Eqn(Entry(V("t"),1),D(0)),body))))));
    }
}
