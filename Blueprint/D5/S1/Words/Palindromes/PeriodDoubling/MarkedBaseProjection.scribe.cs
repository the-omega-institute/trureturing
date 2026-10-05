using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class MarkedBaseProjectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/MarkedBaseProjection.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Base Projection of Marked Paths.", H("Base Projection of Marked Paths"), Blocks(
        Describe.Lean(DescribeId.Create("pd-markedbaseprojection-marker-base-projection"),
            DeclarationHandle.Create(Prefix + "marker_base_projection"), H("Path projection and digit equality"),
            StatementSource.FromAuthor(ProjectionFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The underlying base index follows every raw marker transition. Starting from any valid base index, path induction constructs an indexed base path with the same labels. Its terminal index is exact, and its input and output signed-digit streams equal those observed through the raw marker states. toNat denotes integer conversion to a natural number, and getD uses zero for absent entries."))), DescribeRole.Theorem))));
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
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);



    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula Entry(Formula xs,Formula k) => Call("getD",OptionalIndex(xs,k),D(0));
    private static Formula ProjectionFormula()
    {
        var fin=Call("Fin",D(1,4,9,2));
        var graph=Call("baseAutomaton",V("charge"));
        var slot=Ite(V("output"),D(1,2),D(1,0));
        Formula Emitter(Formula type, Formula index) => Seq(LambdaLower,Sp,OpenBracket,type,CloseBracket,
            Sp,OpenBracket,Alphabet(),CloseBracket,Sp,V("r"),Colon,type,Sp,Mapsto,Sp,
            Entry(Call("fst",Call("baseTable",index)),slot));
        var raw=Call("pathOutputs",Emitter(ListOf(Z()),Call("toNat",Entry(V("r"),D(0)))),V("p"));
        var indexed=Call("pathOutputs",Emitter(fin,Call("val",V("r"))),V("q"));
        var result=Ex("v",fin,Ex("q",Call("Path",graph,V("u"),V("v"),V("xs")),And(
            Eqn(Entry(V("t"),D(0)),Cast(Call("val",V("v")),Z())),All("output",Ty("Bool"),Eqn(raw,indexed)))));
        return Disp(All("charge",Ty("Bool"),All("s",ListOf(Z()),All("t",ListOf(Z()),All("xs",ListOf(Alphabet()),
            All("p",Call("Path",V("prefixRawAutomaton"),V("s"),V("t"),V("xs")),All("u",fin,
                Imp(Eqn(Entry(V("s"),D(0)),Cast(Call("val",V("u")),Z())),result))))))));
    }
}
