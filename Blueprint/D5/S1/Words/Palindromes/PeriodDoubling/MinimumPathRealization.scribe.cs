using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class MinimumPathRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/MinimumPathRealization.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every base path lifts to the complete product graph and records exactly its lowest-position escape events.", H("Complete Lowest-Position Product Realization"), Blocks(
        Describe.Lean(DescribeId.Create("pd-minimumpathrealization-minimum-path-realization"),
            DeclarationHandle.Create(Prefix + "minimum_path_realization"), H("The product flag is the event disjunction"),
            StatementSource.FromAuthor(RealizationFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The lift preserves each of the four labels and the initial and final base-state indices. It starts with a false flag. Its final flag equals the Boolean disjunction of the path events: no input nonzero has yet been recorded, the current input digit is zero, and the current output digit is nonzero. No accepting-endpoint premise is needed for path construction; if the flag is true and the base endpoint accepts, the lifted path accepts in minimumAutomaton. any is Boolean list disjunction, id is the Boolean identity, and the anonymous bracket in the event lambda represents the unused edge-label argument."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula BooleanEq(Formula a, Formula b) =>
        Seq(Open, a, Sp, Eq, Eq, Sp, b, Close);
    private static Formula BooleanNe(Formula a, Formula b) =>
        Seq(Open, a, Sp, Bang, Eq, Sp, b, Close);

    private static Formula OptionalIndex(Formula xs, Formula i) =>
        Call("ite", new Formula.Relation(i, FormulaRelationOperator.LessThan,
            DottedCall("List", "length", xs)),
            Call("some", DottedCall("GetElem", "getElem", xs, i)), Call("none"));

    private static Formula DottedCall(string owner, string member, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(owner), Dot, V(member))), [.. args]);

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
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));


    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula RealizationFormula()
    {
        var baseFin=Call("Fin",D(1,4,9,2));var productFin=Call("Fin",D(1,7,1,0));
        var baseGraph=Call("baseAutomaton",V("true"));var productGraph=V("minimumAutomaton");
        Formula Row(Formula x) => Call("minimumTable",Call("val",x));
        Formula State(Formula x) => Call("fst",Call("baseTable",Call("val",x)));
        Formula Entry(Formula x,int k) => Call("getD",OptionalIndex(x,new Formula.Number(k)),D(0));
        var eventLambda=Seq(LambdaLower,Sp,V("s0"),Colon,baseFin,Sp,OpenBracket,Alphabet(),CloseBracket,Sp,
            V("q"),Colon,baseFin,Sp,Mapsto,Sp,
            DottedCall("Bool", "and",DottedCall("Bool", "and",BooleanEq(Entry(State(V("s0")),14), D(0)),
                BooleanEq(Entry(State(V("q")),10), D(0))),BooleanNe(Entry(State(V("q")),12), D(0))));
        var events=Call("any",V("id"),Call("pathOutputs",eventLambda,V("p")));
        var body=Ex("u",productFin,Ex("v",productFin,And(Mem(V("u"),Call("start",productGraph)),
            Eqn(Call("fst",Row(V("u"))),Call("val",V("s"))),Eqn(Call("fst",Row(V("v"))),Call("val",V("t"))),
            Call("Nonempty",Call("Path",productGraph,V("u"),V("v"),V("xs"))),
            Eqn(Call("fst",Call("snd",Row(V("v")))),events))));
        return Disp(All("s",baseFin,All("t",baseFin,All("xs",ListOf(Alphabet()),
            Imp(Mem(V("s"),Call("start",baseGraph)),All("p",Call("Path",baseGraph,V("s"),V("t"),V("xs")),body))))));
    }
}
