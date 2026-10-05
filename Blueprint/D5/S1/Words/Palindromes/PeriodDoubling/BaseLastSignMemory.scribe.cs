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
            Blocks(Paragraph(Text("For either emitted stream, each literal base edge updates the most recent sign when its new coefficient is nonzero. Induction along an arbitrary source path identifies the terminal memory with the last nonzero coefficient of the emitted stream. All source memories start at zero, and absent last entries use default zero. Acceptance and tightness are unnecessary; this statement also applies to the partial path before a marker is selected. The last-option expression is none for an empty list and some(List.getLast(...)) otherwise; the nonempty proof argument is implicit."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula BooleanNe(Formula a, Formula b) =>
        Seq(Open, a, Sp, Bang, Eq, Sp, b, Close);

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
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula Ite(Formula c, Formula a, Formula b) => Call("ite", c, a, b);
    private static Formula ListNil() => Seq(OpenBracket, CloseBracket);


    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula CutFormula()
    {
        var fin=Call("Fin",D(1,4,9,2));
        var M=Call("baseAutomaton",V("charge"));
        Formula EntryAt(Formula x,Formula i) => Call("getD",OptionalIndex(x,i),D(0));
        var coeff=EntryAt(Call("fst",Call("baseTable",Call("val",V("q")))),Ite(V("output"),new Formula.Number(12),new Formula.Number(10)));
        var stream=Call("pathOutputs",Seq(LambdaLower,Sp,OpenBracket,fin,CloseBracket,Sp,
            OpenBracket,Alphabet(),CloseBracket,Sp,V("q"),Colon,fin,Sp,Mapsto,Sp,coeff),V("p"));
        var nz=Call("filter",Lam("z",Z(),BooleanNe(V("z"), D(0))),stream);
        var last=Call("getD",LastOption(nz),D(0));
        var memory=EntryAt(Call("fst",Call("baseTable",Call("val",V("t")))),Ite(V("output"),new Formula.Number(17),new Formula.Number(16)));
        var body=Imp(Mem(V("s"),Call("start",M)),All("p",Call("Path",M,V("s"),V("t"),V("xs")),Eqn(memory,last)));
        return Disp(All("charge",Ty("Bool"),All("output",Ty("Bool"),All("s",fin,All("t",fin,All("xs",ListOf(Alphabet()),body))))));
    }
}
