using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class PrefixPathRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/PrefixPathRealization.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal marker transitions are represented completely by the finite product graph.", H("Complete Representation of Marker Paths"), Blocks(
        Describe.Lean(DescribeId.Create("pd-prefixpathrealization-prefixrawautomaton"),
            DeclarationHandle.Create(Prefix + "prefixRawAutomaton"), H("The marker transition graph before indexing"),
            StatementSource.FromAuthor(RawFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("States are lists of integer components and each step is one of the literal marker successors. This transition graph places no conditions on its endpoints: its start and accept sets are universal. A separate condition picks the source and final flags when a cut is realized. The four alphabet coordinates are the signed-weight charge, signed-digit charge and the two shifted input bits."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-prefixpathrealization-prefix-path-realization"),
            DeclarationHandle.Create(Prefix + "prefix_path_realization"), H("Every marker path stays in the finite graph"),
            StatementSource.FromAuthor(RealizationFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Starting at any represented state, every symbolic marker path lifts to an indexed path with identical edge labels and identical final components. Complete successor reconstruction is checked at all 4262 product rows. Induction on the arbitrary finite path constructs each indexed successor. This proves completeness of the finite carrier; recognizing the literal marked prefix and its tail phases remains a separate arithmetic step."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula NfaMk(params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V("NFA"), Dot, V("mk"))), [.. args]);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
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
    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula Tuple(params Formula[] a) =>
        Parenthesized(a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Comma, Sp, y)));


    private static Formula State() => ListOf(Z());
    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula RawFormula()
    {
        var start = Call("univ",State());
        var step = Lam("s",State(),Lam("a",Alphabet(),
            Seq(OpenBrace,V("t"),Colon,State(),Sp,Mid,Sp,
                Mem(Tuple(V("t"),V("a")),Call("successors",V("s"))),CloseBrace)));
        var accept = Call("univ",State());
        return Disp(Eqn(V("prefixRawAutomaton"),NfaMk(step,start,accept)));
    }
    private static Formula RealizationFormula()
    {
        var raw=V("prefixRawAutomaton");
        var graph=Call("prefixAutomaton",V("charge"));
        var fin=Call("Fin",D(4,2,6,2));
        Formula Full(Formula i) => Call("fst",Call("prefixTable",Call("val",i)));
        var body=Ex("v",fin,And(Eqn(Full(V("v")),V("t")),
            Call("Nonempty",Call("Path",graph,V("u"),V("v"),V("xs")))));
        body=All("u",fin,Imp(Eqn(Full(V("u")),V("s")),body));
        body=Imp(Call("Nonempty",Call("Path",raw,V("s"),V("t"),V("xs"))),body);
        return Disp(All("charge",Ty("Bool"),All("s",State(),All("t",State(),All("xs",ListOf(Alphabet()),body)))));
    }
}
