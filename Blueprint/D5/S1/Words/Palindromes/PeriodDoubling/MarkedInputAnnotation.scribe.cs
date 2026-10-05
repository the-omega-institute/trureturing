using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class MarkedInputAnnotationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/MarkedInputAnnotation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A base path with a positive prefix spaced by three admits a completed marker annotation.", H("Marked Input Annotation"), Blocks(
        Describe.Lean(DescribeId.Create("pd-markedinputannotation-marked-input-path-annotation"),
            DeclarationHandle.Create(Prefix + "marked_input_path_annotation"), H("Complete annotation of a marked input pattern"),
            StatementSource.FromAuthor(AnnotationFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The base path ends at a valid charge-mode goal. Its input digit stream is a lower tail followed by a nonempty repetition of [1,0,0], and at least one final zero. The two preceding input digits vanish, with the two stored source digits included when the lower tail has fewer than two entries. The initial full marker state stores the base source index and mode zero. There exists a path of the literal marker relation with exactly the same arithmetic labels, ending in mode four at the same base endpoint. The persistent output class flag is zero throughout an accepted base path, so every required marker transition is available. The first marker is selected precisely after the lower tail; all preceding modes remain zero. This statement supplies path existence; interpretation of the retained or removed lowest digit and its terminal charge correction requires further arithmetic information."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Ty(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Ty(name), [.. args]);
    private static Formula ListOf(Formula value) => Call("List", value);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);

    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);



    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula Entry(Formula f,int k) => Call("getD",Call("getElemOption",f,new Formula.Number(k)),D(0));

    private static Formula AnnotationFormula()
    {
        var list=ListOf(Z());var fin=Call("Fin",D(1,4,9,2));
        var automaton=Call("baseAutomaton",Ty("true"));
        var input=Call("pathOutputs",Seq(LambdaLower,Sp,OpenBracket,fin,CloseBracket,Sp,
            OpenBracket,Alphabet(),CloseBracket,Sp,V("q"),Colon,fin,Sp,Mapsto,Sp,
            Entry(Call("fst",Call("baseTable",Call("val",V("q")))),10)),V("p"));
        var block=Seq(OpenBracket,D(1),Comma,Sp,D(0),Comma,Sp,D(0),CloseBracket);
        var twoZeros=Seq(OpenBracket,D(0),Comma,Sp,D(0),CloseBracket);
        var shape=Call("append",Call("append",V("lower"),
            Call("flatten",Call("replicate",V("m"),block))),Call("replicate",Add(V("k"),D(1)),D(0)));
        var state=Call("fst",Call("baseTable",Call("val",V("s"))));
        var history=Call("reverse",Call("append",Seq(OpenBracket,Entry(state,11),Comma,Sp,Entry(state,10),CloseBracket),V("lower")));
        var gap=And(Eqn(Entry(history,0),D(0)),Eqn(Entry(history,1),D(0)));
        var start=And(Eqn(Entry(V("full"),0),Cast(Call("val",V("s")),Z())),Eqn(Entry(V("full"),1),D(0)),
            Mem(V("t"),Call("accept",automaton)),LtF(D(0),V("m")),gap,Eqn(input,shape));
        var modes=Call("pathOutputs",Seq(LambdaLower,Sp,OpenBracket,list,CloseBracket,Sp,
            OpenBracket,Alphabet(),CloseBracket,Sp,V("q"),Colon,list,Sp,Mapsto,Sp,Entry(V("q"),1)),V("pp"));
        var position=Call("length",V("lower"));
        var chosen=Ex("pp",Call("Path",Ty("prefixRawAutomaton"),V("full"),V("u"),V("xs")),And(
            Eqn(Call("take",position,modes),Call("replicate",position,D(0))),
            Eqn(Call("getElemOption",modes,position),Call("some",D(1)))));
        var conclusion=Ex("u",list,And(Eqn(Entry(V("u"),0),Cast(Call("val",V("t")),Z())),
            Eqn(Entry(V("u"),1),D(4)),chosen));
        return Disp(All("s",fin,All("t",fin,All("xs",ListOf(Alphabet()),
            All("p",Call("Path",automaton,V("s"),V("t"),V("xs")),All("full",list,All("lower",list,
                All("m",N(),All("k",N(),Imp(start,conclusion))))))))));
    }
}
