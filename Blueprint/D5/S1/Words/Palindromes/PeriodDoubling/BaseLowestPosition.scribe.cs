using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class BaseLowestPositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/BaseLowestPosition.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A tight accepted base path has no earlier nonzero output coefficient.", H("First Nonzero Digit Order"), Blocks(
        Describe.Lean(DescribeId.Create("pd-baselowestposition-base-path-lowest-order"),
            DeclarationHandle.Create(Prefix + "base_path_lowest_order"), H("The literal minimum-position transition law"),
            StatementSource.FromAuthor(CutFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The lowest-position product records an output nonzero coefficient before the first input nonzero coefficient. Lifting the base path preserves every label, so a true terminal flag would contradict its bound zero on a path with f charge one. The persistent flag is therefore false. Induction along the base path, using the literal first-sign memory checker, supplies a nonzero input coefficient no later than any nonzero output coefficient. Optional list entries use default zero. The coefficients include the dummy leading zero, so both streams use the same indexing."))), DescribeRole.Theorem))));
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
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);

    private static Formula Product(params Formula[] a) => SeqWithTimes(a);
    private static Formula SeqWithTimes(Formula[] a) =>
        a.Skip(1).Aggregate(a[0], (x,y) => Seq(x, Sp, Times, Sp, y));


    private static Formula Alphabet() => Product(Z(),Z(),Z(),Z());
    private static Formula Entry(Formula s, int k) => Call("getD",Call("getElemOption",s,new Formula.Number(k)),D(0));
    private static Formula CutFormula()
    {
        var fin=Call("Fin",D(1,4,9,2));
        var M=Call("baseAutomaton",Ty("true"));
        Formula Coeff(int k,Formula i) => Call("getD",Call("getElemOption",
            Call("pathOutputs",Seq(LambdaLower,Sp,OpenBracket,fin,CloseBracket,Sp,
                OpenBracket,Alphabet(),CloseBracket,Sp,V("q"),Colon,fin,Sp,Mapsto,Sp,
                Entry(Call("fst",Call("baseTable",Call("val",V("q")))),k)),V("p")),i),D(0));
        var charge=Call("pathCharge",Seq(LambdaLower,Sp,OpenBracket,fin,CloseBracket,Sp,
            V("a"),Colon,Alphabet(),Sp,OpenBracket,fin,CloseBracket,Sp,Mapsto,Sp,Call("fst",V("a"))),V("p"));
        var order=All("i",N(),Imp(Ne(Coeff(12,V("i")),D(0)),
            Ex("k",N(),And(LeF(V("k"),V("i")),Ne(Coeff(10,V("k")),D(0))))));
        var body=Imp(And(Mem(V("s"),Call("start",M)),Mem(V("t"),Call("accept",M))),
            All("p",Call("Path",M,V("s"),V("t"),V("xs")),Imp(Eqn(charge,D(1)),order)));
        return Disp(All("s",fin,All("t",fin,All("xs",ListOf(Alphabet()),body))));
    }
}
