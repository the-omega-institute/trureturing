using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class MarkedPrefixExpansionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixExpansion.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal marked prefixes determine the ordered signed stream.", H("Exact Stream of a Marked Prefix"), Blocks(
        Describe.Lean(DescribeId.Create("pd-markedprefixexpansion-marked-prefix-expansion"),
            DeclarationHandle.Create(Prefix + "marked_prefix_expansion"), H("Padded stream and exact lower tail"),
            StatementSource.FromAuthor(ExpansionFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Any nonadjacent signed expansion of twice the rounded half-endpoint, of length at least p+3m+2, consists of a lower tail of length p+1, then m blocks [1,0,0], then at least one leading zero. The lower tail evaluates to twice T and its nonzero positions i satisfy i+2 at most p. Adding the two initial zero memories gives two zero digits immediately before the selected marker, including p=0. The proof constructs the literal expansion, evaluates the geometric block, and applies nonadjacent digit uniqueness. div is natural integer quotient; option lookups have default zero."))), DescribeRole.Theorem))));
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
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static Formula NegF(Formula a) => Call("neg", a);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);



    private static Formula SignedEval(Formula ds) => Call("foldr",Seq(LambdaLower,Sp,V("z"),Colon,Z(),Sp,
        V("x"),Colon,Z(),Sp,Mapsto,Sp,Add(V("z"),Mul(D(2),V("x")))),D(0),ds);
    private static Formula E(Formula ds, Formula i) => Call("getD",Call("getElemOption",ds,i),D(0));
    private static Formula Ints(params Formula[] xs) => Seq(OpenBracket,xs.Skip(1).Aggregate(xs[0],(a,b)=>Seq(a,Comma,Sp,b)),CloseBracket);
    private static Formula ExpansionFormula()
    {
        var coeff=All("z",Z(),Imp(Mem(V("z"),V("ds")),new Formula.Logic(Eqn(V("z"),NegF(D(1))),FormulaLogicOperator.Or,
            new Formula.Logic(Eqn(V("z"),D(0)),FormulaLogicOperator.Or,Eqn(V("z"),D(1))))));
        var sparse=Call("IsChain",V("ds"),Seq(LambdaLower,Sp,V("a"),Colon,Z(),Sp,V("b"),Colon,Z(),Sp,Mapsto,Sp,
            new Formula.Logic(Eqn(V("a"),D(0)),FormulaLogicOperator.Or,Eqn(V("b"),D(0)))));
        var hypotheses=And(Call("markedPrefix",V("n"),V("m"),V("p"),V("T")),coeff,sparse,
            Eqn(SignedEval(V("ds")),Mul(D(2),Cast(Call("div",Add(V("n"),D(1)),D(2)),Z()))),
            LeF(Add(Add(V("p"),Mul(D(3),V("m"))),D(2)),Call("length",V("ds"))));
        var blocks=Call("flatten",Call("replicate",V("m"),Ints(D(1),D(0),D(0))));
        var memories=Call("reverse",Call("append",Ints(D(0),D(0)),V("lower")));
        var result=Ex("lower",ListOf(Z()),Ex("k",N(),And(Eqn(Call("length",V("lower")),Add(V("p"),D(1))),
            Eqn(SignedEval(V("lower")),Mul(D(2),V("T"))),
            All("i",N(),Imp(Ne(E(V("lower"),V("i")),D(0)),LeF(Add(V("i"),D(2)),V("p")))),
            Eqn(V("ds"),Call("append",Call("append",V("lower"),blocks),Call("replicate",Add(V("k"),D(1)),D(0)))),
            Eqn(E(memories,D(0)),D(0)),Eqn(E(memories,D(1)),D(0)))));
        return Disp(All("n",N(),All("m",N(),All("p",N(),All("T",Z(),All("ds",ListOf(Z()),Imp(hypotheses,result)))))));
    }
}
