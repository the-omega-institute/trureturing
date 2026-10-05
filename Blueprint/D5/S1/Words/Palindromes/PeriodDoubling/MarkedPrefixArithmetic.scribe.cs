using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class MarkedPrefixArithmeticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixArithmetic.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arithmetic of Separated Marked Prefixes.", H("Arithmetic of Separated Marked Prefixes"), Blocks(
        Describe.Lean(DescribeId.Create("pd-markedprefixarithmetic-marked-powers"),
            DeclarationHandle.Create(Prefix + "markedPowers"), H("The marked powers"),
            StatementSource.FromAuthor(PowersFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The marked block is the sum of positive powers at positions p, p+3, up to p+3(m-1)."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-markedprefixarithmetic-marked-prefix"),
            DeclarationHandle.Create(Prefix + "markedPrefix"), H("The literal separated marked prefix"),
            StatementSource.FromAuthor(PrefixFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A rounded half-endpoint is the marked block plus a signed tail. The tail is a finite nonadjacent expansion with coefficients minus one, zero and one; every nonzero coefficient at position k satisfies k+3 at most p. div denotes natural integer quotient."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("pd-markedprefixarithmetic-marked-prefix-tail-bound"),
            DeclarationHandle.Create(Prefix + "marked_prefix_tail_bound"), H("Strict tail bound and positive endpoint"),
            StatementSource.FromAuthor(BoundFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A nonempty marked block dominates the separated signed tail. Bounded signed-list evaluation gives the strict absolute tail bound, including positions below three where the tail vanishes, and the lowest positive marked summand forces the endpoint to be positive. NatSub is truncated natural subtraction."))), DescribeRole.Theorem))));
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
    private static Formula LtF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeF(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(params Formula[] items) => items.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);

    private static Formula Lam(string n, Formula t, Formula b) =>
        Seq(V(n), Colon, t, Sp, Mapsto, Sp, b);
    private static Formula NegF(Formula a) => Call("neg", a);
    private static Formula Cast(Formula x, Formula t) => Call("cast", x, t);



    private static Formula SignedEval(Formula ds) => Call("foldr",Seq(LambdaLower,Sp,V("z"),Colon,Z(),Sp,
        V("x"),Colon,Z(),Sp,Mapsto,Sp,Add(V("z"),Mul(D(2),V("x")))),D(0),ds);
    private static Formula B() => Call("markedPowers",V("m"),V("p"));
    private static Formula PowersFormula()
    {
        var term=Lam("s",N(),Pow(D(2),Add(V("p"),Mul(D(3),V("s")))));
        var sum=Call("sum",Call("range",V("m")),term);
        return Disp(All("m",N(),All("p",N(),Eqn(B(),sum))));
    }
    private static Formula PrefixFormula()
    {
        var coeff=All("z",Z(),Imp(Mem(V("z"),V("tail")),
            new Formula.Logic(Eqn(V("z"),NegF(D(1))),FormulaLogicOperator.Or,
                new Formula.Logic(Eqn(V("z"),D(0)),FormulaLogicOperator.Or,Eqn(V("z"),D(1))))));
        var sparse=Call("IsChain",V("tail"),Seq(LambdaLower,Sp,V("a"),Colon,Z(),Sp,V("b"),Colon,Z(),Sp,Mapsto,Sp,
            new Formula.Logic(Eqn(V("a"),D(0)),FormulaLogicOperator.Or,Eqn(V("b"),D(0)))));
        var support=All("k",N(),Imp(Ne(Call("getD",Call("getElemOption",V("tail"),V("k")),D(0)),D(0)),
            LeF(Add(V("k"),D(3)),V("p"))));
        var value=Eqn(Cast(Call("div",Add(V("n"),D(1)),D(2)),Z()),Add(Cast(B(),Z()),V("T")));
        return Disp(All("n",N(),All("m",N(),All("p",N(),All("T",Z(),IffF(Call("markedPrefix",V("n"),V("m"),V("p"),V("T")),
            And(value,Ex("tail",ListOf(Z()),And(Eqn(SignedEval(V("tail")),V("T")),coeff,sparse,support)))))))));
    }
    private static Formula BoundFormula() => Disp(All("n",N(),All("m",N(),All("p",N(),All("T",Z(),
        Imp(And(LtF(D(0),V("m")),Call("markedPrefix",V("n"),V("m"),V("p"),V("T"))),
            And(LtF(Call("abs",V("T")),Cast(Pow(D(2),Call("NatSub",V("p"),D(2))),Z())),LtF(D(0),V("n")))))))));
}
