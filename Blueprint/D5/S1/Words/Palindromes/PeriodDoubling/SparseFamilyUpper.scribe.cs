using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class SparseFamilyUpperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform upper bounds for both sparse-family endpoints.", H("Sparse Family Upper Bounds"), Blocks(
        Describe.Lean(DescribeId.Create("pd-sparsefamilyupper-sparse-family-upper"),
            DeclarationHandle.Create("D5/S1/Words/Palindromes/PeriodDoubling/SparseFamilyUpper.sparse_family_upper"),
            H("Diagonal and off-diagonal upper bounds"),
            StatementSource.FromAuthor(MainFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For positive odd a, odd b at least 2a minus one, and epsilon zero or one, repeated six-cut reductions produce the displayed uniform bound. At b equal to 2a minus one both endpoints have at most 3a factors. At larger odd b the bounds are a+b and a+b+1. The diagonal terminal uses a three-factor construction at an even exponent; the other terminal uses the alternating-tail reduction. NatSub denotes truncated natural subtraction, mod denotes natural remainder, and val denotes the natural value of a finite index."))), DescribeRole.Theorem))));
    private static Formula V(string name) => F.Id(name);
    private static Formula Upd(Formula n) =>
        new Formula.Apply(new Formula.Subscript(V("u"), Seq(Mathrm, Grp(V("pd")))), [n]);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, V(name), Colon, type, Sp, Mapsto, Sp, body);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula SubN(Formula a, Formula b) => Call("NatSub", a, b);
    private static Formula State(Formula p, Formula z, Formula c)
    {
        var high = Call("sum", Call("range", p), Lam("s", N(),
            new Formula.Power(D(2), Add(Add(Add(Mul(D(2), c), z), D(2)), Mul(D(3), V("s"))))));
        var tail = Call("sum", Call("range", c), Lam("j", N(),
            new Formula.Power(D(2), Add(Mul(D(2), V("j")), D(1)))));
        return Add(high, tail);
    }
    private static Formula P(Formula n) => Call("PL", Call("ofFn",
        Lam("i", Call("Fin", n), Upd(Call("val", V("i"))))));
    private static Formula MainFormula()
    {
        var input = P(Add(State(V("a"), D(0), V("b")), V("eps")));
        var hypotheses = And(And(And(And(Lt(D(0), V("a")),
            Eq(Call("mod", V("a"), D(2)), D(1))),
            Eq(Call("mod", V("b"), D(2)), D(1))),
            Le(SubN(Mul(D(2), V("a")), D(1)), V("b"))), Le(V("eps"), D(1)));
        var bound = Call("ite", Eq(V("b"), SubN(Mul(D(2), V("a")), D(1))),
            Mul(D(3), V("a")), Add(Add(V("a"), V("b")), V("eps")));
        return Disp(All("a", N(), All("b", N(), All("eps", N(),
            Imp(hypotheses, Le(input, bound))))));
    }
}
