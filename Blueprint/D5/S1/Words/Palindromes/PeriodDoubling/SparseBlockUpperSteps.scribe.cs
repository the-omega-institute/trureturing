using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.PeriodDoubling;

internal sealed class SparseBlockUpperStepsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform four-cut and two-cut constructions for the sparse binary family.", H("Sparse Block Upper Constructions"), Blocks(
        Describe.Lean(DescribeId.Create("pd-sparseblockuppersteps-sparse-block-upper-steps"),
            DeclarationHandle.Create("D5/S1/Words/Palindromes/PeriodDoubling/SparseBlockUpperSteps.sparse_block_upper_steps"),
            H("The two reductions and both endpoint bits"),
            StatementSource.FromAuthor(MainFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The displayed sums are the literal integers with binary blocks (100) repeated p times, a gap of z zeros and (10) repeated c times. For epsilon zero or one, an even gap and at least three tail blocks permit four cuts; an odd gap and at least one tail block permit two cuts. The construction uses the exact long and short odd-palindrome radii and preserves the higher prefix. NatSub is truncated natural subtraction; mod is natural remainder; val is the natural value of a finite index."))), DescribeRole.Theorem))));
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
        var input = P(Add(State(V("p"), V("z"), V("c")), V("eps")));
        var even = Imp(And(Eq(Call("mod", V("z"), D(2)), D(0)), Le(D(3), V("c"))),
            Le(input, Add(P(Add(State(SubN(V("p"), D(1)), Add(V("z"), D(9)),
                SubN(V("c"), D(3))), V("eps"))), D(4))));
        var odd = Imp(And(Eq(Call("mod", V("z"), D(2)), D(1)), Le(D(1), V("c"))),
            Le(input, Add(P(Add(State(SubN(V("p"), D(1)), Add(V("z"), D(5)),
                SubN(V("c"), D(1))), V("eps"))), D(2))));
        return Disp(All("p", N(), All("z", N(), All("c", N(), All("eps", N(),
            Imp(And(Lt(D(0), V("p")), Le(V("eps"), D(1))), And(even, odd)))))));
    }
}
