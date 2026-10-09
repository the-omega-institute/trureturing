using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Antipowers;

internal sealed class PerturbedGoldenSampleGridDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Antipowers/PerturbedGoldenSampleGrid.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A signed rational approximation separates a parity sample grid by golden cylinder cuts.",
        H("Perturbed Golden Sample Grids"),
        Blocks(
            Node("grid-rank", "Rank in a finite cut set", "rank", RankFormula(),
                "The rank counts cuts at or below x. The filter is over real numbers, with the "
                    + "half-open convention that a cut belongs to the cell on its right.",
                DescribeRole.Definition),
            Node("grid-error", "Signed sampling error", "error", ErrorFormula(),
                "The first error term is signed and the quadratic drift is nonpositive. "
                    + "Nat.cast in these formulas takes its value in the real numbers.",
                DescribeRole.Definition),
            Node("grid-sample", "Parity sample lift", "Y", SampleFormula(),
                "Nat.div and Nat.mod denote natural floor division and remainder. Even indices "
                    + "start in the integer parity class; odd indices start half a period away.",
                DescribeRole.Definition),
            Node("grid-lift-identity", "Sampling lift identity", "sampling_lift_identity",
                LiftFormula(),
                "Splitting j into twice its natural quotient by 2 plus its remainder produces "
                    + "the parity lift. The discarded part is a whole multiple of q.",
                DescribeRole.Lemma),
            Node("grid-rank-injective", "Distinct samples occupy distinct golden cylinders",
                "golden_sample_grid_rank_injective", InjectiveFormula(),
                "For an arbitrary coprime numerator p and positive even denominator q, a signed "
                    + "golden-slope residual satisfying the two strict bounds separates every "
                    + "pair of indices below q−1. The proof constructs ordered periodic cuts "
                    + "from the inverse of p modulo q, puts each parity sample strictly between "
                    + "its cuts, and proves that its cell label is distinct modulo q. No "
                    + "Fibonacci-index assumption is needed.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula RankFormula()
    {
        var t = F.Id("T"); var x = F.Id("x"); var c = F.Id("c");
        var predicate = Seq(Operatorname, Grp(F.Id("fun")), Sp,
            Parenthesized(Seq(c, Sp, Colon, Sp, Reals())), Sp, Mapsto, Sp, Le(c, x));
        return Disp(All("T", Call("Finset", Reals()), All("x", Reals(),
            Equal(Call("rank", t, x),
                Call(Qualified("Finset", "card"),
                    Call(Qualified("Finset", "filter"), predicate, t))))));
    }

    private static Formula ErrorFormula()
    {
        var s = F.Id("s"); var d = F.Id("d"); var j = F.Id("j");
        return Disp(All("s", Reals(), All("d", Reals(), All("j", Naturals(),
            Equal(Call("error", s, d, j),
                Subtract(Multiply(new Formula.Negate(s), d),
                    RealDiv(Multiply(Cast(j), new Formula.Power(d, D(2))), D(2))))))));
    }

    private static Formula SampleFormula()
    {
        var q = F.Id("q"); var p = F.Id("p"); var s = F.Id("s");
        var d = F.Id("d"); var j = F.Id("j");
        var even = Equal(Call(Qualified("Nat", "mod"), j, D(2)), D(0));
        var rhs = Add(Add(Add(Add(Cast(p),
                If(even, D(0), RealDiv(Cast(q), D(2)))),
                Multiply(s, Cast(NatDiv(j, D(2))))),
                If(even, D(0), RealDiv(s, D(2)))), Call("error", s, d, j));
        return Disp(All("q", Naturals(), All("p", Naturals(), All("s", Reals(),
            All("d", Reals(), All("j", Naturals(),
                Equal(Call("Y", q, p, s, d, j), rhs)))))));
    }

    private static Formula LiftFormula()
    {
        var q = F.Id("q"); var p = F.Id("p"); var s = F.Id("s");
        var d = F.Id("d"); var j = F.Id("j");
        var lhs = Add(Add(Add(Cast(p), RealDiv(Multiply(Cast(j), Cast(q)), D(2))),
            RealDiv(Multiply(s, Cast(j)), D(2))), Call("error", s, d, j));
        var rhs = Add(Call("Y", q, p, s, d, j), Multiply(Cast(q), Cast(NatDiv(j, D(2)))));
        return Disp(All("q", Naturals(), All("p", Naturals(), All("s", Reals(),
            All("d", Reals(), All("j", Naturals(), Equal(lhs, rhs)))))));
    }

    private static Formula InjectiveFormula()
    {
        var q = F.Id("q"); var p = F.Id("p"); var s = F.Id("s");
        var d = F.Id("d"); var i = F.Id("i"); var j = F.Id("j");
        var cuts = Call("goldenCylinderEndpointSet", Subtract(q, D(1)));
        Formula RankAt(Formula index) => Call("rank", cuts,
            Call(Qualified("Int", "fract"), RealDiv(Call("Y", q, p, s, d, index), Cast(q))));
        var hypotheses = Conjoin(
            Lt(D(0), q), Call("Even", q), Call(Qualified("Nat", "Coprime"), p, q),
            Or(Equal(s, D(1)), Equal(s, new Formula.Negate(D(1)))), Lt(D(0), d),
            Lt(Multiply(Cast(q), d), RealDiv(D(9), D(2, 0))),
            Lt(Add(d, RealDiv(Multiply(Cast(q), new Formula.Power(d, D(2))), D(2))),
                RealDiv(D(4, 9), D(2, 0, 0, 0))),
            Equal(Multiply(Cast(q), Call("goldenMechanicalSlope")),
                Subtract(Cast(p), Multiply(s, d))),
            Lt(i, Subtract(q, D(1))), Lt(j, Subtract(q, D(1))), NotEqual(i, j));
        return Disp(All("q", Naturals(), All("p", Naturals(), All("s", Reals(),
            All("d", Reals(), All("i", Naturals(), All("j", Naturals(),
                Implies(hypotheses, NotEqual(RankAt(i), RankAt(j))))))))));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Cast(Formula value) => Call(Qualified("Nat", "cast"), value);
    private static Formula NatDiv(Formula a, Formula b) => Call(Qualified("Nat", "div"), a, b);
    private static Formula RealDiv(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Call(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula If(Formula condition, Formula yes, Formula no) => Parenthesized(Seq(
        Operatorname, Grp(F.Id("if")), Sp, condition, Sp, Operatorname, Grp(F.Id("then")), Sp,
        yes, Sp, Operatorname, Grp(F.Id("else")), Sp, no));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Conjoin(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(Parenthesized(clauses[i]), FormulaLogicOperator.And, result);
        return result;
    }
}
