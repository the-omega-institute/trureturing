using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.DegreeRoots;

internal sealed class EscapeWitnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative finite inverse-power sums control the norm of a complex root by its argument.",
        H("A normalized finite-sum root estimate"), Blocks(
            Describe.Lean(DescribeId.Create("normalized-inverse-power-bound"),
                DeclarationHandle.Create("D5/S3/Zeros/DegreeRoots/EscapeWitness.normalized_escape_bound"),
                H("The argument-dependent estimate"), StatementSource.FromAuthor(Disp(BoundFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(DefinitionDsl.Text(
                    "Let a be nonnegative real weights on a finite type, k natural exponents, "
                    + "and a0 a positive real constant. If a0 plus the weighted inverse powers of z vanishes "
                    + "and the norm of z exceeds one, then its norm is at most the ratio of total weight "
                    + "to a0, raised to |Complex.arg z|/Real.pi. "
                    + "For positive argument, put lam=Real.log ‖z‖/Complex.arg z and take the real part "
                    + "after multiplication by 1+lam·Complex.I. The estimate "
                    + "Real.exp(−lam·t)(Real.cos t+lam·Real.sin t)≥−Real.exp(−lam·Real.pi) "
                    + "for lam>0 and t≥0 bounds each summand. Complex conjugation handles negative argument; "
                    + "a positive constant and nonnegative weights exclude argument zero."))),
                DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(Id(name)));
    private static Formula Q(string owner, string name) => Seq(Op(owner), Dot, Op(name));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Id(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) => new Formula.Relation(left, op, right);
    private static Formula Arrow(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Real => Op("Real");
    private static Formula Complex => Op("Complex");
    private static Formula SumOver(Formula value) => Seq(new Formula.Subscript(Sum, Typed(Id("i"), Id("J"))), value);
    private static Formula BoundFormula()
    {
        var z = Id("z");
        var ai = Call("a", Id("i"));
        var norm = new Formula.Norm(z);
        var inverse = new Formula.Power(z, Seq(Minus, D(1)));
        var equation = Rel(Seq(Typed(Id("a0"), Complex), Plus,
                SumOver(Seq(Typed(ai, Complex), Cdot, Sp, new Formula.Power(Parenthesized(inverse), Call("k", Id("i")))))),
            FormulaRelationOperator.Equal, D(0));
        var conclusion = Rel(norm, FormulaRelationOperator.LessThanOrEqual,
            new Formula.Power(Parenthesized(new Formula.Fraction(SumOver(ai), Id("a0"))),
                new Formula.Fraction(new Formula.Absolute(App(Q("Complex", "arg"), z)), Q("Real", "pi"))));
        var body = All("a", new Formula.TypeArrow(Id("J"), Real),
            All("k", new Formula.TypeArrow(Id("J"), Op("Nat")), All("a0", Real, All("z", Complex,
                Arrow(All("i", Id("J"), Rel(D(0), FormulaRelationOperator.LessThanOrEqual, ai)),
                    Arrow(Rel(D(0), FormulaRelationOperator.LessThan, Id("a0")),
                        Arrow(Rel(D(1), FormulaRelationOperator.LessThan, norm), Arrow(equation, conclusion))))))));
        return Seq(Forall, Sp, Typed(Id("J"), Op("Type")),
            OpenBracket, Call("Fintype", Id("J")), CloseBracket, Comma, body);
    }
}
