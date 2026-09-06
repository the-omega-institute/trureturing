using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenLocalThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenLocalThreshold.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boundary marginal inequalities at a common price make a chosen exponent optimal "
            + "within one prime direction.",
        H("Golden Local Threshold"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-prime-local-objective"),
                DeclarationHandle.Create(Prefix + "goldenPrimeLocalObjective"),
                H("The one-prime local objective"),
                StatementSource.FromAuthor(ObjectiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real price lambda, natural base p, and natural exponent a, this "
                        + "is the logarithm of the reciprocal geometric factor through layer a, "
                        + "minus lambda times a log p. The definition is total; the optimality "
                        + "theorem below restricts p to be prime."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-prime-local-threshold-sufficiency"),
                DeclarationHandle.Create(
                    Prefix + "golden_prime_local_objective_maximal_of_threshold"),
                H("Boundary thresholds suffice for local optimality"),
                StatementSource.FromAuthor(ThresholdFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every prime p, real price lambda, and chosen exponent a, assume the "
                            + "next marginal is at most lambda. If a is positive, also assume "
                            + "lambda is at most the adopted boundary marginal; when a is zero, "
                            + "that lower-bound condition is absent. Then every competing natural "
                            + "exponent b has local objective at most the objective at a. Both "
                            + "boundary comparisons are non-strict, so equality and tied optima "
                            + "are retained.")),
                    Paragraph(Text(
                        "The proof identifies each adjacent objective difference with log p "
                            + "times marginal minus price. Frozen strict decrease of the prime "
                            + "marginals propagates the two boundary inequalities, making the "
                            + "objective nondecreasing up to a and nonincreasing after a.")),
                    Paragraph(Text(
                        "This is only the sufficiency direction for one fixed prime. It does not "
                            + "prove local necessity, combine prime directions, define the global "
                            + "bounds L or U, characterize highly abundant numbers, reduce absent "
                            + "prime checks to the smallest missing prime, or classify all "
                            + "endpoint "
                            + "ties."))),
                DescribeRole.Theorem))));

    private static Formula ObjectiveFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula p = F.Id("p");
        Formula a = F.Id("a");
        Formula inverse = Parenthesized(new Formula.Fraction(D(1), p));
        Formula ratio = new Formula.Fraction(
            Subtract(D(1), new Formula.Power(inverse, Add(a, D(1)))),
            Subtract(D(1), inverse));
        Formula cost = Product(Product(lambda, a), Call("log", p));
        return Disp(ForAll(
            [Bound("lambda", Reals()), Bound("p", Naturals()), Bound("a", Naturals())],
            Equal(Call("goldenPrimeLocalObjective", lambda, p, a),
                Subtract(Call("log", ratio), cost))));
    }

    private static Formula ThresholdFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula p = F.Id("p");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula marginal = Call("goldenLayerMarginal", p, a);
        Formula assumptions = And(
            Call("Prime", p),
            And(
                Le(Call("goldenLayerMarginal", p, Add(a, D(1))), lambda),
                Or(Equal(a, D(0)), Le(lambda, marginal))));
        Formula conclusion = ForAll(
            [Bound("b", Naturals())],
            Le(Call("goldenPrimeLocalObjective", lambda, p, b),
                Call("goldenPrimeLocalObjective", lambda, p, a)));
        return Disp(ForAll(
            [Bound("p", Naturals()), Bound("a", Naturals()), Bound("lambda", Reals())],
            Implies(assumptions, conclusion)));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Product(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
