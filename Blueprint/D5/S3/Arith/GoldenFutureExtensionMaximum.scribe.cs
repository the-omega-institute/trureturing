using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenFutureExtensionMaximumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenFutureExtensionMaximum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At every positive resource price, the positive future layers above a positive integer "
            + "form a finite prefix selection whose product attains the best extension gain.",
        H("Golden Future Extension Maximum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-future-extension-maximum-attained"),
                DeclarationHandle.Create(
                    Prefix + "golden_future_extension_maximum_attained"),
                H("The future extension maximum is attained"),
                StatementSource.FromAuthor(MaximumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive real price lambda and positive natural number n, "
                            + "there is a positive multiple m of n whose resource-objective "
                            + "gain over n is at least that of every positive multiple k of n.")),
                    Paragraph(Text(
                        "The proof constructs the finite set of exactly those future prime "
                            + "layers whose marginal exceeds lambda. Uniform decay across primes "
                            + "and fixed-prime decay bound this set in both coordinates, while "
                            + "strict marginal decrease makes each prime fiber a prefix. Its "
                            + "finite supremum defines a finitely supported factorization and "
                            + "therefore an actual positive integer m.")),
                    Paragraph(Text(
                        "The arbitrary-price factorization theorem reduces the global comparison "
                            + "to prime-local comparisons. Positive prefix layers make the local "
                            + "objective nondecreasing up to the selected exponent, and every "
                            + "later layer has nonpositive gain, making it nonincreasing after "
                            + "that exponent.")),
                    Paragraph(Text(
                        "This result proves only finite-prefix construction and attainment among "
                            + "positive divisible extensions. It does not identify the optimum "
                            + "with Phi_lambda or R_lambda, state the displayed layer-sum identity, "
                            + "or separately classify zero-marginal layers."))),
                DescribeRole.Theorem))));

    private static Formula MaximumFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        Formula k = F.Id("k");
        Formula start = Call("goldenResourceObjective", lambda, n);
        Formula candidateGain = Subtract(Call("goldenResourceObjective", lambda, m), start);
        Formula competitorGain = Subtract(Call("goldenResourceObjective", lambda, k), start);
        Formula competitor = ForAll(
            [Bound("k", Naturals())],
            Implies(
                And(Divides(n, k), Le(D(1), k)),
                Le(competitorGain, candidateGain)));
        Formula witness = ExistsMany(
            [Bound("m", Naturals())],
            And(Divides(n, m), And(Le(D(1), m), competitor)));
        return Disp(ForAll(
            [Bound("lambda", Reals()), Bound("n", Naturals())],
            Implies(And(Lt(D(0), lambda), Le(D(1), n)), witness)));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula ExistsMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
