using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class GoldenResourceThresholdCriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/GoldenResourceThresholdCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive integer maximizes the resource objective at a fixed positive price exactly "
            + "when every unadopted boundary layer is below the price and every adopted boundary "
            + "layer is above it, allowing equality.",
        H("Golden Resource Threshold Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-resource-global-optimality"),
                DeclarationHandle.Create(Prefix + "IsGoldenResourceOptimal"),
                H("Optimality at a fixed price"),
                StatementSource.FromAuthor(OptimalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any real price lambda and natural n, the predicate compares n with "
                        + "every positive natural competitor m. Positivity of n and lambda is "
                        + "imposed by the criterion below."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-resource-prime-layer-strict-gain"),
                DeclarationHandle.Create(Prefix + "golden_resource_strict_improvement_of_marginal_gt"),
                H("A profitable next layer gives a better integer"),
                StatementSource.FromAuthor(ImprovementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive lambda, positive n, and a prime p, a next-layer marginal "
                        + "strictly greater than lambda makes n times p strictly better than n. "
                        + "The proof places both objectives on the same finite prime support, "
                        + "cancels the unchanged directions, and computes the remaining gain as "
                        + "log p times marginal minus price. This is the named witness consumed "
                        + "by the necessary upper threshold in the criterion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-resource-common-price-threshold-criterion"),
                DeclarationHandle.Create(Prefix + "golden_resource_optimal_iff_layer_thresholds"),
                H("Fixed-price global optimality and boundary thresholds"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For lambda greater than zero and n at least one, optimality is "
                            + "equivalent to the following two conditions. For every prime p, "
                            + "the marginal at exponent factorization n p plus one is at most "
                            + "lambda. For each prime p dividing n, lambda is at most the "
                            + "marginal at exponent factorization n p. Equality is retained.")),
                    Paragraph(Text(
                        "Necessity compares n with n times p and, for adopted directions, "
                            + "with n divided by p. Sufficiency applies the frozen one-prime "
                            + "threshold theorem termwise after expressing n and an arbitrary "
                            + "positive competitor on the union of their finite prime supports.")),
                    Paragraph(Text(
                        "This slice uses a fixed price. It does not define L or U, establish "
                            + "their extrema, identify a colossally abundant predicate with a "
                            + "nonempty price interval, reduce absent-prime checks to the "
                            + "smallest missing prime, or classify all ties at critical prices."))),
                DescribeRole.Theorem))));

    private static Formula OptimalityFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        return Disp(ForAll(
            [Bound("lambda", Reals()), Bound("n", Naturals())],
            Iff(Call("IsGoldenResourceOptimal", lambda, n),
                ForAll([Bound("m", Naturals())],
                    Implies(Le(D(1), m), Le(Objective(lambda, m), Objective(lambda, n)))))));
    }

    private static Formula ImprovementFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula exponent = Call("factorization", n, p);
        Formula assumptions = And(Lt(D(0), lambda), And(Le(D(1), n),
            And(Call("Prime", p), Lt(lambda, Marginal(p, Add(exponent, D(1)))))));
        return Disp(ForAll(
            [Bound("lambda", Reals()), Bound("n", Naturals()), Bound("p", Naturals())],
            Implies(assumptions,
                Lt(Objective(lambda, n), Objective(lambda, Product(n, p))))));
    }

    private static Formula CriterionFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula exponent = Call("factorization", n, p);
        Formula upper = ForAll([Bound("p", Naturals())],
            Implies(Call("Prime", p), Le(Marginal(p, Add(exponent, D(1))), lambda)));
        Formula lower = ForAll([Bound("p", Naturals())],
            Implies(And(Call("Prime", p), Relation(p, FormulaRelationOperator.Divides, n)),
                Le(lambda, Marginal(p, exponent))));
        return Disp(ForAll([Bound("lambda", Reals()), Bound("n", Naturals())],
            Implies(And(Lt(D(0), lambda), Le(D(1), n)),
                Iff(Call("IsGoldenResourceOptimal", lambda, n), And(upper, lower)))));
    }

    private static Formula Objective(Formula lambda, Formula n) =>
        Call("goldenResourceObjective", lambda, n);
    private static Formula Marginal(Formula p, Formula a) => Call("goldenLayerMarginal", p, a);
    private static Formula Product(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Relation(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Le(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
