using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class GoldenResource5040EndpointComparisonDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/GoldenResource/GoldenResource5040EndpointComparison.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single prime layer determines the two adjacent objective comparisons at 5040.",
        H("Golden Resource Endpoint Comparisons at 5040"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-resource-objective-single-layer-delta"),
                DeclarationHandle.Create(Prefix + "golden_resource_objective_single_layer_delta"),
                H("The exact objective change from adding one prime layer"),
                StatementSource.FromAuthor(DeltaFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real price lambda, positive natural number n, and prime p, "
                            + "multiplication of n by p changes the objective by the next layer "
                            + "marginal minus lambda, multiplied by log p. Positivity of n is "
                            + "an explicit hypothesis.")),
                    Paragraph(Text(
                        "The proof applies the frozen finite-support decomposition to n and "
                            + "n times p on one common support. Prime factorization changes only "
                            + "at p; all other local differences vanish. The remaining difference "
                            + "is evaluated using exact logarithm identities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-resource-5040-endpoint-comparisons"),
                DeclarationHandle.Create(Prefix + "golden_resource_5040_endpoint_comparisons"),
                H("The two adjacent comparisons beyond the price interval"),
                StatementSource.FromAuthor(ComparisonsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At a price at least log(31/30) divided by log 2, the objective at "
                            + "2520 is at least the objective at 5040. At a price at most "
                            + "log(12/11) divided by log 11, the objective at 55440 is at least "
                            + "the objective at 5040. The comparisons include their endpoints "
                            + "and are non-strict.")),
                    Paragraph(Text(
                        "This companion consumes the single-layer delta at n = 2520, p = 2 "
                            + "and n = 5040, p = 11. The exact boundary marginals are those of "
                            + "layer (2,4) and layer (11,1). The dependency direction is endpoint "
                            + "comparisons to single-layer delta.")),
                    Paragraph(Text(
                        "The statement covers only these adjacent comparisons. The previously "
                            + "frozen strict-interval sufficiency result remains upstream. Global "
                            + "endpoint maximality, numerical decimal bounds, and comparisons "
                            + "with the continuous allocation model are not asserted here."))),
                DescribeRole.Theorem))));

    private static Formula DeltaFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula nextLayer = Add(Call("factorization", n, p), Num(1));
        Formula difference = Subtract(
            Call("goldenResourceObjective", lambda, Product(n, p)),
            Call("goldenResourceObjective", lambda, n));
        Formula marginal = Product(
            Seq(Open, Subtract(Call("goldenLayerMarginal", p, nextLayer), lambda), Close),
            Call("log", p));
        return Disp(ForAll(
            [Bound("lambda", Reals()), Bound("n", Naturals()), Bound("p", Naturals())],
            Implies(And(Le(Num(1), n), Call("Prime", p)), Equal(difference, marginal))));
    }

    private static Formula ComparisonsFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula upper = new Formula.Fraction(
            Call("log", new Formula.Fraction(Num(31), Num(30))), Call("log", Num(2)));
        Formula lower = new Formula.Fraction(
            Call("log", new Formula.Fraction(Num(12), Num(11))), Call("log", Num(11)));
        Formula at5040 = Call("goldenResourceObjective", lambda, Num(5040));
        Formula remove = Implies(Le(upper, lambda),
            Le(at5040, Call("goldenResourceObjective", lambda, Num(2520))));
        Formula add = Implies(Le(lambda, lower),
            Le(at5040, Call("goldenResourceObjective", lambda, Num(55440))));
        return Disp(ForAll([Bound("lambda", Reals())], And(remove, add)));
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

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
