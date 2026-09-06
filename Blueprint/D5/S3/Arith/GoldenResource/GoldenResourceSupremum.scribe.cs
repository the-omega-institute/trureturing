using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class GoldenResourceSupremumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/GoldenResourceSupremum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At positive prices the resource supremum equals the finite sum of positive layer gains.",
        H("Golden Resource Supremum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-objective-at-optimal-positive-part-sum"),
                DeclarationHandle.Create(Prefix + "objective_at_optimal_eq_positive_part_sum"),
                H("The objective at the minimal-count configuration"),
                StatementSource.FromAuthor(OptimalValueFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive price and a positive integer realizing optimalLayerCount "
                        + "at every natural p, the objective equals the sum of log p times "
                        + "the net marginal over all strictly profitable prime-layer pairs. "
                        + "The frozen count specification supplies such an integer. The proof "
                        + "telescopes the public single-layer delta along each prime power, "
                        + "then regroups the finite active-pair set by prime. This is the "
                        + "value identity used by the supremum theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-resource-supremum-positive-part-sum"),
                DeclarationHandle.Create(Prefix + "golden_resource_supremum_eq_positive_part_sum"),
                H("The exact unconstrained optimal value"),
                StatementSource.FromAuthor(SupremumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The supremum ranges over objective values of all positive integers. "
                            + "The frozen count specification supplies a greatest element, "
                            + "so this supremum is attained and equals the objective evaluated "
                            + "in the preceding theorem.")),
                    Paragraph(Text(
                        "The sum is indexed by the finite set of all pairs (p,k) with p prime, "
                            + "k at least one, and marginal strictly above lambda. Thus each "
                            + "included net marginal equals its positive part; all excluded "
                            + "positive-index prime layers have zero positive part. This finite "
                            + "support presentation expresses the positive-part double sum. "
                            + "The hypothesis lambda greater than zero is essential. No claim "
                            + "about nonpositive prices or the RH boundary is made."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-resource-equality-price-invariance"),
                DeclarationHandle.Create(Prefix + "golden_resource_objective_eq_of_layer_price"),
                H("Equality-price layers preserve the objective"),
                StatementSource.FromAuthor(EqualityPriceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real price, positive integer n and prime p, if the next p-layer "
                        + "has marginal equal to the price, n and n times p have equal "
                        + "objectives. Reading the equality in reverse also describes removal "
                        + "of that layer. This companion is a direct application of the frozen "
                        + "single-layer delta to the equality-price clause."))),
                DescribeRole.Theorem))));

    private static Formula ActiveSum(Formula lambda)
    {
        Formula p = F.Id("p");
        Formula k = F.Id("k");
        Formula pair = Seq(Open, p, Comma, k, Close);
        Formula active = SetBuilder(pair, Seq(Naturals(), Times, Naturals()),
            And(Le(D(1), k), And(Call("Prime", p), Lt(lambda, Marginal(p, k)))));
        return Seq(Sum, Underscore, Grp(Seq(pair, InMacro, active)), Sp,
            Product(Call("log", p), Seq(Open, Subtract(Marginal(p, k), lambda), Close)));
    }

    private static Formula OptimalValueFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula counts = ForAll([Bound("p", Naturals())],
            Equal(Call("factorization", n, p), Call("optimalLayerCount", lambda, p)));
        return Disp(ForAll([Bound("lambda", Reals()), Bound("n", Naturals())],
            Implies(And(Lt(D(0), lambda), And(Le(D(1), n), counts)),
                Equal(Objective(lambda, n), ActiveSum(lambda)))));
    }

    private static Formula SupremumFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula x = F.Id("x");
        Formula realized = new Formula.BindMany(FormulaQuantifier.Exists,
            [Bound("n", Naturals())], And(Le(D(1), n), Equal(Objective(lambda, n), x)));
        Formula values = SetBuilder(x, Reals(), realized);
        return Disp(ForAll([Bound("lambda", Reals())], Implies(Lt(D(0), lambda),
            Equal(Call("sSup", values), ActiveSum(lambda)))));
    }

    private static Formula EqualityPriceFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula price = Equal(Marginal(p, Add(Call("factorization", n, p), D(1))), lambda);
        return Disp(ForAll(
            [Bound("lambda", Reals()), Bound("n", Naturals()), Bound("p", Naturals())],
            Implies(And(Le(D(1), n), And(Call("Prime", p), price)),
                Equal(Objective(lambda, Product(n, p)), Objective(lambda, n)))));
    }

    private static Formula SetBuilder(Formula variable, Formula domain, Formula predicate) =>
        Seq(OpenBrace, variable, Colon, Sp, domain, Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula Objective(Formula lambda, Formula n) =>
        Call("goldenResourceObjective", lambda, n);
    private static Formula Marginal(Formula p, Formula k) => Call("goldenLayerMarginal", p, k);
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
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
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
