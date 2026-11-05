using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenResource5040PriceIntervalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource5040PriceInterval.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every price strictly between the two adjacent layer thresholds makes 5040 the unique "
            + "maximizer of the golden resource objective.",
        H("Golden Resource 5040 Price Interval"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-resource-5040-target-exponents"),
                DeclarationHandle.Create(Prefix + "targetExponent5040"),
                H("The existing 5040 exponent profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original exponent profile is exposed in place for the "
                    + "boundary computation in ActualRobinInterval. It assigns 4, 2, 1 and 1 "
                    + "to the primes 2, 3, 5 and 7, and zero elsewhere. Its body is unchanged."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-resource-marginal-rational-lower-comparison"),
                DeclarationHandle.Create(Prefix + "one_div_nat_lt_golden_layer_marginal"),
                H("An existing rational lower comparison for a layer price"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a prime p, a positive layer and positive natural k, "
                    + "the stated strict power comparison gives 1/k < goldenLayerMarginal p a. "
                    + "The original logarithm proof is reused by the exact boundary computation; "
                    + "public visibility does not add a new estimate."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("golden-resource-marginal-rational-upper-comparison"),
                DeclarationHandle.Create(Prefix + "golden_layer_marginal_lt_one_div_nat"),
                H("An existing rational upper comparison for a layer price"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The opposite strict power comparison gives "
                    + "goldenLayerMarginal p a < 1/k under the original prime, positive-layer "
                    + "and positive-k hypotheses. The unchanged proof supplies the omitted-layer "
                    + "comparisons in ActualRobinInterval's boundary computation."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("golden-resource-5040-target-factorization"),
                DeclarationHandle.Create(Prefix + "target_exponent_eq_factorization_5040"),
                H("The existing target profile is the actual factorization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original proof identifies targetExponent5040 p "
                    + "with the factorization of 5040 at every natural p. It remains at this "
                    + "owner and is reused directly by the original optimizer boundary proof. "
                    + "Only its visibility has changed."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("golden-prime-local-original-strict-threshold-maximum"),
                DeclarationHandle.Create(Prefix + "golden_prime_local_objective_unique_maximal_of_strict_threshold"),
                H("Original generic strict-threshold uniqueness"),
                StatementSource.FromAuthor(StrictThresholdFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing generic proof is exposed in place for ActualReservePrimeMask. "
                    + "For any real price and actual prime, strict upper and lower thresholds make "
                    + "the chosen exponent maximal, with equality exactly at that exponent. "
                    + "The lower condition allows exponent zero. The theorem is generic despite "
                    + "the 5040 filename; its original proof is unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-resource-5040-price-interval"),
                DeclarationHandle.Create(
                    Prefix + "golden_resource_5040_unique_maximum_of_price_interval"),
                H("The open threshold interval suffices for unique optimality"),
                StatementSource.FromAuthor(PriceIntervalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let lambda lie strictly above log(12/11)/log(11) and strictly below "
                            + "log(31/30)/log(2). For every positive natural number n, the "
                            + "golden resource objective at n is at most its value at 5040, and "
                            + "equality holds exactly when n is 5040.")),
                    Paragraph(Text(
                        "The proof identifies the upper endpoint with the adopted layer (2,4) "
                            + "and the lower endpoint with the first omitted layer (11,1). "
                            + "Strict decay within each prime and a uniform bound for larger "
                            + "primes propagate these comparisons to every adopted and omitted "
                            + "layer. Strict local threshold maximality is then summed over the "
                            + "union of the prime supports of n and 5040.")),
                    Paragraph(Text(
                        "This theorem proves only the sufficient open-interval direction. It "
                            + "does not prove necessity outside the interval, classify endpoint "
                            + "ties, supply decimal approximations, compare classical sequences, "
                            + "or interpret the separate price lambda = 0.04 example."))),
                DescribeRole.Theorem))));

    private static Formula StrictThresholdFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula p = F.Id("p");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula next = new Formula.Binary(a, FormulaBinaryOperator.Add, D(1));
        Formula lower = new Formula.Logic(Equal(a, D(0)), FormulaLogicOperator.Or,
            Lt(lambda, Call("goldenLayerMarginal", p, a)));
        Formula assumptions = And(Call("Prime", p),
            And(Lt(Call("goldenLayerMarginal", p, next), lambda), lower));
        Formula value = Call("goldenPrimeLocalObjective", lambda, p, b);
        Formula maximum = Call("goldenPrimeLocalObjective", lambda, p, a);
        Formula conclusion = And(Le(value, maximum),
            Iff(Equal(value, maximum), Equal(b, a)));
        return Disp(ForAll(
            [Bound("p", Naturals()), Bound("a", Naturals()), Bound("lambda", Reals())],
            Implies(Parenthesized(assumptions), ForAll([Bound("b", Naturals())],
                Parenthesized(conclusion)))));
    }

    private static Formula PriceIntervalFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula lower = new Formula.Fraction(
            Call("log", new Formula.Fraction(D(1, 2), D(1, 1))),
            Call("log", D(1, 1)));
        Formula upper = new Formula.Fraction(
            Call("log", new Formula.Fraction(D(3, 1), D(3, 0))),
            Call("log", D(2)));
        Formula objective = Call("goldenResourceObjective", lambda, n);
        Formula optimum = Call("goldenResourceObjective", lambda, D(5, 0, 4, 0));
        Formula assumptions = And(
            Lt(lower, lambda),
            And(Lt(lambda, upper), Le(D(1), n)));
        Formula conclusion = And(
            Le(objective, optimum),
            Iff(Equal(objective, optimum), Equal(n, D(5, 0, 4, 0))));
        return Disp(ForAll(
            [Bound("lambda", Reals()), Bound("n", Naturals())],
            Implies(Parenthesized(assumptions), Parenthesized(conclusion))));
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

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
