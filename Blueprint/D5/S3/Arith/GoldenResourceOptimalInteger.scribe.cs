using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenResourceOptimalIntegerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResourceOptimalInteger.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At logarithmic resource price 1/25, the positive integer 5040 uniquely maximizes "
            + "the logarithm of the reciprocal divisor sum minus the resource cost.",
        H("Golden Resource Optimal Integer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-resource-objective"),
                DeclarationHandle.Create(Prefix + "goldenResourceObjective"),
                H("The resource objective"),
                StatementSource.FromAuthor(ObjectiveDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is J_lambda(n) = W(n) - lambda E(n) from theorem 11.1 of "
                        + "ZECKENDORF_EULER_5040, with the volume's definitions "
                        + "W(n) = ln(sum of reciprocal divisors) and E(n) = ln(n) expanded. "
                        + "The function is defined on all natural numbers; the optimum theorem "
                        + "uses positive natural numbers. Here divisors is Nat.divisors, log "
                        + "is Real.log, and natural numbers inside logarithms and fractions "
                        + "are coerced to real numbers. All displayed fractions denote real division."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-layer-marginal"),
                DeclarationHandle.Create(Prefix + "goldenLayerMarginal"),
                H("The marginal benefit per logarithmic unit"),
                StatementSource.FromAuthor(MarginalDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the volume's r(p,a), written using powers of the real reciprocal "
                        + "of p. Its prime-layer interpretation applies when p is prime and "
                        + "a is positive; the Lean definition itself is total."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-layer-strict-decrease"),
                DeclarationHandle.Create(Prefix + "golden_layer_strict_decrease"),
                H("Strictly decreasing prime layers"),
                StatementSource.FromAuthor(DecreaseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every prime p and positive layers a < b, the later layer has strictly "
                        + "smaller marginal benefit. Prime denotes Nat.Prime. The proof compares "
                        + "the two geometric quotients over positive denominators, then applies "
                        + "strict monotonicity of the real logarithm."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("golden-resource-sigma-identity"),
                DeclarationHandle.Create(Prefix + "golden_resource_sigma_identity"),
                H("The divisor-sum expression"),
                StatementSource.FromAuthor(SigmaFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here sigma is ArithmeticFunction.sigma; sigma(1,n) is the sum of the "
                        + "positive divisors of n. The divisor-complement bijection identifies "
                        + "the reciprocal divisor sum with sigma(1,n)/n. This named companion "
                        + "connects the source definition to the multiplicative sigma API used "
                        + "in the proof of the unique optimum."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("golden-resource-unique-optimum"),
                DeclarationHandle.Create(Prefix + "golden_resource_unique_optimum"),
                H("5040 is the unique optimum at price 1/25"),
                StatementSource.FromAuthor(OptimumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive natural number n, its objective is at most that "
                            + "of 5040, with equality exactly when n = 5040. These two clauses "
                            + "state the unique argmax in theorem 11.1, without a bound on n.")),
                    Paragraph(Text(
                        "The atom ends at the threshold table header. The surrounding volume "
                            + "supplies the rows for primes 2, 3, 5, 7 and the exclusion of primes "
                            + "at least 11. The proof verifies all nine strict rational power "
                            + "comparisons at exponent 25 in the kernel, proves uniform tail "
                            + "exclusion, and obtains the unique exponents 4, 2, 1, 1. Sigma "
                            + "factorization and a finite sum over the union of prime supports "
                            + "then give the global inequality and its equality characterization.")),
                    Paragraph(Text(
                        "The result concerns this specified resource objective. It asserts "
                            + "neither the Riemann hypothesis nor optimality for other entropy "
                            + "or compression objectives."))),
                DescribeRole.Theorem))));

    private static Formula ObjectiveDefinition()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula d = F.Id("d");
        Formula reciprocalSum = Seq(
            new Formula.Subscript(Sum,
                Relation(d, FormulaRelationOperator.MemberOf, Call("divisors", n))),
            Sp, new Formula.Fraction(D(1), d));
        return Disp(ForAll([Bound("lambda", Reals()), Bound("n", Naturals())],
            Equal(Call("goldenResourceObjective", lambda, n),
                Subtract(Call("log", reciprocalSum), Product(lambda, Call("log", n))))));
    }

    private static Formula MarginalDefinition()
    {
        Formula p = F.Id("p");
        Formula a = F.Id("a");
        Formula inverse = Parenthesized(new Formula.Fraction(D(1), p));
        Formula ratio = new Formula.Fraction(
            Subtract(D(1), new Formula.Power(inverse, Add(a, D(1)))),
            Subtract(D(1), new Formula.Power(inverse, a)));
        return Disp(ForAll([Bound("p", Naturals()), Bound("a", Naturals())],
            Equal(Call("goldenLayerMarginal", p, a),
                new Formula.Fraction(Call("log", ratio), Call("log", p)))));
    }

    private static Formula DecreaseFormula()
    {
        Formula p = F.Id("p");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        return Disp(ForAll(
            [Bound("p", Naturals()), Bound("a", Naturals()), Bound("b", Naturals())],
            Implies(Parenthesized(And(Call("Prime", p), And(Le(D(1), a), Lt(a, b)))),
                Lt(Call("goldenLayerMarginal", p, b), Call("goldenLayerMarginal", p, a)))));
    }

    private static Formula SigmaFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        return Disp(ForAll([Bound("lambda", Reals()), Bound("n", Naturals())],
            Implies(Le(D(1), n), Equal(Call("goldenResourceObjective", lambda, n),
                Subtract(Call("log", new Formula.Fraction(Call("sigma", D(1), n), n)),
                    Product(lambda, Call("log", n)))))));
    }

    private static Formula OptimumFormula()
    {
        Formula n = F.Id("n");
        Formula cost = new Formula.Fraction(D(1), D(2, 5));
        Formula objective = Call("goldenResourceObjective", cost, n);
        Formula optimum = Call("goldenResourceObjective", cost, D(5, 0, 4, 0));
        return Disp(ForAll([Bound("n", Naturals())], Implies(Le(D(1), n),
            Parenthesized(And(Le(objective, optimum), Parenthesized(new Formula.Logic(
                Equal(objective, optimum), FormulaLogicOperator.Iff, Equal(n, D(5, 0, 4, 0)))))))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Relation(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.LessThan, right);
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
    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
}
