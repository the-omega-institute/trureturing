using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class FirstLayerMarginalAntitoneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/FirstLayerMarginalAntitone.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime antitonicity reduces the upper layer price to an explicit finite maximum.",
        H("First-Layer Marginal Antitonicity and Finite Maximum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("successor-logarithm-splitting-identity"),
                DeclarationHandle.Create(Prefix + "log_add_one_div_log_eq_one_add"),
                H("The successor-logarithm identity"),
                StatementSource.FromAuthor(SplittingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For x > 1, factor x + 1 as x(1 + 1/x). Additivity of the "
                        + "logarithm separates the quotient into one plus the first-layer term."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-first-layer-logarithmic-normalization"),
                DeclarationHandle.Create(Prefix + "golden_layer_marginal_one_eq_log_one_add_inv"),
                H("Normalization of the first golden layer"),
                StatementSource.FromAuthor(MarginalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At layer one, the ratio in goldenLayerMarginal simplifies to 1 + 1/p, "
                        + "so the marginal is exactly the normalized logarithmic quotient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-successor-logarithm-decrease"),
                DeclarationHandle.Create(Prefix + "log_add_one_div_log_strictAnti_of_prime"),
                H("Strict decrease across primes"),
                StatementSource.FromAuthor(PrimeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For primes with 2 <= p < q, the successor-logarithm quotient at q is strictly "
                        + "smaller than at p. The common additive term from the splitting "
                        + "identity leaves the strictly decreasing first-layer marginals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("upper-price-finite-maximum"),
                DeclarationHandle.Create(Prefix
                    + "golden_upper_price_eq_finite_max_of_isLeast_missing_prime"),
                H("The upper price is a finite maximum"),
                StatementSource.FromAuthor(FiniteMaximumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let q be the least prime not dividing a positive integer n. The upper "
                        + "layer price equals the maximum of the next-layer marginals over q "
                        + "together with the prime factors of n. Every other prime has first "
                        + "layer marginal at most that of q, so no further prime changes the maximum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("upper-price-finite-maximum-unconditional"),
                DeclarationHandle.Create(Prefix + "golden_upper_price_eq_finite_max"),
                H("The finite maximum without a supplied least prime"),
                StatementSource.FromAuthor(UnconditionalFiniteMaximumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The least prime not dividing n exists for every positive n, so the finite "
                        + "maximum needs no such prime as an input. Producing it here states the "
                        + "reduction of the upper price outright rather than relative to a caller."))),
                DescribeRole.Theorem))));

    private static Formula SplittingFormula()
    {
        Formula x = F.Id("x");
        return Disp(ForAll([Bound("x", Reals())], Implies(Lt(D(1), x),
            Equal(SuccessorRatio(x), Add(D(1), LogRatio(x))))));
    }

    private static Formula PrimeFormula()
    {
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        return Disp(ForAll([Bound("p", Naturals()), Bound("q", Naturals())],
            Implies(And(Prime(p), And(Le(D(2), p), And(Prime(q), Lt(p, q)))),
                Lt(SuccessorRatio(q), SuccessorRatio(p)))));
    }

    private static Formula MarginalFormula()
    {
        Formula p = F.Id("p");
        return Disp(ForAll([Bound("p", Naturals())], Implies(Prime(p),
            Equal(Call("goldenLayerMarginal", p, D(1)), LogRatio(p)))));
    }

    private static Formula FiniteMaximumFormula()
    {
        Formula n = F.Id("n");
        Formula q = F.Id("q");
        Formula p = F.Id("p");
        Formula missingPrimes = Seq(OpenBrace, p, Colon, Sp, Naturals(), Sp, Mid, Sp,
            And(Prime(p), new Formula.Not(Divides(p, n))), CloseBrace);
        Formula leastMissing = Call("IsLeast", missingPrimes, q);
        Formula finiteSupport = Call("insert", q, Call("primeFactors", n));
        Formula finiteMaximum = Seq(Max, Underscore,
            Grp(Seq(p, Sp, InMacro, Sp, finiteSupport)), Sp,
            Call("goldenLayerMarginal", p,
                Add(Call("factorization", n, p), D(1))));
        return Disp(ForAll([Bound("n", Naturals()), Bound("q", Naturals())],
            Implies(And(Le(D(1), n), leastMissing),
                Equal(Call("goldenUpperPrice", n), finiteMaximum))));
    }

    private static Formula UnconditionalFiniteMaximumFormula()
    {
        Formula n = F.Id("n");
        Formula q = F.Id("q");
        Formula p = F.Id("p");
        Formula missingPrimes = Seq(OpenBrace, p, Colon, Sp, Naturals(), Sp, Mid, Sp,
            And(Prime(p), new Formula.Not(Divides(p, n))), CloseBrace);
        Formula leastMissing = Call("IsLeast", missingPrimes, q);
        Formula finiteSupport = Call("insert", q, Call("primeFactors", n));
        Formula finiteMaximum = Seq(Max, Underscore,
            Grp(Seq(p, Sp, InMacro, Sp, finiteSupport)), Sp,
            Call("goldenLayerMarginal", p,
                Add(Call("factorization", n, p), D(1))));
        return Disp(ForAll([Bound("n", Naturals())], Implies(Le(D(1), n),
            Exists([Bound("q", Naturals())],
                And(leastMissing, Equal(Call("goldenUpperPrice", n), finiteMaximum))))));
    }

    private static Formula LogRatio(Formula x) => new Formula.Fraction(
        Call("log", Add(D(1), new Formula.Fraction(D(1), x))), Call("log", x));

    private static Formula SuccessorRatio(Formula x) => new Formula.Fraction(
        Call("log", Add(x, D(1))), Call("log", x));

    private static Formula Prime(Formula value) => Call("Prime", value);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Add(Formula left, Formula right) =>
        Seq(left, Sp, Plus, Sp, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
