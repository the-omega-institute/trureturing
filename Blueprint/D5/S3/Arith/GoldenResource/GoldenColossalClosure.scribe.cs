using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class GoldenColossalClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/GoldenColossalClosure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The base's worst adopted layer fixes a positive threshold. Retaining its factors "
            + "and every strictly better layer constructs a colossally abundant multiple "
            + "that divides every other colossally abundant multiple.",
        H("Golden Colossal Closure"),
        Blocks(
            Entry("goldenPriceThreshold", "golden-colossal-price-threshold", "Base threshold",
                ThresholdFormula(), DescribeRole.Definition,
                "The threshold is exactly the frozen goldenLowerPrice. For B greater than "
                    + "one this is the minimum adopted-layer marginal over its prime divisors, "
                    + "and it is strictly positive."),
            Entry("support_price_le_threshold", "golden-colossal-support-price-bound",
                "A multiple's support price is bounded by the base threshold",
                SupportFormula(), DescribeRole.Theorem,
                "The fixed-price criterion bounds the supporting price by each last adopted "
                    + "layer of N. Divisibility makes every exponent of B at most the exponent "
                    + "of N; decreasing marginals then bound that same price by each last "
                    + "layer of B. Taking the finite minimum gives the threshold bound. "
                    + "The intermediate theorem requires N at least one. The final theorem "
                    + "handles N equal to zero separately, since the frozen abundance "
                    + "predicate does not itself assert positivity."),
            Entry("goldenPositiveLayerCount", "golden-colossal-positive-layer-count",
                "Strictly profitable layer count", CountFormula(), DescribeRole.Definition,
                "This is the natural cardinality of the positive layer indices whose marginal "
                    + "is strictly greater than the base threshold. For a prime and B greater "
                    + "than one, the proof identifies this set with the finite interval from "
                    + "one to the first exponent whose next layer is no longer strictly better. "
                    + "Layers tied with the threshold are excluded from this count."),
            Entry("colossalClosure", "golden-colossal-closure-definition", "Threshold closure",
                ClosureFormula(), DescribeRole.Definition,
                "For B greater than one, the closure is the finite prime product with exponent "
                    + "max(base exponent, strictly profitable layer count). The frozen uniform "
                    + "prime cutoff proves finite support, and the product is positive. "
                    + "For the out-of-source boundary inputs zero and one, the definition "
                    + "returns B itself."),
            Entry("colossal_closure_factorization", "golden-colossal-closure-exponents",
                "The construction has the specified exponents", ExponentFormula(),
                DescribeRole.Theorem,
                "For each prime, the factorization of the constructed integer is exactly the "
                    + "maximum of its base exponent and the natural cardinality of its "
                    + "strictly profitable layers. Thus the finite-support construction "
                    + "realizes the explicit threshold-count formula."),
            Entry("dvd_colossal_closure", "golden-colossal-base-divides-closure",
                "The base divides its closure", BaseDividesFormula(), DescribeRole.Theorem,
                "Every closure exponent is at least its base exponent, so the natural-number "
                    + "factorization divisibility criterion proves that B divides its closure."),
            Entry("colossal_closure_dvd_of_dvd_colossally_abundant",
                "golden-colossal-closure-divides-abundant-multiple",
                "The closure divides every abundant multiple", MinimalityFormula(),
                DescribeRole.Theorem,
                "For a positive abundant multiple N, the named support-price bound puts its "
                    + "supporting price at most the base threshold. Its next-layer bounds "
                    + "therefore bound every strictly profitable prefix by the exponent of N. "
                    + "Both entries of each maximum are at most that exponent, so the closure "
                    + "divides N. For N equal to zero, divisibility holds directly."),
            Entry("colossal_closure_is_colossally_abundant",
                "golden-colossal-closure-abundance", "The closure is colossally abundant",
                AbundanceFormula(), DescribeRole.Theorem,
                "At the positive base threshold, every next layer of the closure has marginal "
                    + "at most the price. Each last adopted layer is either required by B, "
                    + "and hence has marginal at least the threshold, or is strictly profitable. "
                    + "The frozen common-price criterion proves global optimality. Equal-price "
                    + "layers are retained only as required by B. Numerical leastness and "
                    + "uniqueness are not separate public theorems in this slice."))));

    private static DocumentBlock.Describe Entry(string declaration, string id, string title,
        Formula formula, DescribeRole role, string text) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static Formula ThresholdFormula()
    {
        Formula b = F.Id("B");
        return Disp(ForAll([Bound("B", Naturals())],
            Equal(Threshold(b), Call("goldenLowerPrice", b))));
    }

    private static Formula SupportFormula()
    {
        Formula b = F.Id("B"), n = F.Id("N"), price = F.Id("lambda");
        Formula hypotheses = And(Lt(D(1), b), And(Le(D(1), n),
            And(Divides(b, n), And(Abundant(n),
                And(Lt(D(0), price), Call("IsGoldenResourceOptimal", price, n))))));
        return Disp(ForAll([Bound("B", Naturals()), Bound("N", Naturals()),
            Bound("lambda", Reals())], Implies(hypotheses, Le(price, Threshold(b)))));
    }

    private static Formula CountFormula()
    {
        Formula b = F.Id("B"), p = F.Id("p"), k = F.Id("k");
        Formula layers = Seq(OpenBrace, k, Colon, Sp, Naturals(), Sp, Mid, Sp,
            And(Le(D(1), k), Lt(Threshold(b), Call("goldenLayerMarginal", p, k))), CloseBrace);
        return Disp(ForAll([Bound("B", Naturals()), Bound("p", Naturals())],
            Equal(Count(b, p), Call("ncard", layers))));
    }

    private static Formula ClosureFormula()
    {
        Formula b = F.Id("B"), p = F.Id("p");
        Formula product = Seq(Prod, Underscore, Grp(Seq(p, Sp, InMacro, Sp, Call("Primes"))),
            Sp, new Formula.Power(p, Exponent(b, p)));
        return Disp(ForAll([Bound("B", Naturals())],
            Implies(Lt(D(1), b), Equal(Closure(b), product))));
    }

    private static Formula ExponentFormula()
    {
        Formula b = F.Id("B"), p = F.Id("p");
        return Disp(ForAll([Bound("B", Naturals()), Bound("p", Naturals())],
            Implies(And(Lt(D(1), b), Call("Prime", p)),
                Equal(Call("factorization", Closure(b), p), Exponent(b, p)))));
    }

    private static Formula BaseDividesFormula()
    {
        Formula b = F.Id("B");
        return Disp(ForAll([Bound("B", Naturals())],
            Implies(Lt(D(1), b), Divides(b, Closure(b)))));
    }

    private static Formula MinimalityFormula()
    {
        Formula b = F.Id("B"), n = F.Id("N");
        return Disp(ForAll([Bound("B", Naturals()), Bound("N", Naturals())],
            Implies(And(Lt(D(1), b), And(Abundant(n), Divides(b, n))), Divides(Closure(b), n))));
    }

    private static Formula AbundanceFormula()
    {
        Formula b = F.Id("B");
        return Disp(ForAll([Bound("B", Naturals())],
            Implies(Lt(D(1), b), Abundant(Closure(b)))));
    }

    private static Formula Threshold(Formula b) => Call("goldenPriceThreshold", b);
    private static Formula Count(Formula b, Formula p) => Call("goldenPositiveLayerCount", b, p);
    private static Formula Closure(Formula b) => Call("colossalClosure", b);
    private static Formula Abundant(Formula n) => Call("IsColossallyAbundant", n);
    private static Formula Exponent(Formula b, Formula p) =>
        Call("max", Call("factorization", b, p), Count(b, p));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
