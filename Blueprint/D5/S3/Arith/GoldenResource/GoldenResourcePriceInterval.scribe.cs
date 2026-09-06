using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class GoldenResourcePriceIntervalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/GoldenResourcePriceInterval.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The best unadopted prime layer has an attained positive price. Comparing it with "
            + "the worst adopted layer characterizes existence of a common optimal price.",
        H("Golden Resource Price Interval"),
        Blocks(
            Entry("goldenUpperPrice", "golden-resource-upper-price", "Upper layer price",
                UpperDefinition(), DescribeRole.Definition,
                "L(n) is the real supremum of the set of next-layer marginals over all primes, "
                    + "with exponent factorization n p plus one. For positive n the supremum "
                    + "is attained, as proved below. The Lean API is named goldenUpperPrice."),
            Entry("goldenLowerPrice", "golden-resource-lower-price", "Lower layer price",
                LowerDefinition(), DescribeRole.Definition,
                "For n greater than one, U(n) is the minimum of the adopted-layer marginals "
                    + "over the finite nonempty set of prime divisors of n. For empty prime "
                    + "support, namely n equal to zero or one, goldenLowerPrice is defined to "
                    + "equal goldenUpperPrice. This real-valued boundary convention extends "
                    + "the existential criterion to one; it does not make the full set of "
                    + "prices at one a bounded interval."),
            Entry("IsColossallyAbundant", "golden-resource-colossal-abundance",
                "Colossal abundance", AbundanceDefinition(), DescribeRole.Definition,
                "The predicate asserts existence of a strictly positive real price at which "
                    + "n maximizes the frozen resource objective among all positive integers."),
            Entry("golden_upper_price_attained", "golden-resource-upper-price-attainment",
                "A prime attains the best next-layer price", AttainmentFormula(false),
                DescribeRole.Theorem,
                "The next layer at prime two has positive marginal. The frozen uniform "
                    + "cutoff at that value leaves finitely many candidate primes. A maximum "
                    + "among these dominates the omitted tail, since every tail value is "
                    + "below the candidate at two. This constructs the preregistered witness "
                    + "for an arbitrary positive integer, without enumerating a fixed instance."),
            Entry("golden_upper_price_spec", "golden-resource-upper-price-specification",
                "The supremum is an attained maximum", AttainmentFormula(true),
                DescribeRole.Theorem,
                "The attained maximum identifies the real supremum and supplies the upper "
                    + "bound for every next-layer marginal. The final criterion consumes "
                    + "this specification, so attainment is on its proof dependency path."),
            Entry("golden_upper_price_pos", "golden-resource-upper-price-positivity",
                "The upper price is positive", PositiveFormula(), DescribeRole.Theorem,
                "The upper price equals a positive prime-layer marginal. This gives the "
                    + "positive price selected in the sufficient direction of the criterion."),
            Entry("colossally_abundant_iff_price_interval_nonempty",
                "golden-resource-price-interval-criterion", "Existence of a common price",
                CriterionFormula(), DescribeRole.Theorem,
                "For n at least one, colossal abundance is equivalent to L(n) at most U(n). "
                    + "Necessity bounds L by an optimal price and bounds that price by every "
                    + "adopted-layer marginal. Sufficiency chooses the positive price L and "
                    + "applies the frozen fixed-price threshold criterion. Equality is kept. "
                    + "This slice does not separately state the characterization of every "
                    + "admissible price, reduce absent-prime comparisons to the smallest "
                    + "missing prime, or classify ties at critical parameters."))));

    private static DocumentBlock.Describe Entry(string declaration, string id, string title, Formula formula,
        DescribeRole role, string text) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static Formula UpperDefinition()
    {
        Formula n = F.Id("n");
        return Disp(ForAll([Bound("n", Naturals())],
            Equal(Upper(n), Call("sSup", Call("nextPrimeLayerValues", n)))));
    }

    private static Formula LowerDefinition()
    {
        Formula n = F.Id("n");
        return Disp(ForAll([Bound("n", Naturals())], Implies(Lt(D(1), n),
            Equal(Lower(n), Call("min", Call("adoptedPrimeLayerValues", n))))));
    }

    private static Formula AbundanceDefinition()
    {
        Formula n = F.Id("n");
        Formula lambda = F.Id("lambda");
        return Disp(ForAll([Bound("n", Naturals())], Iff(Call("IsColossallyAbundant", n),
            Some([Bound("lambda", Reals())],
                And(Lt(D(0), lambda), Call("IsGoldenResourceOptimal", lambda, n))))));
    }

    private static Formula AttainmentFormula(bool identifySupremum)
    {
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula r = F.Id("r");
        Formula bound = identifySupremum ? Upper(n) : Next(n, p);
        Formula all = ForAll([Bound("r", Naturals())],
            Implies(Call("Prime", r), Le(Next(n, r), bound)));
        Formula body = identifySupremum ? And(Equal(Upper(n), Next(n, p)), all) : all;
        return Disp(ForAll([Bound("n", Naturals())], Implies(Le(D(1), n),
            Some([Bound("p", Naturals())], And(Call("Prime", p), body)))));
    }

    private static Formula PositiveFormula()
    {
        Formula n = F.Id("n");
        return Disp(ForAll([Bound("n", Naturals())],
            Implies(Le(D(1), n), Lt(D(0), Upper(n)))));
    }

    private static Formula CriterionFormula()
    {
        Formula n = F.Id("n");
        return Disp(ForAll([Bound("n", Naturals())], Implies(Le(D(1), n),
            Iff(Call("IsColossallyAbundant", n), Le(Upper(n), Lower(n))))));
    }

    private static Formula Upper(Formula n) => Call("goldenUpperPrice", n);
    private static Formula Lower(Formula n) => Call("goldenLowerPrice", n);
    private static Formula Next(Formula n, Formula p) =>
        Call("goldenLayerMarginal", p, Add(Call("factorization", n, p), D(1)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Some(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
