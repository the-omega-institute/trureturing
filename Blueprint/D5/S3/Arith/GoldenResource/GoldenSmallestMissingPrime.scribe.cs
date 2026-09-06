using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class GoldenSmallestMissingPrimeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/GoldenSmallestMissingPrime.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Missing-prime threshold tests reduce to the least prime not dividing the integer.",
        H("The Smallest Missing Prime"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-first-layer-strict-prime-decrease"),
                DeclarationHandle.Create(Prefix + "golden_layer_marginal_one_strictAnti"),
                H("Strict decrease across primes"),
                StatementSource.FromAuthor(StrictDecreaseFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For primes p less than q, the first-layer marginal at q is strictly "
                        + "smaller than at p. Cancelling the first-layer ratio gives "
                        + "log(1 + 1/p) divided by log p. Its positive numerator strictly "
                        + "decreases with p and its positive denominator strictly increases. "
                        + "This comparison across primes is the new estimate used below; "
                        + "the existing decrease with layer number does not supply it."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-first-layer-threshold-propagation"),
                DeclarationHandle.Create(Prefix + "golden_layer_marginal_one_threshold_of_le"),
                H("Threshold propagation"),
                StatementSource.FromAuthor(PropagationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At any real price, a first-layer threshold valid at q is valid at "
                        + "every prime p at least q. Equality of primes is included. "
                        + "Consequently the implication also holds when both primes are "
                        + "required not to divide a given positive integer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-least-missing-prime-threshold-equivalence"),
                DeclarationHandle.Create(Prefix + "golden_missing_prime_threshold_iff_of_isLeast"),
                H("The least missing prime decides the condition"),
                StatementSource.FromAuthor(LeastEquivalenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Given the least prime q not dividing n, all missing primes have "
                        + "first-layer marginal at most the price exactly when q does. "
                        + "The reverse implication uses the new prime comparison. "
                        + "IsLeast includes both membership and minimality, so the "
                        + "hypothesis identifies an actual missing prime."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-smallest-missing-prime-threshold-existence"),
                DeclarationHandle.Create(Prefix + "exists_smallest_missing_prime_threshold"),
                H("Existence for every positive integer"),
                StatementSource.FromAuthor(ExistenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every integer n at least one has a least missing prime q, and "
                        + "this single q decides the missing-prime condition for every "
                        + "real price. Mathlib supplies a prime above n, which cannot "
                        + "divide the positive integer n; Nat.find selects the least "
                        + "missing prime. The witness q is chosen before the price. "
                        + "No finite search bound or numerical threshold is assumed."))),
                DescribeRole.Theorem))));

    private static Formula StrictDecreaseFormula()
    {
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        return Disp(ForAll([Bound("p", Naturals()), Bound("q", Naturals())],
            Implies(And(Prime(p), And(Prime(q), Lt(p, q))), Lt(Marginal(q), Marginal(p)))));
    }

    private static Formula PropagationFormula()
    {
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula lambda = F.Id("lambda");
        return Disp(ForAll(
            [Bound("p", Naturals()), Bound("q", Naturals()), Bound("lambda", Reals())],
            Implies(And(Prime(p), And(Prime(q), And(Le(q, p), Threshold(q, lambda)))),
                Threshold(p, lambda))));
    }

    private static Formula LeastEquivalenceFormula()
    {
        Formula n = F.Id("n");
        Formula q = F.Id("q");
        Formula lambda = F.Id("lambda");
        return Disp(ForAll(
            [Bound("n", Naturals()), Bound("q", Naturals()), Bound("lambda", Reals())],
            Implies(LeastMissing(n, q), Iff(AllThresholds(n, lambda), Threshold(q, lambda)))));
    }

    private static Formula ExistenceFormula()
    {
        Formula n = F.Id("n");
        Formula q = F.Id("q");
        Formula lambda = F.Id("lambda");
        Formula conclusion = new Formula.BindMany(FormulaQuantifier.Exists,
            [Bound("q", Naturals())], And(LeastMissing(n, q),
                ForAll([Bound("lambda", Reals())],
                    Iff(AllThresholds(n, lambda), Threshold(q, lambda)))));
        return Disp(ForAll([Bound("n", Naturals())], Implies(Le(D(1), n), conclusion)));
    }

    private static Formula LeastMissing(Formula n, Formula q)
    {
        Formula p = F.Id("p");
        Formula missing = Seq(OpenBrace, p, Colon, Sp, Naturals(), Sp, Mid, Sp,
            Missing(n, p), CloseBrace);
        return Call("IsLeast", missing, q);
    }

    private static Formula AllThresholds(Formula n, Formula lambda)
    {
        Formula p = F.Id("p");
        return ForAll([Bound("p", Naturals())], Implies(Missing(n, p), Threshold(p, lambda)));
    }

    private static Formula Missing(Formula n, Formula p) => And(Prime(p),
        Seq(Neg, Grp(new Formula.Relation(p, FormulaRelationOperator.Divides, n))));
    private static Formula Prime(Formula p) => Call("Prime", p);
    private static Formula Marginal(Formula p) => Call("goldenLayerMarginal", p, D(1));
    private static Formula Threshold(Formula p, Formula lambda) => Le(Marginal(p), lambda);
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
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
