using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class UnicyclicSkewnessPlusKurtosisLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/UnicyclicSkewnessPlusKurtosisLowerBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/ptaszynski2022skewness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sum of skewness and kurtosis of every finite positive unidirectional cycle exceeds −8/27, the greatest lower bound over all cycle sizes.",
        H("The sharp lower bound on unicyclic skewness plus kurtosis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-rates"), DeclarationHandle.Create(Prefix + "normalizedRates"),
                H("Normalized inverse rates"), StatementSource.FromAuthor(Disp(NormalizedRatesFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural n and real rate vector k, normalizedRates k divides each inverse rate by their first power sum. Real inversion and division are total; positivity is assumed only in the moment theorem."))),
                DescribeRole.Definition),
            MomentDefinition("p", 2), MomentDefinition("q", 3), MomentDefinition("r", 4),
            Describe.Lean(
                DescribeId.Create("normalized-moments"), DeclarationHandle.Create(Prefix + "normalized_moments"),
                H("Joint moments of the same normalized vector"), StatementSource.FromAuthor(Disp(NormalizedMomentsFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For n ≥ 2 and every positive k, these four facts hold jointly for its normalized inverse rates. The proof applies the original public kurtosis moments theorem after proving positivity of the first power sum. The same suppliers support the sum and difference endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lower-bound"),
                DeclarationHandle.Create(Prefix + "lowerBound"),
                H("The asymptotic lower endpoint"),
                StatementSource.FromAuthor(Disp(LowerBoundFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The real constant −8/27 is the lower endpoint for the sum of skewness and kurtosis "
                    + "in main.tex lines 434-437. Line 424 describes the limit of infinitely many states "
                    + "with one rate a = A/N relative to the other rates; this endpoint corresponds to "
                    + "A = 1/2. The constant will be approached by positive cycles of increasing size."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Strict finite-cycle inequality and greatest lower bound"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n at least two and every strictly positive real rate vector k "
                    + "indexed by Fin n, skewness k + kurtosis k strictly exceeds lowerBound. "
                    + "The same constant is the greatest lower bound of all these values as n varies. "
                    + "The source states in main.tex lines 434-437: “min(S + K) = −8/27 for A = 1/2, "
                    + "max(S + K) = 2 for A → 0.” Line 424 specifies the asymptotic limit. "
                    + "The assertion here reads the lower minimum as an infimum and adds strictness "
                    + "for every finite positive cycle. The source calls the extremal-topology assertion "
                    + "a numerical conjecture in line 792. Only the lower endpoint for the two "
                    + "inverse-rate expressions on unidirectional cycles is asserted here; neither "
                    + "a finite-size extremal topology nor the upper endpoint is asserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The strict bound and its sharp limiting value"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Write Rⱼ = ∑ᵢ(kᵢ)⁻ʲ and xᵢ = (kᵢ)⁻¹/R₁, and put "
                        + "p = ∑ᵢxᵢ², q = ∑ᵢxᵢ³ and r = ∑ᵢxᵢ⁴. "
                        + "The skewness normalization identity gives S = 3p² − 2q, and the "
                        + "kurtosis normalization identity gives K = 15p² − 20q + 6r/p. "
                        + "Adding these identities gives S + K = 18p² − 22q + 6r/p. "
                        + "For n ≥ 2 and positive k, "
                        + "R₁ > 0: each summand is positive, including the one at i = 0. "
                        + "Thus x is positive. The moment inequalities give "
                        + "p > 0, q ≥ 0, q² ≤ pr and r < p². "
                        + "Here q² ≤ pr is Cauchy-Schwarz applied to x and its coordinatewise square, "
                        + "and r < p² follows from the strict square-sum inequality for the "
                        + "at least two positive coordinates xᵢ².")),
                    Paragraph(Text(
                        "Set t = q/p, e = r/p − t² and d = p − t². "
                        + "Then t ≥ 0, q = pt and e ≥ 0 by q² ≤ pr. "
                        + "Since q² ≤ pr < p³, one has t² < p and d > 0. "
                        + "Also r = p(t² + e), so "
                        + "S + K + 8/27 = 18p² − 22pt + 6t² + 6e + 8/27. "
                        + "If t ≤ 11/18, this equals "
                        + "6e + 18(p − (11/18)t)² + (13/18)((11/18)² − t²) + 155/5832. "
                        + "All terms except the positive last constant are nonnegative, since "
                        + "0 ≤ t ≤ 11/18. Hence the sum is strictly positive.")),
                    Paragraph(Text(
                        "If t > 11/18, substitute d = p − t² to obtain instead "
                        + "6e + d(18d + 36t² − 22t) + (t − 2/3)²(18t² + 2t + 2/3). "
                        + "The factor 36t² − 22t = 2t(18t − 11) is nonnegative, "
                        + "so 18d + 36t² − 22t > 0. Its product with d is strictly positive. "
                        + "The polynomial 18t² + 2t + 2/3 is positive, as is seen by "
                        + "completing its square, so the remaining square term is nonnegative. "
                        + "Together with e ≥ 0 this proves positivity in the second case. "
                        + "The normalized expression therefore gives S + K > −8/27 "
                        + "for every finite positive cycle with at least two states.")),
                    Paragraph(Text(
                        "For sharpness, let m ≥ 1 be natural and take m + 1 rates with "
                        + "k₀ = (2(m : ℝ))⁻¹ and kᵢ = 1 for i ≠ 0. These rates are positive. "
                        + "For each natural j their inverse-rate power sum is "
                        + "Rⱼ = (2(m : ℝ))ʲ + (m : ℝ). "
                        + "Substitution in the skewness and kurtosis formulas and cancellation gives "
                        + "S + K + 8/27 = 2(60(m : ℝ)² − 8(m : ℝ) + 1) "
                        + "/[27(m : ℝ)²(4(m : ℝ) + 1)]. "
                        + "Define F(t) = 2(60t − 8t² + t³)/[27(4 + t)]. "
                        + "The preceding value equals F(1/(m : ℝ)). "
                        + "This rational function is continuous at zero and F(0) = 0. "
                        + "Using m + 1 in place of m, the reciprocals "
                        + "1/((m + 1 : ℕ) : ℝ) tend to zero, so the sums for "
                        + "these positive cycles of size m + 2 tend to lowerBound.")),
                    Paragraph(Text(
                        "Finally, the strict inequality makes lowerBound a lower bound of the "
                        + "set of all positive-cycle sums. Any other lower bound b is no greater "
                        + "than every sum in the explicit sequence of cycles of size m + 2. "
                        + "Passing to the limit gives b ≤ lowerBound. Thus lowerBound is the "
                        + "greatest lower bound, and no finite positive cycle attains it."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ptaszynski-2022-unidirectional-skewness-plus-kurtosis-lower-bound"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock.Describe MomentDefinition(string name, byte degree) => Describe.Lean(
        DescribeId.Create(name), DeclarationHandle.Create(Prefix + name), H("Normalized inverse-rate moment " + name),
        StatementSource.FromAuthor(Disp(All("n", Naturals(), All("k", RateType(),
            Equal(Typed(At(Local(name), X("k")), Reals()), PowerSum(Natural(degree), At(Local("normalizedRates"), X("k")))))))),
        AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text("This is the degree " + degree + " power sum of the same normalized inverse-rate vector, for every natural n and real k."))),
        DescribeRole.Definition);

    private static Formula NormalizedRatesFormula() => All("n", Naturals(), All("k", RateType(),
        Equal(Typed(At(Local("normalizedRates"), X("k")), RateType()),
            LambdaOf("i", FinOf(X("n")), Divide(At(Qualified("Inv", "inv"), At(X("k"), X("i"))),
                PowerSum(Natural(1), LambdaOf("j", FinOf(X("n")), At(Qualified("Inv", "inv"), At(X("k"), X("j"))))))))));

    private static Formula NormalizedMomentsFormula()
    {
        Formula a = At(Local("p"), X("k")), b = At(Local("q"), X("k")), c = At(Local("r"), X("k"));
        return All("n", Naturals(), Implication(LessEqual(Natural(2), X("n")), All("k", RateType(),
            Implication(PositiveRates(), Conjunction(Less(Real(0), a), Conjunction(LessEqual(Real(0), b),
                Conjunction(LessEqual(Power(b, Natural(2)), Multiply(a, c)), Less(c, Power(a, Natural(2))))))))));
    }
    private static Formula LambdaOf(string name, Formula type, Formula body) => Seq(Qualified("fun"), Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula PowerSum(Formula degree, Formula vector) => At(Qualified("D5", "S3", "Quantum", "Transport", "StrongAbsorption", "Foundations", "powerSum"), X("n"), degree, vector);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));

    private static Formula LowerBoundFormula() =>
        Equal(Typed(Local("lowerBound"), Reals()),
            Divide(new Formula.Negate(Real(8)), Real(2, 7)));

    private static Formula ClaimBody()
    {
        Formula strict = All("n", Naturals(), Implication(LessEqual(Natural(2), X("n")),
            All("k", RateType(), Implication(PositiveRates(),
                Less(Local("lowerBound"), SumValue())))));
        Formula values = Seq(OpenBrace, Typed(X("s"), Reals()), Sp, Mid, Sp,
            Some("n", Naturals(), Conjunction(LessEqual(Natural(2), X("n")),
                Some("k", RateType(), Conjunction(PositiveRates(), Equal(X("s"), SumValue()))))),
            CloseBrace);
        return Conjunction(strict, At(Qualified("IsGLB"), values, Local("lowerBound")));
    }

    private static Formula SumValue() => Add(
        At(Qualified("D5", "S3", "StatisticalMechanics", "UnicyclicSkewnessMinimum", "skewness"), X("k")),
        At(Qualified("D5", "S3", "StatisticalMechanics", "UnicyclicKurtosisLowerBound", "kurtosis"), X("k")));
    private static Formula PositiveRates() =>
        All("i", FinOf(X("n")), Less(Real(0), At(X("k"), X("i"))));
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "StatisticalMechanics", "UnicyclicSkewnessPlusKurtosisLowerBound", name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula X(string name) => F.Id(name);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Natural(params byte[] digits) => Typed(D(digits), Naturals());
    private static Formula Real(params byte[] digits) => Typed(D(digits), Reals());
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula RateType() => new Formula.TypeArrow(FinOf(X("n")), Reals());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Divide(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
}
