using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class UnicyclicKurtosisLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/ptaszynski2022skewness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The kurtosis of every finite positive unidirectional cycle exceeds −(1 + √5)/10, and this constant is the greatest lower bound over all cycle sizes.",
        H("The sharp lower bound on unicyclic current kurtosis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kurtosis"),
                DeclarationHandle.Create(Prefix + "kurtosis"),
                H("Kurtosis from inverse-rate power sums"),
                StatementSource.FromAuthor(Disp(KurtosisFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a real rate vector k indexed by Fin n, powerSum n j sums the jth powers "
                    + "of its argument over Fin n. "
                    + "The source defines kurtosis as the fourth scaled current cumulant divided by the second "
                    + "in main.tex line 54. Substituting the current cumulants in lines 773-775 and the "
                    + "waiting-time cumulants in lines 787-790 gives the displayed rational expression. "
                    + "This definition uses total real inversion and division, so it is defined for every "
                    + "natural n and every real rate vector. Its interpretation as a current cumulant ratio "
                    + "concerns positive rates on a unidirectional cycle with at least two states; "
                    + "the expression itself does not construct a stochastic process."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lower-bound"),
                DeclarationHandle.Create(Prefix + "lowerBound"),
                H("The asymptotic lower endpoint"),
                StatementSource.FromAuthor(Disp(LowerBoundFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The constant is the lower endpoint for kurtosis stated in main.tex line 132. "
                    + "Section III E 1, lines 424-427, gives this value in the limit of infinitely many "
                    + "states, with one rate equal to A/n and all other rates equal to one, "
                    + "where A = (3 - √5)/2. It is an infimum over cycle sizes, rather than "
                    + "a value attained by a finite positive cycle with at least two states."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Strict finite-cycle inequality and greatest lower bound"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n at least two and every strictly positive vector k indexed by "
                    + "Fin n, kurtosis k strictly exceeds lowerBound. The same lowerBound is the greatest "
                    + "lower bound of the set of all such values, allowing n to vary. "
                    + "This is the unidirectional lower-bound assertion of main.tex lines 417 and 424-427, "
                    + "with the asymptotic minimum read as an infimum and with strictness for each finite cycle. "
                    + "The source's choice of extremal rates is a numerical conjecture in line 417 "
                    + "and in the Appendix, line 792. The assertion here concerns only the lower endpoint "
                    + "for the displayed inverse-rate expression on positive unidirectional cycles."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized"),
                DeclarationHandle.Create(Prefix + "normalized"),
                H("Kurtosis in rescaled inverse rates"),
                StatementSource.FromAuthor(Disp(NormalizedFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Dividing every inverse rate by its first power sum rewrites kurtosis as "
                    + "15 times the square of the second power sum, minus 20 times the third, "
                    + "plus 6 times the fourth divided by the second. The identity holds for "
                    + "every natural n and every real vector k, using total real inversion and division. "
                    + "To prove it, factor the normalization denominator out of each sum. "
                    + "If the first or second inverse-rate power sum is zero, simplify using "
                    + "division by zero; otherwise clear the nonzero denominators."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moments"),
                DeclarationHandle.Create(Prefix + "moments"),
                H("Four inequalities for positive-coordinate power sums"),
                StatementSource.FromAuthor(Disp(MomentsFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For a strictly positive real vector x on Fin n with n at least two, "
                    + "the second power sum is positive and the third is nonnegative. "
                    + "Cauchy-Schwarz applied to x and its coordinatewise square bounds the "
                    + "square of the third power sum by the product of the second and fourth. "
                    + "The strict square-sum inequality applied to the positive coordinates xᵢ² "
                    + "bounds the fourth power sum strictly below the square of the second."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The strict bound and its sharp limiting value"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First write Rⱼ = ∑ᵢ(kᵢ)⁻ʲ and normalize the inverse rates by "
                        + "xᵢ = (kᵢ)⁻¹/R₁. Factoring R₁ out of each power sum gives "
                        + "kurtosis k = 15a² - 20b + 6c/a, where "
                        + "a = ∑ᵢxᵢ², b = ∑ᵢxᵢ³ and c = ∑ᵢxᵢ⁴. "
                        + "The algebraic identity holds with total division even when R₁ or R₂ vanishes: "
                        + "those cases are handled separately before clearing denominators.")),
                    Paragraph(Text(
                        "For a positive vector x on Fin n with n ≥ 2, the squares are nonnegative "
                        + "and the square at i = 0 is positive, so Finset.sum_pos' gives a > 0. "
                        + "Positivity of the cubes gives b ≥ 0. "
                        + "Cauchy-Schwarz, in the form Finset.sum_mul_sq_le_sq_mul_sq, applied to x "
                        + "and its coordinatewise square gives b² ≤ ac. "
                        + "HermiteMomentBounds.sum_sq_lt_sq_sum applied to the positive coordinates "
                        + "yₗ = xₗ² gives ∑ₗyₗ² < (∑ₗyₗ)². "
                        + "The power identity (xₗ²)² = xₗ⁴ then gives c < a².")),
                    Paragraph(Text(
                        "Put C = lowerBound and f(u) = 15u⁴ - 20u³ + 6u². "
                        + "For u ≥ 0, direct expansion using (√5)² = 5 gives "
                        + "f(u) - C = (u - (5 + √5)/10)² "
                        + "[15u² + (3√5 - 5)u + (√5 - 1)/2]. "
                        + "The comparisons 5/3 ≤ √5 and 1 ≤ √5 show that the coefficients "
                        + "3√5 - 5 and (√5 - 1)/2 are nonnegative, "
                        + "so every factor on the right is nonnegative and f(u) ≥ C.")),
                    Paragraph(Text(
                        "Now suppose a > 0, b ≥ 0, b² ≤ ac and c < a², and set t = b/a. "
                        + "Then t ≥ 0, at = b, t² < a and at² ≤ c. Consequently "
                        + "15a² - 20b + 6c/a ≥ Q, where Q = 15a² - 20at + 6t². "
                        + "If t ≤ 2/3, then t² ≤ 4/9 and "
                        + "Q = (5/3)(3a - 2t)² - (2/3)t² ≥ -8/27. "
                        + "The relation (√5)² = 5 and √5 ≥ 0 gives C < -8/27, so Q > C. "
                        + "If t > 2/3, then 15(a + t²) - 20t > 0, since a > t² and "
                        + "t(3t - 2) > 0. Thus "
                        + "Q - f(t) = (a - t²)[15(a + t²) - 20t] > 0. "
                        + "Combining this with f(t) ≥ C again gives Q > C.")),
                    Paragraph(Text(
                        "For positive rates k, Finset.sum_pos' gives R₁ > 0 from the nonnegative "
                        + "inverse rates and the positive inverse rate at i = 0. "
                        + "The rescaled vector x is therefore positive. Applying its moment inequalities "
                        + "and the preceding estimate to the rescaled kurtosis identity proves "
                        + "lowerBound < kurtosis k for every n ≥ 2.")),
                    Paragraph(Text(
                        "To approach the bound, put A = (3 - √5)/2 and, for each natural m, take "
                        + "n = m + 2, k₀ = A/((m + 2 : ℕ) : ℝ) and kᵢ = 1 for i ≠ 0. "
                        + "Since √5 < 3, A > 0 and every rate is positive. "
                        + "For each natural j, their inverse-rate power sum is "
                        + "Rⱼ = (((m : ℝ) + 2)/A)ʲ + ((m : ℝ) + 1). "
                        + "Introduce the rational function "
                        + "F(a,t) = 15(1 + a²(t - t²))²/(1 + a - at)⁴ "
                        + "- 20(1 + a³(t² - t³))/(1 + a - at)³ "
                        + "+ 6(1 + a⁴(t³ - t⁴))/[(1 + a - at)²(1 + a²(t - t²))]. "
                        + "Substitution of the power sums and clearing positive denominators gives "
                        + "kurtosis k = F(A,1/((m + 2 : ℕ) : ℝ)). "
                        + "Indeed 0 < 1/((m + 2 : ℕ) : ℝ) ≤ 1, so both "
                        + "1 + A - A/((m + 2 : ℕ) : ℝ) and "
                        + "1 + A²(1/((m + 2 : ℕ) : ℝ) - (1/((m + 2 : ℕ) : ℝ))²) are positive.")),
                    Paragraph(Text(
                        "The function F(A,t) is continuous at t = 0, since its denominators there "
                        + "are powers of 1 + A > 0 and the factor 1. "
                        + "As m tends to infinity, 1/((m + 2 : ℕ) : ℝ) tends to zero. "
                        + "Expanding F(A,0), substituting A = (3 - √5)/2 and reducing the powers "
                        + "(√5)² = 5, (√5)³ = 5√5, (√5)⁴ = 25 and (√5)⁵ = 25√5 "
                        + "gives F(A,0) = C. Hence the kurtosis values of these positive cycles tend to C.")),
                    Paragraph(Text(
                        "Finally, the strict inequality implies that C is a lower bound of the set "
                        + "of positive-cycle kurtosis values. If b is any other lower bound, it is at most "
                        + "each value in the explicit sequence. Passing to its limit gives b ≤ C. "
                        + "Thus C is the greatest lower bound, and the strict finite-cycle inequality "
                        + "shows that no finite positive cycle attains it."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ptaszynski-2022-unidirectional-kurtosis-lower-bound"),
                    ResolutionKind.Proved)))));

    private static Formula KurtosisFormula()
    {
        Formula inverseRates = LambdaOf("i", FinOf(X("n")),
            At(Qualified("Inv", "inv"), At(X("k"), X("i"))));
        Formula first = PowerSum(Natural(1), inverseRates);
        Formula second = PowerSum(Natural(2), inverseRates);
        Formula third = PowerSum(Natural(3), inverseRates);
        Formula fourth = PowerSum(Natural(4), inverseRates);
        return All("n", Naturals(), All("k", RateType(),
            Equal(Typed(At(Local("kurtosis"), X("k")), Reals()),
                Add(Subtract(
                    Divide(Multiply(Real(1, 5), Power(second, Natural(2))), Power(first, Natural(4))),
                    Divide(Multiply(Real(2, 0), third), Power(first, Natural(3)))),
                    Divide(Multiply(Real(6), fourth), Multiply(Power(first, Natural(2)), second))))));
    }

    private static Formula NormalizedFormula()
    {
        Formula rescaled = LambdaOf("i", FinOf(X("n")),
            Divide(At(Qualified("Inv", "inv"), At(X("k"), X("i"))),
                PowerSum(Natural(1), LambdaOf("j", FinOf(X("n")),
                    At(Qualified("Inv", "inv"), At(X("k"), X("j")))))));
        Formula second = PowerSum(Natural(2), rescaled);
        Formula third = PowerSum(Natural(3), rescaled);
        Formula fourth = PowerSum(Natural(4), rescaled);
        return All("n", Naturals(), All("k", RateType(),
            Equal(At(Local("kurtosis"), X("k")),
                Add(Subtract(Multiply(Real(1, 5), Power(second, Natural(2))),
                    Multiply(Real(2, 0), third)), Divide(Multiply(Real(6), fourth), second)))));
    }

    private static Formula MomentsFormula()
    {
        Formula second = PowerSum(Natural(2), X("x"));
        Formula third = PowerSum(Natural(3), X("x"));
        Formula fourth = PowerSum(Natural(4), X("x"));
        Formula positive = All("i", FinOf(X("n")), Less(Real(0), At(X("x"), X("i"))));
        return All("n", Naturals(), Implication(LessEqual(Natural(2), X("n")),
            All("x", RateType(), Implication(positive,
                Conjunction(Less(Real(0), second), Conjunction(LessEqual(Real(0), third),
                    Conjunction(LessEqual(Power(third, Natural(2)), Multiply(second, fourth)),
                        Less(fourth, Power(second, Natural(2))))))))));
    }

    private static Formula LowerBoundFormula() =>
        Equal(Typed(Local("lowerBound"), Reals()),
            Divide(new Formula.Negate(Parenthesized(
                Add(Real(1), At(Qualified("Real", "sqrt"), Real(5))))), Real(1, 0)));

    private static Formula ClaimBody()
    {
        Formula strict = All("n", Naturals(), Implication(LessEqual(Natural(2), X("n")),
            All("k", RateType(), Implication(PositiveRates(),
                Less(Local("lowerBound"), At(Local("kurtosis"), X("k")))))));
        Formula values = Seq(OpenBrace, Typed(X("s"), Reals()), Sp, Mid, Sp,
            Some("n", Naturals(), Conjunction(LessEqual(Natural(2), X("n")),
                Some("k", RateType(), Conjunction(PositiveRates(),
                    Equal(X("s"), At(Local("kurtosis"), X("k"))))))), CloseBrace);
        return Conjunction(strict, At(Qualified("IsGLB"), values, Local("lowerBound")));
    }

    private static Formula PositiveRates() =>
        All("i", FinOf(X("n")), Less(Real(0), At(X("k"), X("i"))));
    private static Formula PowerSum(Formula exponent, Formula function) =>
        At(Qualified("D5", "S3", "Quantum", "Transport", "StrongAbsorption", "Foundations", "powerSum"),
            X("n"), exponent, function);
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "StatisticalMechanics", "UnicyclicKurtosisLowerBound", name);
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
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
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
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Divide(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
}
