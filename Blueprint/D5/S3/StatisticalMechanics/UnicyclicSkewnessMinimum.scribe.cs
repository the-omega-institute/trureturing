using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class UnicyclicSkewnessMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/ptaszynski2022skewness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every unidirectional cycle with at least two states, the least skewness of positive rates is attained when one rate is the reciprocal of the number of other rates.",
        H("The minimum skewness of a unidirectional cycle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("skewness"),
                DeclarationHandle.Create(Prefix + "skewness"),
                H("Skewness from inverse-rate power sums"),
                StatementSource.FromAuthor(Disp(SkewnessFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For n real rates k, powerSum n j sums the jth powers of its argument over Fin n. "
                    + "The displayed expression is the third scaled current cumulant divided by the first. "
                    + "The source defines this ratio in main.tex line 53; its Appendix gives the current "
                    + "and waiting-time cumulants in lines 772-789. Substituting those formulas gives "
                    + "the expression in inverse-rate power sums. The definition is a total real-valued "
                    + "function for every natural n and every real rate vector; the current interpretation "
                    + "and the minimum below concern positive rates on cycles with n at least two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("minimum-value"),
                DeclarationHandle.Create(Prefix + "minimumValue"),
                H("The finite-state minimum value"),
                StatementSource.FromAuthor(Disp(MinimumValueFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "This is the value in Section III E 1, main.tex line 420. The argument n is a "
                    + "natural number, and each occurrence of n in the rational expression is explicitly "
                    + "cast to the reals. The expression is defined for every n using real division; "
                    + "its asserted role as a minimum is restricted to n at least two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("An attained minimum over all positive rate vectors"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n at least two, minimumValue n belongs to the set of skewness "
                    + "values of positive vectors k indexed by Fin n and is no larger than any member "
                    + "of that set. Thus IsLeast includes both attainment and the universal lower bound. "
                    + "This expresses the skewness-minimum part of the extremal-topology conjecture "
                    + "in Section III E 1, main.tex lines 416-420, and the Appendix, line 792."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The sharp lower bound and its attaining rates"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "First normalize inverse rates. For n positive and k positive, let R be the sum "
                        + "of the inverse rates and set xᵢ = (kᵢ)⁻¹/R. Every inverse rate is positive, "
                        + "so this vector is nonnegative, nonzero before normalization, and has sum one. "
                        + "Dividing its power sums by the corresponding powers of R shows that the "
                        + "skewness equals F(x) = 3p² - 2q, where p = ∑ᵢ xᵢ² and q = ∑ᵢ xᵢ³.")),
                    Paragraph(Text(
                        "The algebraic estimate uses real numbers r, a, b, p, q with r ≥ 1, "
                        + "a + rb = 1, b ≤ a, a ≥ 0, p ≥ a² + rb², and "
                        + "q ≤ (a + 2b)p - 2ab - b² + (r + 1)ab². Set "
                        + "d = p - (a² + rb²), h = 3(a² + rb²)² - 2(a³ + rb³), "
                        + "and g = -(r² - 6r + 1)/(16r²). Then d ≥ 0, r > 0, "
                        + "b = (1 - a)/r, and z = (r + 1)a - 1 ≥ 0. Direct expansion gives "
                        + "h - g = (2a - 1)²[12z² + 4(r - 1)z + (r - 1)²]/(16r²), "
                        + "so h ≥ g. The upper bound for q also gives "
                        + "3p² - 2q ≥ h + 3d² + 2(a - b)(3a - 1)d.")),
                    Paragraph(Text(
                        "If 3a - 1 ≥ 0, every correction on the right is nonnegative, giving "
                        + "3p² - 2q ≥ g. If 3a - 1 < 0, the relations a + rb = 1 and b ≤ a "
                        + "imply r ≥ 2. Define "
                        + "u = 18(r + 1)a² + 3(r² - 2r - 12)a + r² - 8r + 18. "
                        + "For 2 ≤ r ≤ 8, the identity "
                        + "72(r + 1)u = [36(r + 1)a + 3(r² - 2r - 12)]² "
                        + "+ 9r(8 - r)(r - 2)² proves u ≥ 0. For r > 8, all three terms "
                        + "in the defining expression for u are nonnegative, again giving u ≥ 0.")),
                    Paragraph(Text(
                        "In this second case, another expansion gives "
                        + "h - (a - b)²(3a - 1)²/3 - g "
                        + "= (1/3 - a)u/(9r²) + [11(r - 2)² + 10(r - 2) + 3]/(432r²), "
                        + "which is nonnegative. Completing the remaining square yields "
                        + "h + 3d² + 2(a - b)(3a - 1)d - g "
                        + "= [h - (a - b)²(3a - 1)²/3 - g] "
                        + "+ [3d + (a - b)(3a - 1)]²/3 ≥ 0. "
                        + "This proves the algebraic estimate in both cases.")),
                    Paragraph(Text(
                        "Now let x be any point of the closed standard simplex on Fin n, with n ≥ 2. "
                        + "Choose i with maximal coordinate and put a = xᵢ, r = (n : ℝ) - 1, "
                        + "b = (1 - a)/r, p = ∑ⱼ xⱼ², q = ∑ⱼ xⱼ³. Then r ≥ 1 and "
                        + "a + rb = 1. Nonnegativity gives a ≥ 0, and summing xⱼ ≤ a gives "
                        + "1 ≤ (n : ℝ)a, hence b ≤ a. Expanding "
                        + "∑ⱼ(xⱼ - b)² = p - 2b + (n : ℝ)b² and retaining its ith term "
                        + "gives p ≥ a² + rb². Moreover each (a - xⱼ)(xⱼ - b)² is nonnegative. "
                        + "Their sum is -q + (a + 2b)p - (2ab + b²) + (n : ℝ)ab², "
                        + "which gives the required upper bound for q. Applying the algebraic estimate "
                        + "and substituting r = (n : ℝ) - 1 proves F(x) ≥ minimumValue n.")),
                    Paragraph(Text(
                        "For attainment, write n = m + 1, so m > 0, and take k₀ = (m : ℝ)⁻¹ "
                        + "and kᵢ = 1 for i ≠ 0. These rates are positive. For each natural j, "
                        + "the jth power sum of their inverse rates is (m : ℝ)ʲ + (m : ℝ). "
                        + "Substituting the first three such sums into the skewness formula and "
                        + "clearing the positive denominators gives skewness k = minimumValue n. "
                        + "Thus the rate vector is (1/(n - 1), 1, …, 1), and its normalized inverse "
                        + "rates are (1/2, 1/(2(n - 1)), …, 1/(2(n - 1))).")),
                    Paragraph(Text(
                        "Finally fix n ≥ 2. The explicit rates put minimumValue n in the set of "
                        + "positive-rate skewness values. For any member s, choose its positive rate "
                        + "vector k, replace its skewness by F of the normalized inverse rates, "
                        + "and apply the closed-simplex lower bound. Hence minimumValue n ≤ s, "
                        + "which proves IsLeast. The conclusion concerns the finite-n skewness "
                        + "minimum for positive rates on unidirectional cycles."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ptaszynski-2022-unicyclic-skewness-minimum"),
                    ResolutionKind.Proved)))));

    private static Formula SkewnessFormula()
    {
        Formula inverseRates = LambdaOf("i", FinOf(X("n")),
            At(Qualified("Inv", "inv"), At(X("k"), X("i"))));
        Formula first = PowerSum(D(1), inverseRates);
        Formula second = PowerSum(D(2), inverseRates);
        Formula third = PowerSum(D(3), inverseRates);
        return All("n", Naturals(), All("k", RateType(),
            Equal(Typed(At(Local("skewness"), X("k")), Reals()),
                Subtract(Divide(Multiply(D(3), Power(second, D(2))), Power(first, D(4))),
                    Divide(Multiply(D(2), third), Power(first, D(3)))))));
    }

    private static Formula MinimumValueFormula()
    {
        Formula nReal = Typed(At(Qualified("Nat", "cast"), X("n")), Reals());
        return All("n", Naturals(),
            Equal(Typed(At(Local("minimumValue"), X("n")), Reals()),
                Divide(new Formula.Negate(Parenthesized(
                        Add(Subtract(D(8), Multiply(D(8), nReal)), Power(nReal, D(2))))),
                    Multiply(D(1, 6), Power(Subtract(nReal, D(1)), D(2))))));
    }

    private static Formula ClaimBody()
    {
        Formula values = Seq(OpenBrace, Typed(X("s"), Reals()), Sp, Mid, Sp,
            Some("k", RateType(), Conjunction(
                All("i", FinOf(X("n")), Less(Typed(D(0), Reals()), At(X("k"), X("i")))),
                Equal(X("s"), At(Local("skewness"), X("k"))))), CloseBrace);
        return All("n", Naturals(), Implication(LessEqual(Typed(D(2), Naturals()), X("n")),
            At(Qualified("IsLeast"), values, At(Local("minimumValue"), X("n")))));
    }

    private static Formula PowerSum(Formula exponent, Formula function) =>
        At(Qualified("D5", "S3", "Quantum", "Transport", "StrongAbsorption", "Foundations", "powerSum"),
            X("n"), exponent, function);
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "StatisticalMechanics", "UnicyclicSkewnessMinimum", name);
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
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
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
