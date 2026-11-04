using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class UnicyclicSkewnessMinusKurtosisUpperBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/ptaszynski2022skewness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every finite cycle size at least two and every positive real rate vector, S − K is at most B = 3(107 + 51√17)/2048; B is the least upper bound of all these actual values.",
        H("The exact upper endpoint of unicyclic skewness minus kurtosis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("upper-bound"), DeclarationHandle.Create(Prefix + "upperBound"),
                H("The source's upper endpoint"),
                StatementSource.FromAuthor(Disp(Equal(Typed(Local("upperBound"), Reals()),
                    Divide(Multiply(Real(3), Add(Real(1, 0, 7), Multiply(Real(5, 1),
                        At(Qualified("Real", "sqrt"), Real(1, 7))))), Real(2, 0, 4, 8))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The primary v4 main.tex display at line 432 and Figure 6 concern S − K and give "
                    + "B = 3(107 + 51√17)/2048 at A = (5 − √17)/4. The summary at line 133 instead "
                    + "prints K − S with the same rounded interval. That sign discrepancy is preserved: "
                    + "this result follows the detailed S − K display and Figure 6. Line 424 derives "
                    + "the displayed endpoint analytically on the asymptotic family a = A/N, while "
                    + "line 792 calls the proposed universal extremal topology numerical/conjectural."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("All rates and the realized least upper bound"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The first clause quantifies over every natural n ≥ 2 and every k : Fin n → ℝ "
                    + "with all coordinates strictly positive. Repeated rates retain their multiplicity. "
                    + "Both skewness and kurtosis use this same k. The second clause is IsLUB for "
                    + "exactly the values from those actual rate vectors, with no bound on n. It does "
                    + "not replace realizable vectors by abstract moment triples. No extremal-topology "
                    + "assumption, rational-rate restriction or finite dimension cutoff is imposed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalized-difference"),
                DeclarationHandle.Create(Prefix + "normalized_difference"),
                H("The common normalized difference"),
                StatementSource.FromAuthor(Disp(NormalizedDifferenceFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every finite real rate vector, S − K equals −12p² + 18q − 6r/p, "
                    + "where p, q and r are the second, third and fourth power sums of the same "
                    + "normalized inverse-rate vector. The identity uses total real division; "
                    + "positivity is required by the extremal bounds, not by this identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The universal upper bound and sharpness"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The reused definitions are S(k) = 3R₂²/R₁⁴ − 2R₃/R₁³ and "
                        + "K(k) = 15R₂²/R₁⁴ − 20R₃/R₁³ + 6R₄/(R₁²R₂), where "
                        + "Rⱼ = ∑ᵢ kᵢ⁻ʲ. These are ratios of scaled current cumulants, not "
                        + "standardized central moments. Their original normalization identities and "
                        + "normalized_moments give, on xᵢ = kᵢ⁻¹/R₁, the joint facts "
                        + "a = ∑xᵢ² > 0, b = ∑xᵢ³ ≥ 0, b² ≤ ac and c = ∑xᵢ⁴ < a². "
                        + "The common-vector expression is S − K = −12a² + 18b − 6c/a.")),
                    Paragraph(Text(
                        "Put t = b/a. Then t ≥ 0, t² < a and c/a ≥ t², so "
                        + "S − K ≤ −12a² + 18at − 6t². For t ≤ 3/4, completing the square "
                        + "gives −12(a − 3t/4)² + 3t²/4 ≤ 27/64 ≤ B. For t > 3/4, "
                        + "the difference between f(t) = −12t⁴ + 18t³ − 6t² and that expression "
                        + "is (a − t²)[12(a + t²) − 18t] ≥ 0. The factorization "
                        + "B − f(t) = (t − (9 + √17)/16)² "
                        + "[12t² + ((3√17 − 9)/2)t + (9√17 − 15)/32] "
                        + "is nonnegative for t ≥ 0. This proves the bound on every admissible vector.")),
                    Paragraph(Text(
                        "For sharpness set u = (9 + √17)/16, so 0 < u < 1. For each natural m, "
                        + "choose n = m + 2 and the actual positive rates k₀ = 1/u and "
                        + "kᵢ = (m + 1)/(1 − u) for i ≠ 0. Their inverse rates sum to one: "
                        + "x₀ = u and the m + 1 remaining coordinates equal (1 − u)/(m + 1). "
                        + "For j = 2,3,4 the power sum is uʲ + (1 − u)ʲ/(m + 1)ʲ⁻¹. "
                        + "With z = 1/(m + 1), substitution gives "
                        + "−12[u² + (1 − u)²z]² + 18[u³ + (1 − u)³z²] "
                        + "− 6[u⁴ + (1 − u)⁴z³]/[u² + (1 − u)²z]. "
                        + "Its denominator at zero is u² > 0; continuity and z → 0 give "
                        + "the limit f(u) = B. Every term belongs to the exact set in claim. "
                        + "Any upper bound of that set bounds this sequence, and passing to the limit "
                        + "makes it at least B. Hence B is IsLUB.")),
                    Paragraph(Text(
                        "The finite parametrization just used differs from the source's a = A/N. "
                        + "Dividing our rates by their common tail rate gives exceptional rate "
                        + "a = (1 − u)/(u(N − 1)) = A/(N − 1), with "
                        + "A = (1 − u)/u = (5 − √17)/4. Its ratio to A/N is N/(N − 1), "
                        + "which tends to one. The proof evaluates our finite vectors directly; "
                        + "it uses neither an identification of the two finite families nor an "
                        + "unproved classification of extremal topologies.")),
                    Paragraph(Text(
                        "For n = 2 the physical interpretation uses two successive oriented phase "
                        + "stages and counts one marked winding crossing. The Lean result proves "
                        + "the inverse-rate formulas on positive vectors; it constructs no stochastic "
                        + "process and asserts no renewal theorem or empirical realization. There is "
                        + "no physical n = 1 claim. Bidirectional and multicyclic networks, finite-time "
                        + "cumulants, and standardized moments are outside this statement. Published "
                        + "no-hit claims are restricted to the independently inspected scopes; the "
                        + "unread journal body, unchecked citation-list memberships and global "
                        + "theorem-equivalence search remain limitations."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ptaszynski-2022-unidirectional-skewness-minus-kurtosis-upper-bound"),
                    ResolutionKind.Proved)))));

    private static Formula ClaimBody()
    {
        Formula bound = All("n", Naturals(), Implication(LessEqual(Natural(2), X("n")),
            All("k", RateType(), Implication(PositiveRates(),
                LessEqual(DifferenceValue(), Local("upperBound"))))));
        Formula values = Seq(OpenBrace, Typed(X("s"), Reals()), Sp, Mid, Sp,
            Some("n", Naturals(), Conjunction(LessEqual(Natural(2), X("n")),
                Some("k", RateType(), Conjunction(PositiveRates(), Equal(X("s"), DifferenceValue()))))),
            CloseBrace);
        return Conjunction(bound, At(Qualified("IsLUB"), values, Local("upperBound")));
    }

    private static Formula NormalizedDifferenceFormula()
    {
        Formula p = At(Qualified("D5", "S3", "StatisticalMechanics",
            "UnicyclicSkewnessPlusKurtosisLowerBound", "p"), X("k"));
        Formula q = At(Qualified("D5", "S3", "StatisticalMechanics",
            "UnicyclicSkewnessPlusKurtosisLowerBound", "q"), X("k"));
        Formula r = At(Qualified("D5", "S3", "StatisticalMechanics",
            "UnicyclicSkewnessPlusKurtosisLowerBound", "r"), X("k"));
        return All("n", Naturals(), All("k", RateType(), Equal(DifferenceValue(),
            Subtract(Add(Multiply(new Formula.Negate(Real(1, 2)),
                    new Formula.Power(Parenthesized(p), Natural(2))), Multiply(Real(1, 8), q)),
                Divide(Multiply(Real(6), r), p)))));
    }

    private static Formula DifferenceValue() => Subtract(
        At(Qualified("D5", "S3", "StatisticalMechanics", "UnicyclicSkewnessMinimum", "skewness"), X("k")),
        At(Qualified("D5", "S3", "StatisticalMechanics", "UnicyclicKurtosisLowerBound", "kurtosis"), X("k")));
    private static Formula PositiveRates() =>
        All("i", FinOf(X("n")), Less(Real(0), At(X("k"), X("i"))));
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "StatisticalMechanics", "UnicyclicSkewnessMinusKurtosisUpperBound", name);
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
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Divide(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
}
