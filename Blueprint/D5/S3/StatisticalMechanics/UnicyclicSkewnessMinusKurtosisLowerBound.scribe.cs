using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class UnicyclicSkewnessMinusKurtosisLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisLowerBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/ptaszynski2022skewness");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every finite cycle size at least two and every strictly positive real rate vector, S − K is at least C = 3(107 − 51√17)/2048; C is the greatest lower bound of all actual values.",
        H("The exact lower endpoint of unicyclic skewness minus kurtosis"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lower-bound"), DeclarationHandle.Create(Prefix + "lowerBound"),
                H("The detailed source's lower endpoint"),
                StatementSource.FromAuthor(Disp(Equal(Typed(Local("lowerBound"), Reals()),
                    Divide(Multiply(Real(3), Subtract(Real(1, 0, 7), Multiply(Real(5, 1),
                        At(Qualified("Real", "sqrt"), Real(1, 7))))), Real(2, 0, 4, 8))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The primary arXiv v4 main.tex display at line 431 and Figure 6 concern S − K. "
                    + "The summary at line 133 instead labels the interval K − S. This sign conflict "
                    + "is retained: the present endpoint follows the detailed display and figure. "
                    + "Line 424 evaluates the asymptotic exceptional-rate family a = A/N with "
                    + "A = (5 + √17)/4. Line 417 and Appendix line 792 describe the universal "
                    + "extremal topology as numerical/conjectural; no such topology is a hypothesis."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Every positive vector and the entire actual value set"),
                StatementSource.FromAuthor(Disp(Equivalence(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The first clause includes every natural n ≥ 2 and every k : Fin n → ℝ "
                    + "with all coordinates strictly positive. The original skewness and kurtosis "
                    + "use the same vector, with repeated coordinates counted with multiplicity. "
                    + "The IsGLB clause uses exactly the values realized by these finite vectors, "
                    + "with unbounded n. It imposes neither a topology classification nor an "
                    + "abstract-moment realizability assumption."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The universal bound and its sharp actual approximation"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Write Rⱼ = ∑ᵢ kᵢ⁻ʲ. The original definitions are "
                        + "S = 3R₂²/R₁⁴ − 2R₃/R₁³ and "
                        + "K = 15R₂²/R₁⁴ − 20R₃/R₁³ + 6R₄/(R₁²R₂). "
                        + "They are scaled current cumulant ratios C₃/C₁ and C₄/C₂. "
                        + "They are not standardized central moments. The original normalized_simplex "
                        + "and normalized_difference apply to xᵢ = kᵢ⁻¹/R₁. With "
                        + "p = ∑xᵢ², q = ∑xᵢ³, r = ∑xᵢ⁴ and u = √p, they give "
                        + "∑xᵢ = 1, 0 < p, 0 ≤ xᵢ ≤ u ≤ 1 and D = S − K = −12p² + 18q − 6r/p.")),
                    Paragraph(Text(
                        "For u ≤ 1/3 the nonnegative sum ∑xᵢ²(u − xᵢ)(u + xᵢ − 3p) "
                        + "equals p[D − f(u)]/6, where f(u) = −12u⁴ + 18u³ − 6u². "
                        + "The factorization f(u) − C = (u − (9 − √17)/16)² "
                        + "[−12u² + (9 + 3√17)u/2 + (15 + 9√17)/32] is nonnegative "
                        + "on this interval. For u ≥ 1/3 put d = (3p − u)/2. The nonnegative "
                        + "sum ∑xᵢ(u − xᵢ)(xᵢ − d)² equals "
                        + "p[D + (3/2)u(1 − u)³]/6. Finally "
                        + "8/81 − u(1 − u)³ = (u − 1/3)[4/27 + "
                        + "(u − 1/3)(1 − u)(4/3 − u)] ≥ 0, so D ≥ −4/27 ≥ C. "
                        + "These are estimates on the original common finite vector.")),
                    Paragraph(Text(
                        "For sharpness let α = (9 − √17)/16, which lies strictly between zero and one. "
                        + "For every natural m take n = m + 2 and rates k₀ = 1/α and "
                        + "kᵢ = (m + 1)/(1 − α) for i ≠ 0. All rates are positive and their inverse "
                        + "rates sum to one. For j = 2,3,4 the exact moments are "
                        + "αʲ + (1 − α)ʲ/(m + 1)ʲ⁻¹. With z = 1/(m + 1), the difference is "
                        + "−12[α² + (1 − α)²z]² + 18[α³ + (1 − α)³z²] "
                        + "− 6[α⁴ + (1 − α)⁴z³]/[α² + (1 − α)²z]. "
                        + "The denominator at zero is α² > 0. Continuity and z → 0 give f(α) = C. "
                        + "Every term is an actual value in the asserted set, so every lower bound "
                        + "of that set is at most C.")),
                    Paragraph(Text(
                        "Dividing these rates by their common tail rate gives exceptional rate "
                        + "a = (1 − α)/(α(N − 1)) = A/(N − 1), with A = (5 + √17)/4. "
                        + "This finite family differs from the source's A/N, and their ratio "
                        + "N/(N − 1) tends to one. The proof directly evaluates its own finite "
                        + "vectors and requires no finite-family identification.")),
                    Paragraph(Text(
                        "For N = 2 the interpretation is two oriented, channel-labelled phase stages "
                        + "with one marked winding crossing; that physical identification is not explicitly supplied by the source notation. The theorem proves the rational inverse-rate "
                        + "expressions; it constructs no stochastic process, renewal identification or "
                        + "empirical correspondence. Physical N = 1, bidirectional, thermal and multicyclic "
                        + "networks and finite-time cumulants are outside its scope. The result claims neither "
                        + "strict finite inequality nor finite-N optimizer classification."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ptaszynski-skewness-minus-kurtosis-lower-bound"),
                    ResolutionKind.Proved)))));

    private static Formula ClaimBody()
    {
        Formula bound = All("n", Naturals(), Implication(LessEqual(Natural(2), X("n")),
            All("k", RateType(), Implication(PositiveRates(),
                LessEqual(Local("lowerBound"), DifferenceValue())))));
        Formula values = Seq(OpenBrace, Typed(X("s"), Reals()), Sp, Mid, Sp,
            Some("n", Naturals(), Conjunction(LessEqual(Natural(2), X("n")),
                Some("k", RateType(), Conjunction(PositiveRates(), Equal(X("s"), DifferenceValue()))))),
            CloseBrace);
        return Conjunction(bound, At(Qualified("IsGLB"), values, Local("lowerBound")));
    }

    private static Formula DifferenceValue() => Subtract(
        At(Qualified("D5", "S3", "StatisticalMechanics", "UnicyclicSkewnessMinimum", "skewness"), X("k")),
        At(Qualified("D5", "S3", "StatisticalMechanics", "UnicyclicKurtosisLowerBound", "kurtosis"), X("k")));
    private static Formula PositiveRates() =>
        All("i", FinOf(X("n")), Less(Real(0), At(X("k"), X("i"))));
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "StatisticalMechanics", "UnicyclicSkewnessMinusKurtosisLowerBound", name);
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
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Divide(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
}
