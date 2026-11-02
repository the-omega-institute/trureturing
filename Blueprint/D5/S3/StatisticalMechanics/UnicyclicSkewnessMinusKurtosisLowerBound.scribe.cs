using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

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
                StatementSource.FromLean(),
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
                StatementSource.FromLean(),
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
                StatementSource.FromLean(),
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
                        + "with one marked winding crossing. The theorem proves the rational inverse-rate "
                        + "expressions; it constructs no stochastic process, renewal identification or "
                        + "empirical correspondence. Physical N = 1, bidirectional, thermal and multicyclic "
                        + "networks and finite-time cumulants are outside its scope. Bounded source and "
                        + "literature searches do not establish worldwide openness or priority."))),
                DescribeRole.Theorem))));
}
