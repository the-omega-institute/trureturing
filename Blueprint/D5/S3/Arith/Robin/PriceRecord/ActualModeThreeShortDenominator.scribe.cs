using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualModeThreeShortDenominatorDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/ActualModeThreeShortDenominator";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual mode-three cutoff excludes short denominators satisfying both label error bounds.",
        H("Actual mode-three short-denominator exclusion"),
        Blocks(
            Paragraph(Text(
                "The real offset d j X is j log(cutoff j (referencePrice X)) − log X. "
                + "Here referencePrice X = 1 / (X log X), and cutoff is the existing higher-layer clamped cutoff. "
                + "For each fixed nonnegative K, the eventual threshold in X is uniform over all natural labels h, m and p.")),
            Describe.Lean(
                DescribeId.Create("eventually-mode-three-residual-bound"),
                DeclarationHandle.Create(Gid + ".eventually_mode_three_residual_bound"),
                H("Residual bound at the actual cutoff"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "theorem eventually_mode_three_residual_bound {K : ℝ} (hK : 0 ≤ K) : "
                        + "∀ᶠ X : ℝ in atTop, let L := log X; let x := L / d 2 X; let t := d 3 X / d 2 X; "
                        + "∀ h m p : ℕ, 0 < h → "
                        + "|(h : ℝ) * x - m| ≤ K * exp (-(L / 15)) → "
                        + "|(h : ℝ) * t - p| ≤ K * exp (-(L / 15)) / L ^ 2 → "
                        + "h < m ∧ h < p ∧ 5 * p ≤ 8 * h ∧ (m : ℝ) ≤ 2 * (h : ℝ) * L ∧ "
                        + "|(p : ℝ) * log (2 * (m : ℝ) / ((m : ℝ) + h)) - "
                        + "(h : ℝ) * log (3 * (m : ℝ) / ((m : ℝ) + p))| ≤ "
                        + "(2 * K + 6) * ((L ^ 2)⁻¹ * exp (-(L / 15)) + (h : ℝ) * exp (-(L / 3)))")),
                    Paragraph(Text(
                        "The two actual root equations identify the continuous logarithmic residual at (x,t) "
                        + "with η₃ − tη₂. The normalized gain bounds control |ηⱼ| by 2 exp(−L/j). "
                        + "The layer-offset limits give eventual bounds on x and t that transfer to m/h and p/h "
                        + "using the two label errors. Derivative estimates then compare the continuous residual "
                        + "to its value at (m/h,p/h). Multiplying that value by h yields the finite logarithmic expression."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("eventually-mode-three-short-denominator-exclusion"),
                DeclarationHandle.Create(Gid + ".eventually_mode_three_short_denominator_exclusion"),
                H("Exclusion for short denominators"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "theorem eventually_mode_three_short_denominator_exclusion {K : ℝ} (hK : 0 ≤ K) : "
                        + "∀ᶠ X : ℝ in atTop, let L := log X; let x := L / d 2 X; let t := d 3 X / d 2 X; "
                        + "∀ h m p : ℕ, 0 < h → (h : ℝ) ≤ L / (50 * log L) → "
                        + "¬ (|(h : ℝ) * x - m| ≤ K * exp (-(L / 15)) ∧ "
                        + "|(h : ℝ) * t - p| ≤ K * exp (-(L / 15)) / L ^ 2)")),
                    Paragraph(Text(
                        "With C = 2K + 6, combine the eventual residual bound with L ≥ exp 50 "
                        + "and L > 1500 log(2C). The resulting label inequalities and logarithmic bound "
                        + "are the hypotheses of mode_three_short_denominator_exclusion in ExactRationalCutoffSeparation."))),
                DescribeRole.Theorem))));
}
