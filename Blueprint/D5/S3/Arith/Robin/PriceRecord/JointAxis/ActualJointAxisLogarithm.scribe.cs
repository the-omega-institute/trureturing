using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord.JointAxis;

internal sealed class ActualJointAxisLogarithmDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/Robin/PriceRecord/JointAxis/ActualJointAxisLogarithm";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal Robin floor budgets give a nonzero joint logarithm with inverse-square precision.",
        H("Joint logarithm at the actual Robin clock"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eventually-clock-joint-logarithm"),
                DeclarationHandle.Create(Gid + ".eventually_clock_joint_logarithm"),
                H("Eventual nonvanishing and upper bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("theorem eventually_clock_joint_logarithm {β κζ : ℝ} (hβ : 37 / 50 ≤ β ∧ β < 3 / 4) (hκζ : 0 < κζ) : "
                        + "∀ᶠ e : ℤ in atTop, ∀ {Lbar w : ℝ} {h : ℤ} {p : Fin 3 → ℤ}, let R := reference e; "
                        + "let Y := exp R; let K := transportConstant κζ; |R - Lbar| ≤ 1 → 1 ≤ h → (h : ℝ) ≤ exp (R / 50) → "
                        + "jointSquare (boxSizes β κζ Lbar) h p (coordinates Y) w ≤ (43 : ℝ) / 9 → "
                        + "let Ω := omegaThree (h : ℝ) (p 0 : ℝ) (p 1 : ℝ); Ω ≠ 0 ∧ "
                        + "|Ω| ≤ (50 * K + 1) * exp (-(R / 15)) / R ^ 2")),
                    Paragraph(Text(
                        "The literal floor-budget estimates put the two signed labels in a rectangle around the "
                        + "actual root phases. The third-to-second offset ratio converges to log 3 / log 2, which is "
                        + "strictly inside the integer cone. The root equations reduce the central value to signed "
                        + "cutoff residuals. After the denominator bound is applied, those residuals fit within "
                        + "exp(−R/15)/R². The cubic sensitivity of the first coordinate preserves the inverse-square "
                        + "precision of the second coordinate."))),
                DescribeRole.Theorem))));
}
