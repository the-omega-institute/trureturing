using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class HigherLossScalarAbsorptionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact sharp scalar reduction and two Young bounds.",
        H("Exact sharp scalar reduction and two Young bounds"),
        Blocks(
            Paragraph(Text("Assume the stated finite budget, V<=T, W<=Delta+delta, delta<=2log X, the logarithm comparison, and the coercivity estimate for Delta. Then R<=a T sqrt(R)/X^(5/4)+a(T/X)R+dTlog X/X^2+2/X, with a=12000 and d=24000. Absorption uses T=E+5sqrt X and the hypothesis aT/X<=1/4. The square (sqrt R/2-aT/X^(5/4))^2 absorbs the square-root term. A second Young square absorbs Tlog X/X^2. The log-squared rounding term is <=1/X eventually, proved through a standard logarithmic little-o limit. q=2a^2+d and finalConstant=52q+d+4 give the exact E^2/X^(5/2)+1/X rate.")),
            Describe.Lean(
                DescribeId.Create("higherlossscalarabsorption-scalar-budget-reduction"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLossScalarAbsorption.scalar_budget_reduction"),
                H("scalar budget reduction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement:\ntheorem scalar_budget_reduction {X T V W Δ δ R : ℝ}\n    (hX : exp 2 ≤ X) (hT : 0 ≤ T) (hV : 0 ≤ V) (hW : 0 ≤ W)\n    (hVT : V ≤ T) (hWΔ : W ≤ Δ + δ) (hδ0 : 0 ≤ δ)\n    (hδ : δ ≤ 2 * log X) (hhalf : log X / 2 ≤ log (X / 2))\n    (hR : R ≤ 6 * V * W / (X ^ 2 * log (X / 2)) + δ / (X * log X))\n    (hΔ : Δ ≤ 1000 * (X ^ (3 / 4 : ℝ) * log X * sqrt R +\n      X * log X * R + log X ^ 2)) :\n    R ≤ a * T / X ^ (5 / 4 : ℝ) * sqrt R + a * (T / X) * R +\n      d * T * log X / X ^ 2 + 2 / X"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlossscalarabsorption-scalar-absorption"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLossScalarAbsorption.scalar_absorption"),
                H("scalar absorption"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement:\ntheorem scalar_absorption {X E R : ℝ} (hX : 1 < X) (hE : 0 ≤ E) (hR0 : 0 ≤ R)\n    (hsmall : a * ((E + 5 * sqrt X) / X) ≤ 1 / 4)\n    (hlog : log X ^ 2 ≤ sqrt X)\n    (hR : R ≤ a * (E + 5 * sqrt X) / X ^ (5 / 4 : ℝ) * sqrt R +\n      a * ((E + 5 * sqrt X) / X) * R +\n      d * (E + 5 * sqrt X) * log X / X ^ 2 + 2 / X) :\n    R ≤ finalConstant * (E ^ 2 / X ^ (5 / 2 : ℝ) + 1 / X)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlossscalarabsorption-log-rounding-eventually"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLossScalarAbsorption.log_rounding_eventually"),
                H("log rounding eventually"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement:\ntheorem log_rounding_eventually : ∀ᶠ X : ℝ in atTop, log X ^ 2 ≤ sqrt X"))),
                DescribeRole.Theorem)
        )));
}
