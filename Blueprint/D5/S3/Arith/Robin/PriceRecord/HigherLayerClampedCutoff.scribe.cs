using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class HigherLayerClampedCutoffDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constructed strict cutoff with the lower boundary retained.",
        H("Constructed strict cutoff with the lower boundary retained"),
        Blocks(
            Paragraph(Text("The cutoff is constructed by the intermediate value theorem when eta<beta_j(2), and otherwise equals 2. Occupancy is eta<beta_j(u) iff u<cutoff, including u=2 and zero-margin roots. Both prices remain positive for 0<s<=1/2. Integrated slope and log((1+s)/(1-s))<=3s give movement<=9s x_minus/j. For every active layer and X>=exp(2), the actual lower-price root is <=(2jX)^(1/j)<=2X^(1/j), and j<6 log X. The finite active-layer cardinality and the sum x_minus/j<37 sqrt(X) are proved uniformly in all j. Integer counting uses only the finite set minimum and maximum and Nat.card_Icc, giving length+1, with no estimate of prime density or prime gaps.")),
            Describe.Lean(
                DescribeId.Create("higherlayerclampedcutoff-root-exists"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.root_exists"),
                H("root exists"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem root_exists {j : ℕ} (hj : 2 ≤ j) {η : ℝ} (hη : 0 < η) (hactive : η < beta j 2) : ∃ u : ℝ, 2 < u ∧ beta j u = η"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerclampedcutoff-cutoff-spec"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.cutoff_spec"),
                H("cutoff spec"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem cutoff_spec {j : ℕ} (hj : 2 ≤ j) {η : ℝ} (hη : 0 < η) : 2 ≤ cutoff j η ∧ beta j (cutoff j η) ≤ η ∧ (2 < cutoff j η → beta j (cutoff j η) = η) ∧ (η < beta j 2 ↔ 2 < cutoff j η)"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerclampedcutoff-cutoff-antitone"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.cutoff_antitone"),
                H("cutoff antitone"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem cutoff_antitone {j : ℕ} (hj : 2 ≤ j) {η ζ : ℝ} (hη : 0 < η) (hζ : 0 < ζ) (hηζ : η ≤ ζ) : cutoff j ζ ≤ cutoff j η"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerclampedcutoff-cutoff-occupancy"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.cutoff_occupancy"),
                H("cutoff occupancy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem cutoff_occupancy {j : ℕ} (hj : 2 ≤ j) {η u : ℝ} (hη : 0 < η) (hu : 2 ≤ u) : η < beta j u ↔ u < cutoff j η"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerclampedcutoff-log-price-ratio-le"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.log_price_ratio_le"),
                H("log price ratio le"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem log_price_ratio_le {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) : log ((1 + s) / (1 - s)) ≤ 3 * s"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerclampedcutoff-cutoff-movement"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.cutoff_movement"),
                H("cutoff movement"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem cutoff_movement {j : ℕ} (hj : 2 ≤ j) {«λ» s : ℝ} («hλ» : 0 < «λ») (hs : 0 < s) (hs2 : s ≤ 1 / 2) : cutoff j ((1 - s) * «λ») - cutoff j ((1 + s) * «λ») ≤ 9 * s * cutoff j ((1 - s) * «λ») / j"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerclampedcutoff-two-mul-index-le-two-pow"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.two_mul_index_le_two_pow"),
                H("two mul index le two pow"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem two_mul_index_le_two_pow {j : ℕ} (hj : 2 ≤ j) : 2 * j ≤ 2 ^ j"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerclampedcutoff-active-root-bounds"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.active_root_bounds"),
                H("active root bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem active_root_bounds {X s : ℝ} (hX : exp 2 ≤ X) (hs : 0 < s) (hs2 : s ≤ 1 / 2) {j : ℕ} (hj : 2 ≤ j) (hactive : 2 < cutoff j ((1 - s) / (X * log X))) : cutoff j ((1 - s) / (X * log X)) ≤ (2 * j * X) ^ (1 / (j : ℝ)) ∧ (2 * j * X) ^ (1 / (j : ℝ)) ≤ 2 * X ^ (1 / (j : ℝ)) ∧ (j : ℝ) < 6 * log X"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerclampedcutoff-log-cuberoot-lt-three-sqrt"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.log_cuberoot_lt_three_sqrt"),
                H("log cuberoot lt three sqrt"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem log_cuberoot_lt_three_sqrt {X : ℝ} (hX : exp 2 ≤ X) : log X * X ^ (1 / 3 : ℝ) < 3 * sqrt X"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerclampedcutoff-integer-interval-card"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.integer_interval_card"),
                H("integer interval card"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem integer_interval_card (S : Finset ℕ) {a b : ℝ} (hab : a ≤ b) (hS : ∀ p ∈ S, a ≤ (p : ℝ) ∧ (p : ℝ) < b) : (S.card : ℝ) ≤ b - a + 1"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerclampedcutoff-active-layer-card"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.active_layer_card"),
                H("active layer card"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem active_layer_card {X s : ℝ} (hX : exp 2 ≤ X) (hs : 0 < s) (hs2 : s ≤ 1 / 2) (J : Finset ℕ) (hJ : ∀ j ∈ J, 2 ≤ j ∧ 2 < cutoff j ((1 - s) / (X * log X))) : (J.card : ℝ) ≤ 6 * log X"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("higherlayerclampedcutoff-active-cutoff-sum"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/HigherLayerClampedCutoff.active_cutoff_sum"),
                H("active cutoff sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete Lean statement: theorem active_cutoff_sum {X s : ℝ} (hX : exp 2 ≤ X) (hs : 0 < s) (hs2 : s ≤ 1 / 2) (J : Finset ℕ) (hJ : ∀ j ∈ J, 2 ≤ j ∧ 2 < cutoff j ((1 - s) / (X * log X))) : (∑ j ∈ J, cutoff j ((1 - s) / (X * log X)) / j) < 37 * sqrt X"))),
                DescribeRole.Theorem)
        )));
}
