using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class FixedLayerShrinkingPrimeRosterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "FixedLayerShrinkingPrimeRoster",
        H("UNCOMPILED_UNACCEPTED source components"),
        Blocks(
            Paragraph(Text("SOURCE ONLY: UNCOMPILED_UNACCEPTED / RegUNVALIDATED. All proof bodies are uncompiled candidates. No Lean/Scribe/Reg build, kernel/axiom closure, lawful enrollment, source binding, official/RH acceptance, novelty or consensus is asserted. Ordinary Pro reasoning is fallible input. The final uniform paid-prefix repair, its uniform original-price consumer, and the optional elementary-energy consumer remain unfinished. The finite components must not be presented as those final theorems. Existing owners are imported with exact unapplied consumed-helper patches. Each public target has a faithful full-telescope typed Reg attempt; rejected lawful families, whole-family variation, sensitivity, observational dependence and exact source binding remain missing.")),
            Describe.Lean(
                DescribeId.Create("fixedlayershrinkingprimeroster-fixed-layer-shrinking-prime-roster"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.fixed_layer_shrinking_prime_roster"),
                H("fixed layer shrinking prime roster"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete candidate Lean telescope: theorem fixed_layer_shrinking_prime_roster {j : ℕ} (hj : 2 ≤ j) :     ∀ C : ℝ, 0 < C → ∃ T : ℝ, 1 < T ∧ ∀ X : ℝ, T ≤ X →       ∃ S : Finset ℕ,         C * log X ≤ (S.card : ℝ) ∧         (∀ p ∈ S, p.Prime ∧ cutoff j (referencePrice X) < (p : ℝ) ∧           (p : ℝ) ≤ cutoff j (referencePrice X) * (1 + 1 / log X ^ 4)) ∧         cutoff j (referencePrice X) / (2 * log X ^ 4) ≤           ∑ p ∈ S, log p"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-four-root-ratio"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.root_ratio"),
                H("root_ratio"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("UNCOMPILED_UNACCEPTED / RegUNVALIDATED. Exact full candidate statement: theorem root_ratio {j : ℕ} (hj : 2 ≤ j) :     Tendsto (fun X : ℝ => cutoff j (referencePrice X) / X ^ ((j : ℝ)⁻¹))       atTop (𝓝 ((j : ℝ) ^ ((j : ℝ)⁻¹)))"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-four-root-at-top"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.root_atTop"),
                H("root_atTop"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("UNCOMPILED_UNACCEPTED / RegUNVALIDATED. Exact full candidate statement: theorem root_atTop {j : ℕ} (hj : 2 ≤ j) :     Tendsto (fun X : ℝ => cutoff j (referencePrice X)) atTop atTop"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-four-root-log-ratio"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.root_log_ratio"),
                H("root_log_ratio"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("UNCOMPILED_UNACCEPTED / RegUNVALIDATED. Exact full candidate statement: theorem root_log_ratio {j : ℕ} (hj : 2 ≤ j) :     Tendsto (fun X : ℝ => log (cutoff j (referencePrice X)) / log X)       atTop (𝓝 ((j : ℝ)⁻¹))"))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-four-fixed-layer-shrinking-prime-roster-power"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/FixedLayerShrinkingPrimeRoster.fixed_layer_shrinking_prime_roster_power"),
                H("fixed_layer_shrinking_prime_roster_power"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("UNCOMPILED_UNACCEPTED / RegUNVALIDATED. Exact full candidate statement: theorem fixed_layer_shrinking_prime_roster_power {j : ℕ} (hj : 2 ≤ j)     (w d : ℕ) (hw : 0 < w) :     ∀ C : ℝ, 0 < C → ∃ T : ℝ, 1 < T ∧ ∀ X : ℝ, T ≤ X →       ∃ S : Finset ℕ,         C * log X ^ d ≤ (S.card : ℝ) ∧         (∀ p ∈ S, p.Prime ∧ cutoff j (referencePrice X) < (p : ℝ) ∧           (p : ℝ) ≤ cutoff j (referencePrice X) * (1 + 1 / log X ^ w)) ∧         cutoff j (referencePrice X) / (2 * log X ^ w) ≤           ∑ p ∈ S, log p"))),
                DescribeRole.Theorem)
        )));
}
