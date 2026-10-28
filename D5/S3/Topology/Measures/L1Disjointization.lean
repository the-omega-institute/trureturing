/- GID: D5/S3/Topology/Measures/L1Disjointization
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/L1Disjointization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Summable old-input losses give actual disjoint literal restrictions. -/

import D5.S3.Topology.Measures.L1Restriction
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Disjointization by removing the union of every later support. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory Topology
open scoped ENNReal NNReal

namespace D5.S3.Topology.Measures.L1Disjointization

open L1Restriction

universe u
variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Summably small effects of later supports yield actual pairwise disjoint
sets. Their literal complements differ in norm by a null sequence from the
original complements, and the original disjoint-mass limit is preserved. -/
theorem exists_disjoint_restrictions (f : ℕ → Lp ℝ 1 μ) (A : ℕ → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (α : ℝ)
    (hcross : ∀ i h, i < h → ‖restrict (A h) (hA h) (f i)‖ ≤ (1 / 2 : ℝ) ^ h)
    (hlim : Tendsto (fun i => ‖restrict (A i) (hA i) (f i)‖) atTop (𝓝 α)) :
    ∃ (E : ℕ → Set Ω) (hE : ∀ i, MeasurableSet (E i)),
      Pairwise (fun i j => Disjoint (E i) (E j)) ∧
      Tendsto (fun i => ‖restrict (E i) (hE i) (f i)‖) atTop (𝓝 α) ∧
      Tendsto (fun i => ‖restrict (E i)ᶜ (hE i).compl (f i) -
        restrict (A i)ᶜ (hA i).compl (f i)‖) atTop (𝓝 0) := by
  let U (i : ℕ) := ⋃ m : ℕ, A (i + 1 + m)
  have hU (i : ℕ) : MeasurableSet (U i) := MeasurableSet.iUnion (fun m => hA _)
  let E (i : ℕ) := A i \ U i
  have hE (i : ℕ) : MeasurableSet (E i) := (hA i).diff (hU i)
  let D (i : ℕ) := A i ∩ U i
  have hD (i : ℕ) : MeasurableSet (D i) := (hA i).inter (hU i)
  let e (i : ℕ) := restrict (D i) (hD i) (f i)
  have he (i : ℕ) : ‖e i‖ ≤ (1 / 2 : ℝ) ^ i := by
    have he' : ‖e i‖ₑ ≤ (2⁻¹ : ℝ≥0∞) ^ i := by
      calc
        _ = ∫⁻ x in D i, ‖f i x‖ₑ ∂μ := enorm_restrict _ _ _
        _ ≤ ∫⁻ x in U i, ‖f i x‖ₑ ∂μ :=
          lintegral_mono' (Measure.restrict_mono_set μ inter_subset_right) le_rfl
        _ ≤ ∑' m : ℕ, ∫⁻ x in A (i + 1 + m), ‖f i x‖ₑ ∂μ := lintegral_iUnion_le _ _
        _ = ∑' m : ℕ, ‖restrict (A (i + 1 + m)) (hA _) (f i)‖ₑ := by
          apply tsum_congr; intro m; exact (enorm_restrict _ _ _).symm
        _ ≤ ∑' m : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (i + 1 + m)) := by
          apply ENNReal.tsum_le_tsum; intro m
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hcross i _ (by omega))
        _ = ∑' m : ℕ, (2⁻¹ : ℝ≥0∞) ^ (i + 1 + m) := by
          apply tsum_congr; intro m
          rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (1 / 2 : ℝ)),
            ENNReal.ofReal_div_of_pos (by norm_num : 0 < (2 : ℝ))]
          norm_num
        _ = (2⁻¹ : ℝ≥0∞) ^ i := by
          simp only [pow_add, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two, pow_one]
          rw [mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
    have h := ENNReal.toReal_mono (show (2⁻¹ : ℝ≥0∞) ^ i ≠ ∞ by finiteness) he'
    simpa using h
  have hgeo : Tendsto (fun i : ℕ => (1 / 2 : ℝ) ^ i) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have helim : Tendsto (fun i => ‖e i‖) atTop (𝓝 0) := squeeze_zero (fun _ => norm_nonneg _) he hgeo
  have heqU (i : ℕ) : restrict (A i) (hA i) (f i) - restrict (E i) (hE i) (f i) = e i := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (restrict (A i) (hA i) (f i)) (restrict (E i) (hE i) (f i)),
      coe_restrict (A i) (hA i) (f i), coe_restrict (E i) (hE i) (f i),
      coe_restrict (D i) (hD i) (f i)] with x hs ha he hd
    rw [hs, Pi.sub_apply, ha, he, hd]
    by_cases hxa : x ∈ A i <;> by_cases hxu : x ∈ U i <;> simp [E, D, hxa, hxu]
  have heqW (i : ℕ) : restrict (E i)ᶜ (hE i).compl (f i) -
      restrict (A i)ᶜ (hA i).compl (f i) = e i := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (restrict (E i)ᶜ (hE i).compl (f i)) (restrict (A i)ᶜ (hA i).compl (f i)),
      coe_restrict (E i)ᶜ (hE i).compl (f i), coe_restrict (A i)ᶜ (hA i).compl (f i),
      coe_restrict (D i) (hD i) (f i)] with x hs he ha hd
    rw [hs, Pi.sub_apply, he, ha, hd]
    by_cases hxa : x ∈ A i <;> by_cases hxu : x ∈ U i <;> simp [E, D, hxa, hxu]
  refine ⟨E, hE, ?_, ?_, ?_⟩
  · apply (pairwise_disjoint_on E).2
    intro i j hij
    apply Set.disjoint_left.2
    intro x hxi hxj
    apply hxi.2
    apply mem_iUnion.2
    refine ⟨j - (i + 1), ?_⟩
    simpa only [show i + 1 + (j - (i + 1)) = j by omega] using hxj.1
  · have hd : Tendsto (fun i => dist ‖restrict (E i) (hE i) (f i)‖ ‖restrict (A i) (hA i) (f i)‖)
        atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => dist_nonneg) _ hgeo
      intro i
      refine (dist_norm_norm_le _ _).trans ?_
      rw [norm_sub_rev, heqU]
      exact he i
    apply tendsto_iff_dist_tendsto_zero.2
    apply squeeze_zero (fun _ => dist_nonneg) (fun i => dist_triangle _ _ _)
    simpa using hd.add (tendsto_iff_dist_tendsto_zero.1 hlim)
  · simpa only [heqW] using helim

end D5.S3.Topology.Measures.L1Disjointization
