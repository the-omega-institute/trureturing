/- GID: D5/S3/Arith/Robin/PriceRecord/HigherLayerInsertionRegret
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/HigherLayerInsertionRegret
   mirror-E: none(waiver:elementary-differential-inequality)
   anchors: []
   utility: none
   digest: Actual higher-layer insertion regret in a shrinking multiplicative window. -/
import D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
import Mathlib.Tactic

/-! UNCOMPILED_UNACCEPTED. Reuses the actual real beta and its derivative.
The lower-slope owner is not copied or redefined.
Continuation revision: quote the reserved lambda identifier; the statement
and proof are otherwise inherited unchanged from the preserved component. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.HigherLayerInsertionRegret
open Real Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope

theorem slope_upper {u : ℝ} (hu : 2 ≤ u) {j : ℕ} (hj : 2 ≤ j) :
    logarithmicSlope j u ≤ 2 * j := by
  have hu0 : 0 < u := by linarith
  have hj1 : 1 ≤ j := by omega
  have hs := powerSum_pos hu0 hj1
  have hg := gain_pos hu0 hj1
  have hD : u * powerSumDerivative j u ≤ (j : ℝ) * powerSum j u := by
    calc
      _ = ∑ k ∈ range j, ((k + 1 : ℕ) : ℝ) * u ^ (k + 1) := by
        simp only [powerSumDerivative, mul_sum, pow_succ]
        apply sum_congr rfl
        intro k _
        push_cast
        ring
      _ ≤ ∑ k ∈ range j, (j : ℝ) * u ^ (k + 1) := by
        apply sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hu0.le _)
        exact_mod_cast (show k + 1 ≤ j by have := mem_range.mp hk; omega)
      _ = _ := by rw [← mul_sum]; rfl
  have hA : u * powerSumDerivative j u / powerSum j u ≤ j :=
    (div_le_iff₀ hs).mpr hD
  have hA0 : 0 ≤ u * powerSumDerivative j u / powerSum j u := by
    unfold powerSumDerivative
    positivity
  have hlog := one_sub_inv_le_log_of_pos (show 0 < 1 + 1 / powerSum j u by positivity)
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1 + 1 / powerSum j u by positivity)
  have hprod : (1 + 1 / powerSum j u) * (1 - (1 + 1 / powerSum j u)⁻¹) =
      1 / powerSum j u := by
    field_simp [hs.ne', (show 1 + 1 / powerSum j u ≠ 0 by positivity)] <;> ring
  rw [hprod] at hm
  have hB : (1 / powerSum j u) / ((1 + 1 / powerSum j u) * gain j u) ≤ 1 :=
    (div_le_one (mul_pos (by positivity) hg)).mpr hm
  have hB0 : 0 ≤ (1 / powerSum j u) / ((1 + 1 / powerSum j u) * gain j u) := by positivity
  have hmul := mul_le_mul hA hB hB0 (Nat.cast_nonneg j)
  have hlog2 : (1 / 2 : ℝ) < log 2 := by
    have h := lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 1)
    norm_num at h
    linarith
  have hlogu : 1 / 2 < log u := hlog2.trans_le (log_le_log (by norm_num) hu)
  have hrec : 1 / log u ≤ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < log u)).mpr
    linarith
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj
  dsimp [logarithmicSlope]
  nlinarith only [hmul, hrec, hj2]

theorem log_drop_upper {j : ℕ} (hj : 2 ≤ j) {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) :
    log (beta j u / beta j v) ≤ (2 * j : ℝ) * log (v / u) := by
  let f := fun t : ℝ => log (beta j t) + (2 * j : ℝ) * log t
  have hd (t : ℝ) (ht : 2 ≤ t) :
      HasDerivAt f (((2 * j : ℝ) - logarithmicSlope j t) / t) t := by
    convert (log_beta_hasDerivAt ht (by omega : 1 ≤ j)).add
      ((Real.hasDerivAt_log (by linarith : t ≠ 0)).const_mul (2 * j : ℝ)) using 1 <;> ring
  have hmono : MonotoneOn f (Set.Ici 2) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 2)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact div_nonneg (sub_nonneg.mpr (slope_upper (interior_subset ht) hj))
        (by have ht2 : 2 ≤ t := interior_subset ht; linarith)
  have h := hmono hu (hu.trans huv) huv
  dsimp [f] at h
  rw [log_div (beta_pos hu (by omega)).ne' (beta_pos (hu.trans huv) (by omega)).ne',
    log_div (by linarith : v ≠ 0) (by linarith : u ≠ 0)]
  linarith only [h]

/-- The actual arithmetic marginal, every fixed or varying layer j>=2,
including a zero window and both endpoint ties. The final full-loss consumer
multiplies this inequality by the positive prime logarithm. -/
theorem insertion_regret {j p : ℕ} (hj : 2 ≤ j) (hp : p.Prime)
    {u priceLambda κ : ℝ} (hu : 2 ≤ u) (hLambda : 0 < priceLambda) (hroot : beta j u = priceLambda)
    (hκ : 0 ≤ κ) (hpu : u ≤ (p : ℝ)) (hup : (p : ℝ) ≤ u * (1 + κ)) :
    0 ≤ priceLambda - goldenLayerMarginal p j ∧
      priceLambda - goldenLayerMarginal p j ≤ 2 * j * κ * priceLambda := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hb := beta_pos hp2 (by omega : 1 ≤ j)
  have hanti := (beta_strictAntiOn hj).antitoneOn hu hp2 hpu
  rw [hroot] at hanti
  have hdrop := log_drop_upper hj hu hpu
  rw [hroot] at hdrop
  have hbasic := one_sub_inv_le_log_of_pos (div_pos hLambda hb)
  have hround : log ((p : ℝ) / u) ≤ κ := by
    have hlog := log_le_sub_one_of_pos (div_pos (show (0 : ℝ) < p by exact_mod_cast hp.pos) (by linarith : 0 < u))
    have hrat : (p : ℝ) / u ≤ 1 + κ := (div_le_iff₀ (by linarith : 0 < u)).mpr (hup.trans_eq (mul_comm _ _))
    linarith only [hlog, hrat]
  have hlow : priceLambda - beta j (p : ℝ) ≤ priceLambda * log (priceLambda / beta j (p : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hbasic hLambda.le
    have he : priceLambda * (1 - (priceLambda / beta j (p : ℝ))⁻¹) = priceLambda - beta j (p : ℝ) := by
      field_simp [hLambda.ne', hb.ne'] <;> ring
    rwa [he] at hh
  have hlog := mul_le_mul_of_nonneg_left hdrop hLambda.le
  have hwin := mul_le_mul_of_nonneg_left hround (show 0 ≤ priceLambda * (2 * j : ℝ) by positivity)
  rw [← beta_nat hp (by omega : 1 ≤ j)]
  exact ⟨sub_nonneg.mpr hanti, by nlinarith only [hlow, hlog, hwin]⟩

#print axioms slope_upper
#print axioms log_drop_upper
#print axioms insertion_regret
end D5.S3.Arith.Robin.PriceRecord.HigherLayerInsertionRegret
