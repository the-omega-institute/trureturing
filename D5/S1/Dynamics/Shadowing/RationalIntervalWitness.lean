/- GID: D5/S1/Dynamics/Shadowing/RationalIntervalWitness
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/RationalIntervalWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal weighted-sum failures of self-tuning on every positive closed restriction. -/

import D5.S1.Dynamics.Shadowing.RationalIntervalPhaseMemory
import D5.S1.Dynamics.Shadowing.RationalIntervalWeightedDistance

/-! The witness family uses the unchanged full closed domains and the literal distance sum. -/

open Set Filter
open scoped Topology BigOperators

namespace D5.S1.Dynamics.Shadowing.RationalInterval

private noncomputable def midpoint : I := ⟨1 / 2, by norm_num⟩
private def bottom : I := ⟨0, by norm_num⟩

private noncomputable def smallPoint (m : ℕ) : I :=
  ⟨(1 / 2 : ℝ) ^ m, by positivity,
    pow_le_one₀ (by norm_num) (by norm_num)⟩

private theorem midpoint_orbit (k : ℤ) :
    ((f ^ k) midpoint : ℝ) = (2 : ℝ) ^ k / (1 + (2 : ℝ) ^ k) := by
  rw [f_zpow, homeomorph_apply, action_coe]
  dsimp [midpoint]
  have hp : 0 < (2 : ℝ) ^ k := by positivity
  field_simp
  ring

private theorem midpoint_negative (n : ℕ) :
    ((f ^ (-(n : ℤ))) midpoint : ℝ) = 1 / ((2 : ℝ) ^ n + 1) := by
  rw [midpoint_orbit, zpow_neg, zpow_natCast]
  have hp : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

private theorem midpoint_marker (k : ℤ) :
    ((1 / 3 : ℝ) < (f ^ k) midpoint ∧ ((f ^ k) midpoint : ℝ) < 2 / 3) ↔ k = 0 := by
  rw [midpoint_orbit]
  have hp : 0 < (2 : ℝ) ^ k := by positivity
  constructor
  · rintro ⟨hl, hu⟩
    have hlo := (lt_div_iff₀ (by linarith : 0 < 1 + (2 : ℝ) ^ k)).mp hl
    have hup := (div_lt_iff₀ (by linarith : 0 < 1 + (2 : ℝ) ^ k)).mp hu
    have ha : (2 : ℝ) ^ (-1 : ℤ) < (2 : ℝ) ^ k := by norm_num; linarith
    have hb : (2 : ℝ) ^ k < (2 : ℝ) ^ (1 : ℤ) := by norm_num; linarith
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp ha
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hb
    omega
  · rintro rfl
    norm_num

private theorem smallPoint_image (m : ℕ) :
    (f (smallPoint m) : ℝ) = 2 / ((2 : ℝ) ^ m + 1) := by
  rw [f_coe]
  change 2 * (1 / 2 : ℝ) ^ m / (1 + (1 / 2 : ℝ) ^ m) = _
  rw [one_div, inv_pow]
  have hp : (2 : ℝ) ^ m ≠ 0 := by positivity
  field_simp

/-- The early error depends only on `m`; the genuine tail starts at `n`. -/
noncomputable def witnessSequence (m n : ℕ) (k : ℤ) : I :=
  if k = -1 then smallPoint m
  else if (n : ℤ) ≤ k then (f ^ (k - 2 * (n : ℤ))) midpoint else bottom

private theorem witness_early (m n : ℕ) (k : ℤ) (hk : k < (n : ℤ)) (h : k ≠ -1) :
    witnessSequence m n k = bottom := by simp [witnessSequence, h, not_le.mpr hk]

private theorem witness_tail (m n : ℕ) (hn : 1 ≤ n) (k : ℤ) (hk : (n : ℤ) ≤ k) :
    witnessSequence m n k = (f ^ (k - 2 * (n : ℤ))) midpoint := by
  simp [witnessSequence, show k ≠ -1 by omega, hk]

/-- All errors, including the three distinct exceptional indices when `n=1`. -/
theorem witness_link_errors (m n : ℕ) (hn : 1 ≤ n) (k : ℤ) :
    CompactSelector.linkError f (witnessSequence m n) k =
      if k = -2 then (1 / 2 : ℝ) ^ m
      else if k = -1 then 2 / ((2 : ℝ) ^ m + 1)
      else if k = (n : ℤ) - 1 then 1 / ((2 : ℝ) ^ n + 1) else 0 := by
  have hf0 : f bottom = bottom := action_zero 2 (by norm_num)
  by_cases h₂ : k = -2
  · subst k
    rw [ite_eq_left rfl]
    simp only [CompactSelector.linkError]
    norm_num only [show (-2 : ℤ) + 1 = -1 by omega]
    rw [show witnessSequence m n (-1) = smallPoint m by simp [witnessSequence],
      witness_early m n (-2) (by omega) (by omega), hf0]
    rw [Subtype.dist_eq, Real.dist_eq]
    change |(1 / 2 : ℝ) ^ m - 0| = _
    rw [sub_zero, abs_of_nonneg (by positivity)]
  rw [ite_eq_right h₂]
  by_cases h₁ : k = -1
  · subst k
    rw [ite_eq_left rfl]
    simp only [CompactSelector.linkError]
    rw [show (-1 : ℤ) + 1 = 0 by omega, witness_early m n 0 (by omega) (by omega),
      show witnessSequence m n (-1) = smallPoint m by simp [witnessSequence]]
    rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
    change |(f (smallPoint m) : ℝ) - 0| = _
    rw [sub_zero, abs_of_nonneg (f (smallPoint m)).property.1, smallPoint_image]
  rw [ite_eq_right h₁]
  by_cases ht : k = (n : ℤ) - 1
  · subst k
    rw [ite_eq_left rfl]
    simp only [CompactSelector.linkError]
    rw [show (n : ℤ) - 1 + 1 = n by omega, witness_tail m n hn n (le_refl _),
      witness_early m n ((n : ℤ) - 1) (by omega) (by omega), hf0]
    rw [Subtype.dist_eq, Real.dist_eq]
    change |((f ^ ((n : ℤ) - 2 * n)) midpoint : ℝ) - 0| = _
    rw [sub_zero, abs_of_nonneg ((f ^ ((n : ℤ) - 2 * n)) midpoint).property.1,
      show (n : ℤ) - 2 * n = -(n : ℤ) by omega, midpoint_negative]
  rw [ite_eq_right ht]
  unfold CompactSelector.linkError
  by_cases hkn : (n : ℤ) ≤ k
  · rw [witness_tail m n hn k hkn, witness_tail m n hn (k + 1) (by omega)]
    have hs := CompactSelector.orbit_step f midpoint (k - 2 * (n : ℤ))
    rw [show k + 1 - 2 * (n : ℤ) = (k - 2 * n) + 1 by omega]
    exact dist_eq_zero.mpr hs
  · rw [witness_early m n k (by omega) h₁,
      witness_early m n (k + 1) (by omega) (by omega), hf0, dist_self]

private theorem transition_le (n : ℕ) :
    1 / ((2 : ℝ) ^ n + 1) ≤ (1 / 2 : ℝ) ^ n := by
  calc
    _ ≤ 1 / (2 : ℝ) ^ n := one_div_le_one_div_of_le (by positivity) (by linarith)
    _ = _ := by rw [one_div, one_div, inv_pow]

private theorem small_image_le (m : ℕ) :
    2 / ((2 : ℝ) ^ m + 1) ≤ 2 * (1 / 2 : ℝ) ^ m := by
  rw [← smallPoint_image, f_coe]
  change 2 * (1 / 2 : ℝ) ^ m / (1 + (1 / 2 : ℝ) ^ m) ≤ _
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [sq_nonneg ((1 / 2 : ℝ) ^ m)]

private theorem witness_mem {ρ : ℝ} (m n : ℕ) (hn : 1 ≤ n)
    (hm : 2 * (1 / 2 : ℝ) ^ m < ρ) (hpow : (1 / 2 : ℝ) ^ n < ρ) :
    CompactSelector.ClosedPseudoOrbit f ρ (witnessSequence m n) := by
  intro k
  rw [witness_link_errors m n hn k]
  split_ifs
  · have hp : 0 < (1 / 2 : ℝ) ^ m := by positivity
    linarith
  · exact (small_image_le m).trans hm.le
  · exact (transition_le n).trans hpow.le
  · have hp : 0 < (1 / 2 : ℝ) ^ n := by positivity
    linarith

private theorem witness_error_support (m n : ℕ) (hn : 1 ≤ n) :
    Function.support (CompactSelector.linkError f (witnessSequence m n)) =
      ({-2, -1, (n : ℤ) - 1} : Set ℤ) := by
  ext k
  simp only [Function.mem_support, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [witness_link_errors m n hn k]
  have hp : (1 / 2 : ℝ) ^ m ≠ 0 := by positivity
  have hm : (2 : ℝ) ^ m + 1 ≠ 0 := by positivity
  have hn' : (2 : ℝ) ^ n + 1 ≠ 0 := by positivity
  split_ifs <;> simp_all

/-- The unique open-band marker is exactly the center `2n`. -/
theorem witness_marker (m n : ℕ) (hm : 3 ≤ m) (hn : 1 ≤ n) :
    bandMarkers (fun k => (witnessSequence m n k : ℝ)) (1 / 3) (2 / 3) =
      ({2 * (n : ℤ)} : Set ℤ) ∧
      (witnessSequence m n (2 * (n : ℤ) - 1) : ℝ) = 1 / 3 ∧
      (witnessSequence m n (2 * (n : ℤ) + 1) : ℝ) = 2 / 3 := by
  refine ⟨?_, ?_, ?_⟩
  · have hp : (1 / 2 : ℝ) ^ m ≤ 1 / 8 := by
      convert pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1) hm using 1
      norm_num
    ext k
    change ((1 / 3 : ℝ) < witnessSequence m n k ∧
      (witnessSequence m n k : ℝ) < 2 / 3) ↔ k = 2 * (n : ℤ)
    by_cases he : k = -1
    · subst k
      rw [show witnessSequence m n (-1) = smallPoint m by simp [witnessSequence]]
      change ((1 / 3 : ℝ) < (1 / 2 : ℝ) ^ m ∧ (1 / 2 : ℝ) ^ m < 2 / 3) ↔ _
      constructor
      · intro h
        linarith [h.1]
      · omega
    by_cases hk : (n : ℤ) ≤ k
    · rw [witness_tail m n hn k hk, midpoint_marker]
      omega
    · rw [witness_early m n k (by omega) he]
      change ((1 / 3 : ℝ) < 0 ∧ (0 : ℝ) < 2 / 3) ↔ k = 2 * (n : ℤ)
      constructor
      · norm_num
      · omega
  · rw [witness_tail m n hn _ (by omega),
      show 2 * (n : ℤ) - 1 - 2 * n = -1 by omega, midpoint_orbit]
    norm_num
  · rw [witness_tail m n hn _ (by omega),
      show 2 * (n : ℤ) + 1 - 2 * n = 1 by omega, midpoint_orbit]
    norm_num

private theorem witness_center (m n : ℕ) (hn : 1 ≤ n) :
    witnessSequence m n (2 * (n : ℤ)) = midpoint := by
  rw [witness_tail m n hn _ (by omega), sub_self, zpow_zero]
  rfl

private theorem witness_weight (m n : ℕ) (hm : 3 ≤ m) (hn : 1 ≤ n) (k : ℤ) :
    weight (witnessSequence m n k) = if k = 2 * (n : ℤ) then 1 / 36 else 0 := by
  by_cases hk : k = 2 * (n : ℤ)
  · subst k
    rw [ite_eq_left rfl, witness_center m n hn]
    norm_num [weight, midpoint]
  · rw [ite_eq_right hk]
    have hb : ¬ ((1 / 3 : ℝ) < witnessSequence m n k ∧
        (witnessSequence m n k : ℝ) < 2 / 3) := by
      have heq := (witness_marker m n hm hn).1
      intro h
      have : k ∈ bandMarkers (fun k => (witnessSequence m n k : ℝ)) (1 / 3) (2 / 3) := h
      rw [heq] at this
      exact hk this
    unfold weight
    apply max_eq_left
    rcases le_or_gt (witnessSequence m n k : ℝ) (1 / 3) with hl | hl
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    · have hu : (2 / 3 : ℝ) ≤ witnessSequence m n k := by push Not at hb; exact hb hl
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

private theorem witness_W {ρ : ℝ} (hρ : ρ ≤ (1 / 256 : ℝ))
    (m n : ℕ) (hm : 3 ≤ m) (hn : 1 ≤ n)
    (hx : CompactSelector.ClosedPseudoOrbit f ρ (witnessSequence m n)) :
    W (CompactSelector.inclusion f hρ ⟨witnessSequence m n, hx⟩) = 1 / 36 := by
  change (∑ᶠ k : ℤ, weight (witnessSequence m n k)) = _
  rw [finsum_eq_single _ (2 * (n : ℤ)) (fun k hk => by
    rw [witness_weight m n hm hn k, ite_eq_right hk]),
    witness_weight m n hm hn, ite_eq_left rfl]

private theorem witness_A {ρ : ℝ} (hρ : ρ ≤ (1 / 256 : ℝ))
    (m n : ℕ) (hm : 3 ≤ m) (hn : 1 ≤ n)
    (hx : CompactSelector.ClosedPseudoOrbit f ρ (witnessSequence m n)) :
    A (CompactSelector.inclusion f hρ ⟨witnessSequence m n, hx⟩) =
      (2 : ℝ) ^ (-(2 * (n : ℤ))) / 36 := by
  change (∑ᶠ k : ℤ, (2 : ℝ) ^ (-k) * weightedOdds (witnessSequence m n k)) = _
  rw [finsum_eq_single _ (2 * (n : ℤ)) (fun k hk => by
    simp [weightedOdds, witness_weight m n hm hn k, hk]), witness_center m n hn]
  norm_num [weightedOdds, weight, midpoint]
  ring

private theorem witness_R {ρ : ℝ} (hρ : ρ ≤ (1 / 256 : ℝ))
    (m n : ℕ) (hm : 3 ≤ m) (hn : 1 ≤ n)
    (hx : CompactSelector.ClosedPseudoOrbit f ρ (witnessSequence m n)) :
    R (CompactSelector.inclusion f hρ ⟨witnessSequence m n, hx⟩) =
      (f ^ (-(2 * (n : ℤ)))) midpoint := by
  apply Subtype.ext
  have hw := witness_W hρ m n hm hn hx
  have ha := witness_A hρ m n hm hn hx
  have hp : 0 < W (CompactSelector.inclusion f hρ ⟨witnessSequence m n, hx⟩) := by rw [hw]; norm_num
  simp only [R, dite_eq_left hp]
  rw [hw, ha, midpoint_orbit]
  simp [Q]

private theorem memory_shift_eq (x : P) (k : ℤ) :
    memory (CompactSelector.shift f k x) = CompactSelector.linkError f x.1 (k - 1) := by
  simp only [memory, CompactSelector.linkError, CompactSelector.shift_apply]
  simp only [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]

private theorem witness_memory {ρ : ℝ} (hρ : ρ ≤ (1 / 256 : ℝ))
    (m n : ℕ) (hn : 1 ≤ n)
    (hx : CompactSelector.ClosedPseudoOrbit f ρ (witnessSequence m n)) :
    memory (CompactSelector.inclusion f hρ ⟨witnessSequence m n, hx⟩) =
      2 / ((2 : ℝ) ^ m + 1) ∧
    memory (CompactSelector.shift f (2 * (n : ℤ))
      (CompactSelector.inclusion f hρ ⟨witnessSequence m n, hx⟩)) = 0 := by
  constructor
  · change CompactSelector.linkError f (witnessSequence m n) (-1) = _
    rw [witness_link_errors m n hn]
    norm_num
  · rw [memory_shift_eq]
    change CompactSelector.linkError f (witnessSequence m n) (2 * (n : ℤ) - 1) = _
    rw [witness_link_errors m n hn]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem witness_phase_center {ρ : ℝ} (hρ : ρ ≤ (1 / 256 : ℝ))
    (m n : ℕ) (hm : 3 ≤ m) (hn : 1 ≤ n)
    (hx : CompactSelector.ClosedPseudoOrbit f ρ (witnessSequence m n)) :
    (f ^ (2 * (n : ℤ)))
      (R (CompactSelector.inclusion f hρ ⟨witnessSequence m n, hx⟩)) = midpoint := by
  rw [witness_R hρ m n hm hn hx]
  change (f ^ (2 * (n : ℤ)) * f ^ (-(2 * (n : ℤ)))) midpoint = midpoint
  rw [← zpow_add, add_neg_cancel, zpow_zero]
  rfl

/-- The exact defect is positive and independent of the late transition `n`. -/
theorem witness_defect {ρ : ℝ} (hρ : ρ ≤ (1 / 256 : ℝ))
    (m n : ℕ) (hm : 3 ≤ m) (hn : 1 ≤ n)
    (hx : CompactSelector.ClosedPseudoOrbit f ρ (witnessSequence m n)) :
    let x := CompactSelector.inclusion f hρ ⟨witnessSequence m n, hx⟩
    dist ((f ^ (2 * (n : ℤ))) (T x))
      (T (CompactSelector.shift f (2 * (n : ℤ)) x)) = 1 / (2 * ((2 : ℝ) ^ m + 2)) := by
  dsimp only
  let x := CompactSelector.inclusion f hρ ⟨witnessSequence m n, hx⟩
  have hm₀ := witness_memory hρ m n hn hx
  have hr := witness_phase_center hρ m n hm hn hx
  change (f ^ (2 * (n : ℤ))) (R x) = midpoint at hr
  change memory x = _ ∧ memory (CompactSelector.shift f (2 * (n : ℤ)) x) = 0 at hm₀
  change dist ((f ^ (2 * (n : ℤ))) (T x))
    (T (CompactSelector.shift f (2 * (n : ℤ)) x)) = _
  rw [T_iterate]
  simp only [T, hm₀.2, R_shift, hr, add_zero, action_one]
  rw [Subtype.dist_eq, Real.dist_eq, action_displacement _ (by
    rw [hm₀.1]; positivity), hm₀.1]
  change |(2 / ((2 : ℝ) ^ m + 1)) * (1 / 2) * (1 - 1 / 2) /
    (1 + (2 / ((2 : ℝ) ^ m + 1)) * (1 / 2))| = _
  rw [abs_of_nonneg (by positivity)]
  have hp : 0 < (2 : ℝ) ^ m := by positivity
  field_simp
  ring

/-- Agreement on the complete half-line gives the bound for the actual sum. -/
theorem witness_weightedDistance (m n : ℕ) (hn : 1 ≤ n) :
    weightedDistance (fun j => witnessSequence m n (2 * (n : ℤ) + j))
      (CompactSelector.orbit f (witnessSequence m n (2 * (n : ℤ)))) ≤ (1 / 2 : ℝ) ^ n := by
  apply weightedDistance_le_negative_tail
  intro j hj
  rw [witness_center m n hn, witness_tail m n hn _ (by omega)]
  unfold CompactSelector.orbit
  congr 2
  omega

/-- Literal Definition 5.1 for the restriction of the same fixed `T` by inclusion. -/
def SelfTuningOn (ρ : ℝ) (hρ : ρ ≤ (1 / 256 : ℝ)) : Prop :=
  ∀ ε > 0, ∃ η > 0, ∀ (x : CompactSelector.Space f ρ) (k : ℤ),
    weightedDistance (CompactSelector.shift f k x).1 (CompactSelector.orbit f (x.1 k)) < η →
      dist ((f ^ k) (T (CompactSelector.inclusion f hρ x)))
        (T (CompactSelector.inclusion f hρ (CompactSelector.shift f k x))) ≤ ε

/-- Fix `m` and a positive defect once for `ρ`; only `n` varies with the threshold. -/
theorem T_every_rho_witness (ρ : ℝ) (hρ₀ : 0 < ρ) (hρ : ρ ≤ (1 / 256 : ℝ)) :
    ∃ m : ℕ, 3 ≤ m ∧ (2 : ℝ) ^ (1 - (m : ℤ)) < ρ ∧
      ∀ η > 0, ∃ n : ℕ, 1 ≤ n ∧ (1 / 2 : ℝ) ^ n < min ρ η ∧
        ∃ hx : CompactSelector.ClosedPseudoOrbit f ρ (witnessSequence m n),
          let x : CompactSelector.Space f ρ := ⟨witnessSequence m n, hx⟩
          (CompactSelector.linkError f x.1).HasFiniteSupport ∧
          weightedDistance (CompactSelector.shift f (2 * (n : ℤ)) x).1
            (CompactSelector.orbit f (x.1 (2 * (n : ℤ)))) < η ∧
          dist ((f ^ (2 * (n : ℤ))) (T (CompactSelector.inclusion f hρ x)))
            (T (CompactSelector.inclusion f hρ (CompactSelector.shift f (2 * (n : ℤ)) x))) =
              1 / (2 * ((2 : ℝ) ^ m + 2)) := by
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < ρ / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  let m := max 3 M
  have hm : 3 ≤ m := le_max_left _ _
  have hpm : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ M :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right _ _)
  have hsmall : 2 * (1 / 2 : ℝ) ^ m < ρ := by linarith
  refine ⟨m, hm, ?_, ?_⟩
  · convert hsmall using 1
    rw [zpow_sub₀ (by norm_num), zpow_one, zpow_natCast, div_eq_mul_inv,
      one_div, inv_pow]
  intro η hη
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (lt_min hρ₀ hη)
    (by norm_num : (1 / 2 : ℝ) < 1)
  let n := N + 1
  have hn : 1 ≤ n := by omega
  have hpn : (1 / 2 : ℝ) ^ n < min ρ η :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ N)).trans_lt hN
  have hx := witness_mem m n hn hsmall (hpn.trans_le (min_le_left _ _))
  refine ⟨n, hn, hpn, hx, ?_, ?_, ?_⟩
  · rw [Function.HasFiniteSupport, witness_error_support m n hn]
    exact Set.toFinite _
  · exact (witness_weightedDistance m n hn).trans_lt (hpn.trans_le (min_le_right _ _))
  · exact witness_defect hρ m n hm hn hx

/-- The same `T` fails self-tuning on every positive closed restriction. -/
theorem T_not_self_tuning_on (ρ : ℝ) (hρ₀ : 0 < ρ) (hρ : ρ ≤ (1 / 256 : ℝ)) :
    ¬ SelfTuningOn ρ hρ := by
  obtain ⟨m, hm, hsmall, hw⟩ := T_every_rho_witness ρ hρ₀ hρ
  let B : ℝ := 1 / (2 * ((2 : ℝ) ^ m + 2))
  have hB : 0 < B := by dsimp [B]; positivity
  intro hs
  obtain ⟨η, hη, hηprop⟩ := hs (B / 2) (by positivity)
  obtain ⟨n, hn, hpn, hx, _, hD, hd⟩ := hw η hη
  have hb := hηprop ⟨witnessSequence m n, hx⟩ (2 * (n : ℤ)) hD
  rw [hd] at hb
  change B ≤ B / 2 at hb
  linarith

#print axioms T_every_rho_witness
#print axioms T_not_self_tuning_on

end D5.S1.Dynamics.Shadowing.RationalInterval
