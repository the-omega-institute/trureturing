/- GID: D5/S3/Analytic/Oscillation/SparseOrdinateMass
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/SparseOrdinateMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse inclusive ordinate counts force vanishing normalized harmonic mass. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Dyadic mass estimates for a locally finite positive spectrum. -/

set_option autoImplicit false

open Filter
open scoped BigOperators Topology

namespace D5.S3.Analytic.Oscillation.SparseOrdinateMass

noncomputable section

/-- Sum a weight over all indices whose real ordinate is at most the cutoff. -/
def cutoffSum {ι : Type*} (γ : ι → ℝ)
    (finite_le : ∀ T : ℝ, {j | γ j ≤ T}.Finite) (w : ι → ℝ) (T : ℝ) : ℝ :=
  ∑ j ∈ (finite_le T).toFinset, w j

private theorem dyadic_log_sq_bound {W : ℝ → ℝ} (hmono : Monotone W)
    {A c : ℝ} (hA : 2 ≤ A) (hc : 0 ≤ c)
    (hstep : ∀ T : ℝ, A < T → W T ≤ W (T / 2) + c * Real.log 2 * Real.log T) :
    ∀ T : ℝ, W T ≤ W A + c * Real.log T ^ 2 := by
  have hApos : 0 < A := by linarith
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hind (n : ℕ) (T : ℝ) (hT : T ≤ (2 : ℝ) ^ n * A) :
      W T ≤ W A + c * Real.log T ^ 2 := by
    induction n generalizing T with
    | zero =>
      have hTA : T ≤ A := by simpa using hT
      exact (hmono hTA).trans (le_add_of_nonneg_right (mul_nonneg hc (sq_nonneg _)))
    | succ n ih =>
      by_cases hTA : T ≤ A
      · exact (hmono hTA).trans (le_add_of_nonneg_right (mul_nonneg hc (sq_nonneg _)))
      · have hAT : A < T := lt_of_not_ge hTA
        have hTpos : 0 < T := hApos.trans hAT
        have hhalf : T / 2 ≤ (2 : ℝ) ^ n * A := by
          rw [pow_succ] at hT
          linarith
        have hloghalf : 0 ≤ Real.log (T / 2) :=
          Real.log_nonneg (by linarith)
        have hlog : Real.log T = Real.log (T / 2) + Real.log 2 := by
          rw [Real.log_div hTpos.ne' (by norm_num)]
          ring
        have hsq : Real.log (T / 2) ^ 2 + Real.log 2 * Real.log T ≤ Real.log T ^ 2 := by
          rw [hlog]
          nlinarith [mul_nonneg hloghalf hlog2]
        calc
          W T ≤ W (T / 2) + c * Real.log 2 * Real.log T := hstep T hAT
          _ ≤ W A + c * (Real.log (T / 2) ^ 2 + Real.log 2 * Real.log T) := by
            linarith [ih (T / 2) hhalf]
          _ ≤ W A + c * Real.log T ^ 2 :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq hc)
  intro T
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (T / A) (show (1 : ℝ) < 2 by norm_num)
  exact hind n T ((div_lt_iff₀ hApos).mp hn).le

/-- Sparse inclusive multiplicity counts force vanishing normalized mass for any
nonnegative weight bounded by multiplicity divided by ordinate at positive ordinates. -/
theorem cutoffMass_tendsto_zero {ι : Type*} (γ : ι → ℝ) (m w : ι → ℝ)
    (finite_le : ∀ T : ℝ, {j | γ j ≤ T}.Finite)
    (hm : ∀ j, 0 ≤ m j) (hw : ∀ j, 0 ≤ w j)
    (hw_le : ∀ j, 0 < γ j → w j ≤ m j / γ j)
    (hcount : Tendsto (fun T : ℝ => cutoffSum γ finite_le m T / (T * Real.log T))
      atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => cutoffSum γ finite_le w T / (Real.log T) ^ 2) atTop (𝓝 0) := by
  classical
  let W := cutoffSum γ finite_le w
  let B := cutoffSum γ finite_le m
  change Tendsto (fun T : ℝ => W T / Real.log T ^ 2) atTop (𝓝 0)
  change Tendsto (fun T : ℝ => B T / (T * Real.log T)) atTop (𝓝 0) at hcount
  have hsubset {s t : ℝ} (hst : s ≤ t) :
      (finite_le s).toFinset ⊆ (finite_le t).toFinset := fun j hj =>
    (finite_le t).mem_toFinset.mpr (((finite_le s).mem_toFinset.mp hj).trans hst)
  have hWnonneg (T : ℝ) : 0 ≤ W T := Finset.sum_nonneg fun j _ => hw j
  have hWmono : Monotone W := fun _ _ hst =>
    Finset.sum_le_sum_of_subset_of_nonneg (hsubset hst) fun j _ _ => hw j
  have hshell (T : ℝ) (hT : 0 < T) : W T ≤ W (T / 2) + B T / (T / 2) := by
    let s := (finite_le (T / 2)).toFinset
    let t := (finite_le T).toFinset
    have hst : s ⊆ t := hsubset (by linarith)
    have hwShell : ∀ j ∈ t \ s, w j ≤ m j / (T / 2) := by
      intro j hj
      have hlow : T / 2 < γ j := lt_of_not_ge fun hj' =>
        (Finset.mem_sdiff.mp hj).2 ((finite_le _).mem_toFinset.mpr hj')
      have hhalf : 0 < T / 2 := by positivity
      exact (hw_le j (hhalf.trans hlow)).trans
        (div_le_div_of_nonneg_left (hm j) hhalf hlow.le)
    have hsum : (∑ j ∈ t \ s, w j) + W (T / 2) = W T :=
      Finset.sum_sdiff hst
    calc
      W T = (∑ j ∈ t \ s, w j) + W (T / 2) := hsum.symm
      _ ≤ (∑ j ∈ t \ s, m j / (T / 2)) + W (T / 2) :=
        add_le_add (Finset.sum_le_sum hwShell) le_rfl
      _ ≤ B T / (T / 2) + W (T / 2) := by
        rw [← Finset.sum_div]
        exact add_le_add (div_le_div_of_nonneg_right
          (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun j _ _ => hm j)
          (by positivity)) le_rfl
      _ = _ := add_comm _ _
  apply tendsto_order.mpr
  refine ⟨fun a ha => Filter.Eventually.of_forall fun T =>
    ha.trans_le (div_nonneg (hWnonneg T) (sq_nonneg _)), ?_⟩
  intro ε hε
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let c := ε / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hδ : 0 < c * Real.log 2 / 2 := by positivity
  obtain ⟨U, hU⟩ := eventually_atTop.mp ((tendsto_order.mp hcount).2 _ hδ)
  let A := max U 2
  have hA : 2 ≤ A := le_max_right _ _
  have hstep (T : ℝ) (hAT : A < T) :
      W T ≤ W (T / 2) + c * Real.log 2 * Real.log T := by
    have hT : 0 < T := by linarith
    have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
    have hBT := (div_lt_iff₀ (mul_pos hT hlogT)).mp
      (hU T ((le_max_left U 2).trans hAT.le))
    have hdiv : B T / (T / 2) ≤ c * Real.log 2 * Real.log T :=
      (div_le_iff₀ (by positivity)).mpr (by linarith [hBT])
    exact (hshell T hT).trans (add_le_add le_rfl hdiv)
  have hbound := dyadic_log_sq_bound hWmono hA hc.le hstep
  have hInv := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hconstant : Tendsto (fun T : ℝ => W A / Real.log T ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
      div_eq_mul_inv, inv_pow] using (hInv.pow 2).const_mul (W A)
  filter_upwards [(tendsto_order.mp hconstant).2 _ hc, eventually_gt_atTop (1 : ℝ)]
    with T hsmall hT
  have hden : 0 < Real.log T ^ 2 := pow_pos (Real.log_pos hT) _
  calc
    W T / Real.log T ^ 2 ≤ (W A + c * Real.log T ^ 2) / Real.log T ^ 2 :=
      div_le_div_of_nonneg_right (hbound T) hden.le
    _ = W A / Real.log T ^ 2 + c := by
      rw [add_div, mul_div_cancel_right₀ _ hden.ne']
    _ < ε := by dsimp [c] at *; linarith

/-- The per-ordinate kernel is dominated by the reciprocal for positive ordinates. -/
private theorem harmonicWeight_le {x a : ℝ} (hx : 0 < x) (ha : 0 ≤ a) :
    a * x / (1 / 4 + x ^ 2) ≤ a / x := by
  apply (div_le_div_iff₀ (by positivity) hx).mpr
  nlinarith [mul_nonneg ha (show (0 : ℝ) ≤ 1 / 4 by norm_num)]

/-- For any locally finite positive spectrum, use the original natural multiplicity
in both the count and the harmonic mass. The inclusive cutoff is real. -/
theorem harmonicMass_tendsto_zero {ι : Type*} (γ : ι → ℝ) (m : ι → ℕ)
    (finite_le : ∀ T : ℝ, {j | γ j ≤ T}.Finite) (hγ : ∀ j, 0 < γ j)
    (hcount : Tendsto (fun T : ℝ => cutoffSum γ finite_le (fun j => (m j : ℝ)) T /
      (T * Real.log T)) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => cutoffSum γ finite_le
      (fun j => (m j : ℝ) * γ j / (1 / 4 + γ j ^ 2)) T / Real.log T ^ 2) atTop (𝓝 0) := by
  apply cutoffMass_tendsto_zero γ (fun j => (m j : ℝ)) _ finite_le
  · intro j
    exact Nat.cast_nonneg _
  · intro j
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hγ j).le) (by positivity)
  · intro j hj
    exact harmonicWeight_le hj (Nat.cast_nonneg _)
  · exact hcount

end

end D5.S3.Analytic.Oscillation.SparseOrdinateMass
