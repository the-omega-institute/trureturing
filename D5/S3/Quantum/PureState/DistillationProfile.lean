/- GID: D5/S3/Quantum/PureState/DistillationProfile
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/DistillationProfile
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Clipping at a common threshold optimizes the scalar phase-memory profile. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
The scalar memory-budget objective is the dual-ball description of the
distillation norm of Regula, Fang, Wang and Adesso (arXiv:1711.10512v3,
Theorem 2 and Supplemental Material, Eq. (S12)).
-/

namespace PhaseRecordDistillation

noncomputable section

variable {I : Type*} [Fintype I]

/-- Diagonal profiles allowed by the trace and operator budgets. -/
def Feasible (d : I → ℝ) (M : ℝ) : Prop :=
  (∀ i, 0 ≤ d i) ∧ (∀ i, d i ≤ 1) ∧ (∑ i, d i) ≤ M

/-- The amplitude sum whose square determines the relaxed success. -/
def profileValue (t d : I → ℝ) : ℝ := ∑ i, t i * Real.sqrt (d i)

/-- A sufficient certificate of optimality. Coordinates below the cap share one slope. -/
theorem profileValue_le_of_certificate (t d v r : I → ℝ) (c M : ℝ)
    (hd : Feasible d M) (hv : Feasible v M) (hm : ∑ i, d i = M)
    (hc : 0 ≤ c) (hr : ∀ i, c ≤ r i)
    (ht : ∀ i, t i = Real.sqrt (d i) * r i)
    (hclip : ∀ i, d i < 1 → r i = c) :
    profileValue t v ≤ profileValue t d := by
  have hcap i : (r i - c) * v i ≤ (r i - c) * d i := by
    rcases (hd.2.1 i).lt_or_eq with h | h
    · simp [hclip i h]
    · rw [h]
      exact mul_le_mul_of_nonneg_left (hv.2.1 i) (sub_nonneg.mpr (hr i))
  have hweighted : (∑ i, r i * v i) ≤ ∑ i, r i * d i := by
    calc
      _ = c * (∑ i, v i) + ∑ i, (r i - c) * v i := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ c * (∑ i, d i) + ∑ i, (r i - c) * d i :=
        add_le_add (mul_le_mul_of_nonneg_left (hm ▸ hv.2.2) hc)
          (Finset.sum_le_sum fun i _ => hcap i)
      _ = _ := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
  have hself : profileValue t d = ∑ i, r i * d i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ht i, mul_right_comm, Real.mul_self_sqrt (hd.1 i), mul_comm]
  unfold profileValue
  change (∑ i, t i * Real.sqrt (v i)) ≤ profileValue t d
  calc
    _ ≤ ∑ i, r i * (d i + v i) / 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := sq_nonneg (Real.sqrt (d i) - Real.sqrt (v i))
      have hs : 2 * (Real.sqrt (d i) * Real.sqrt (v i)) ≤ d i + v i := by
        nlinarith [Real.sq_sqrt (hd.1 i), Real.sq_sqrt (hv.1 i)]
      rw [ht i]
      have hm := mul_le_mul_of_nonneg_left hs (hc.trans (hr i))
      linarith only [mul_assoc (Real.sqrt (d i)) (r i) (Real.sqrt (v i)), hm]
    _ = ((∑ i, r i * d i) + ∑ i, r i * v i) / 2 := by
      simp only [mul_add, add_div, Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ profileValue t d := by rw [hself]; linarith

/-- The capped square profile at a positive threshold. -/
def clippedProfile (t : I → ℝ) (c : ℝ) (i : I) : ℝ :=
  min 1 ((t i / c) ^ 2)

omit [Fintype I] in
theorem clippedProfile_certificate (t : I → ℝ) (ht : ∀ i, 0 ≤ t i)
    (c : ℝ) (hc : 0 < c) :
    (∀ i, 0 ≤ clippedProfile t c i) ∧ (∀ i, clippedProfile t c i ≤ 1) ∧
    (∀ i, t i = Real.sqrt (clippedProfile t c i) * max (t i) c) ∧
    (∀ i, clippedProfile t c i < 1 → max (t i) c = c) := by
  refine ⟨fun i => le_min zero_le_one (sq_nonneg _), fun i => min_le_left _ _, ?_, ?_⟩
  · intro i
    by_cases h : t i ≤ c
    · have hdiv : t i / c ≤ 1 := (div_le_one hc).mpr h
      rw [clippedProfile, min_eq_right (by nlinarith [div_nonneg (ht i) hc.le]),
        Real.sqrt_sq (div_nonneg (ht i) hc.le), max_eq_right h, div_mul_cancel₀ _ hc.ne']
    · have hdiv : 1 ≤ t i / c := (le_div_iff₀ hc).mpr (by linarith)
      rw [clippedProfile, min_eq_left (by nlinarith), Real.sqrt_one, max_eq_left (by linarith), one_mul]
  · intro i hi
    by_contra! h
    have hlt : c < t i := lt_of_not_ge fun hle => h (max_eq_right hle)
    have hdiv : 1 ≤ t i / c := (le_div_iff₀ hc).mpr (by linarith)
    have he : clippedProfile t c i = 1 := min_eq_left (by nlinarith)
    linarith

/-- The clipping threshold exists up to and including the positive-support size. -/
theorem exists_clippedProfile_sum (t : I → ℝ) (ht : ∀ i, 0 ≤ t i)
    (M : ℝ) (hM : 0 < M)
    (hsupport : M ≤ ∑ i, (if 0 < t i then (1 : ℝ) else 0)) :
    ∃ c : ℝ, 0 < c ∧ ∑ i, clippedProfile t c i = M := by
  let S := 1 + ∑ i, (t i)⁻¹
  have hS : 0 ≤ S := add_nonneg zero_le_one
    (Finset.sum_nonneg fun i _ => inv_nonneg.mpr (ht i))
  let f (s : ℝ) := ∑ i, min 1 ((t i * s) ^ 2)
  have hf : Continuous f := by
    apply continuous_finsetSum
    intro i _
    exact continuous_const.min ((continuous_const.mul continuous_id).pow 2)
  have hf0 : f 0 = 0 := by simp [f]
  have hfS : f S = ∑ i, (if 0 < t i then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · have hle : (t i)⁻¹ ≤ ∑ j, (t j)⁻¹ :=
        Finset.single_le_sum (fun j _ => inv_nonneg.mpr (ht j)) (Finset.mem_univ i)
      have hprod := mul_le_mul_of_nonneg_left (show (t i)⁻¹ ≤ S by dsimp [S]; linarith) hi.le
      rw [mul_inv_cancel₀ hi.ne'] at hprod
      exact min_eq_left (by nlinarith)
    · have hz : t i = 0 := le_antisymm (not_lt.mp hi) (ht i)
      simp [hz]
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hS hf.continuousOn
    (show M ∈ Set.Icc (f 0) (f S) by rw [hf0, hfS]; exact ⟨hM.le, hsupport⟩)
  have hs' : 0 < s := by
    refine lt_of_le_of_ne hs.1 ?_
    intro he
    rw [← he, hf0] at hfs
    linarith
  refine ⟨s⁻¹, inv_pos.mpr hs', ?_⟩
  simpa [clippedProfile, div_eq_mul_inv] using hfs

end

end PhaseRecordDistillation
