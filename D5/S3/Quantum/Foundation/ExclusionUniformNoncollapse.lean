/- GID: D5/S3/Quantum/Foundation/ExclusionUniformNoncollapse
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ExclusionUniformNoncollapse
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Closed pure loci prevent positive-rank collapse of whole exclusion ball charts. -/

import D5.S3.Quantum.Foundation.ExclusionWidthCompactness
import D5.S3.Quantum.Foundation.OriginalFacePolarity
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D5.S3.Quantum.Foundation.ExclusionUniformNoncollapse

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open ExclusionWidthCompactness ContinuousFrameSum

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A nonzero kernel direction pads any point of a closed ball to its sphere
without changing its linear image. -/
private theorem kernel_padding (A : E →L[ℝ] V) {k : E} (hk : k ≠ 0)
    (hAk : A k = 0) {x : E} (hx : ‖x‖ ≤ 1) :
    ∃ y : E, ‖y‖ = 1 ∧ A y = A x := by
  let t : ℝ := (‖x‖ + 1) / ‖k‖
  have hkpos : 0 < ‖k‖ := norm_pos_iff.mpr hk
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htk : ‖t • k‖ = ‖x‖ + 1 := by
    rw [norm_smul, Real.norm_of_nonneg ht]
    exact div_mul_cancel₀ _ hkpos.ne'
  have hlarge : 1 ≤ ‖x + t • k‖ := by
    have h := norm_sub_le (x + t • k) x
    rw [add_sub_cancel_left, htk] at h
    linarith
  have hc : Continuous (fun s : ℝ => ‖x + s • k‖) := by fun_prop
  obtain ⟨s, _, hs⟩ := intermediate_value_Icc ht hc.continuousOn
    (show (1 : ℝ) ∈ Icc ‖x + (0 : ℝ) • k‖ ‖x + t • k‖ by simpa using And.intro hx hlarge)
  exact ⟨x + s • k, hs, by simp [hAk]⟩

/-- If an affine sphere lies entirely in the extreme locus, a noninjective
linear part must vanish: a flattened sphere cannot bound a nontrivial disk. -/
private theorem sphere_extreme_injective_or_zero (K : Set V) (c : V)
    (A : E →L[ℝ] V)
    (hsphere : ∀ x : E, ‖x‖ = 1 → c + A x ∈ K.extremePoints ℝ) :
    Function.Injective A ∨ A = 0 := by
  classical
  by_cases hi : Function.Injective A
  · exact Or.inl hi
  · right
    obtain ⟨k, hAk, hk⟩ := (not_injective_iff_exists_ne_zero (f := A)).mp hi
    have hball (x : E) (hx : ‖x‖ ≤ 1) : c + A x ∈ K.extremePoints ℝ := by
      obtain ⟨y, hy, he⟩ := kernel_padding A hk hAk hx
      simpa [he] using hsphere y hy
    have hc : c ∈ K.extremePoints ℝ := by simpa using hball 0 (by simp)
    have hz (x : E) (hx : ‖x‖ ≤ 1) : A x = 0 := by
      have hmid : c ∈ openSegment ℝ (c + A x) (c + A (-x)) := by
        convert midpoint_mem_openSegment (𝕜 := ℝ) (c + A x) (c + A (-x)) using 1
        simp [midpoint_eq_smul_add, ← smul_add]
      have he := hc.2 (hball x hx).1 (hball (-x) (by simpa using hx)).1 hmid
      exact add_left_cancel (he.trans (add_zero c).symm)
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · have hn : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
      have he := hz (‖x‖⁻¹ • x) hn
      rw [map_smul, smul_eq_zero] at he
      exact he.resolve_left (inv_ne_zero (norm_ne_zero_iff.mpr hx))

end D5.S3.Quantum.Foundation.ExclusionUniformNoncollapse
