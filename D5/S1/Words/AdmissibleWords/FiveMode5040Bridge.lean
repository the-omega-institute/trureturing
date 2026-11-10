/- GID: D5/S1/Words/AdmissibleWords/FiveMode5040Bridge
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/FiveMode5040Bridge
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The central 5040 slice has five head modes and its uniform law has an exact Fisher quadratic form. -/

import D5.S1.Ledger.BoundedTimeSlice
import D5.S1.Words.AdmissibleWords.FiveModeFisherMetric

set_option autoImplicit false
noncomputable section

namespace D5.S1.Words.AdmissibleWords.FiveMode5040Bridge

open scoped BigOperators
open D5.S1.Ledger.BoundedTimeSlice
open D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates

/-- The law obtained by assigning equal mass to the five head modes. -/
def uniformLaw5040 : Fin 5 → ℝ := fun _ => (1 : ℝ) / 5

theorem uniformLaw5040_mem_openSimplex : uniformLaw5040 ∈ openSimplex := by
  constructor
  · intro s
    norm_num [uniformLaw5040]
  · rw [Fin.sum_univ_succ]
    norm_num [uniformLaw5040]

/-- At the central time, every bounded tail state has one head completion. -/
theorem central_5040_has_five_head_modes :
    timeSlice5040Count 4 = 12 ∧
      ∀ b : TailBox tailCapacities5040,
        ∃! h : Fin 5, h.val + tailSum b = 4 ∧ h.val = 4 - tailSum b := by
  exact ⟨(time_slice_5040_unique_maximum 4).2.mpr rfl,
    time_slice_5040_tail_extension⟩

/-- The uniform five-mode Fisher form is exactly five times Euclidean pairing. -/
theorem fisher_uniformLaw5040 (u v : Fin 5 → ℝ) :
    fisher uniformLaw5040 u v = 5 * ∑ s, u s * v s := by
  unfold fisher uniformLaw5040
  norm_num [div_eq_mul_inv]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs
  ring

theorem fisher_uniformLaw5040_pos (u : Fin 5 → ℝ) (hu : u ≠ 0) :
    0 < fisher uniformLaw5040 u u := by
  rw [fisher_uniformLaw5040]
  obtain ⟨s, hs⟩ : ∃ s, u s ≠ 0 := by
    by_contra h
    apply hu
    funext s
    by_contra hs0
    exact h ⟨s, hs0⟩
  have hsum : 0 < ∑ s, u s * u s := by
    exact Finset.sum_pos' (fun s _ => mul_self_nonneg _) ⟨s, Finset.mem_univ _,
      mul_self_pos.mpr hs⟩
  nlinarith

theorem central_5040_five_mode_fisher_data :
    timeSlice5040Count 4 = 12 ∧
      uniformLaw5040 ∈ openSimplex ∧
      (∀ u v, fisher uniformLaw5040 u v = 5 * ∑ s, u s * v s) ∧
      (∀ u, u ≠ 0 → 0 < fisher uniformLaw5040 u u) := by
  exact ⟨(central_5040_has_five_head_modes).1, uniformLaw5040_mem_openSimplex,
    fisher_uniformLaw5040, fisher_uniformLaw5040_pos⟩

#print axioms central_5040_five_mode_fisher_data

end D5.S1.Words.AdmissibleWords.FiveMode5040Bridge
