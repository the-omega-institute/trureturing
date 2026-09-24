/- GID: D5/S3/Combinatorics/OddParityExtension
   generality: G
   mirror-B: D5/B/S3/Combinatorics/OddParityExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every assignment off one coordinate has a unique odd-parity completion. -/

import D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.OddParityExtension

open scoped BigOperators
open D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments

/-- Two binary words agree away from the designated coordinate. -/
def agreesOff {L : ℕ} (i : Fin L) (x y : Fin L → Fin 2) : Prop :=
  ∀ j, j ≠ i → x j = y j

/--
For any designated coordinate, every assignment on all other coordinates has exactly
one completion in the odd parity fibre. This is the finite parity bridge used by the
cyclic law in the independent-source lower-bound argument.
-/
theorem odd_parity_unique_extension {L : ℕ} (_hL : 0 < L) (i : Fin L)
    (y : Fin L → Fin 2) :
    ∃! x : Fin L → Fin 2, agreesOff i x y ∧ x ∈ parityFiber L (-1) := by
  classical
  let rest : ℤ := (Finset.univ.erase i).prod (fun j => paritySign (y j))
  have hrest : rest = -1 ∨ rest = 1 := by
    dsimp [rest]
    induction (Finset.univ.erase i) using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha]
        rcases ih with h | h
        · have hya : y a = 0 ∨ y a = 1 := by omega
          rcases hya with hya | hya
          · have hpa : paritySign (y a) = -1 := by simp [paritySign, hya]
            rw [hpa, h]
            simp
          · have hpa : paritySign (y a) = 1 := by simp [paritySign, hya]
            rw [hpa, h]
            simp
        · have hya : y a = 0 ∨ y a = 1 := by omega
          rcases hya with hya | hya
          · have hpa : paritySign (y a) = -1 := by simp [paritySign, hya]
            rw [hpa, h]
            simp
          · have hpa : paritySign (y a) = 1 := by simp [paritySign, hya]
            rw [hpa, h]
            simp
  have hprod (b : Fin 2) :
      (∏ j : Fin L, paritySign ((Function.update y i b) j)) =
        paritySign b * rest := by
    have hfun :
        (fun j : Fin L => paritySign ((Function.update y i b) j)) =
          Function.update (fun j : Fin L => paritySign (y j)) i (paritySign b) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ i)]
    rw [Finset.sdiff_singleton_eq_erase]
  have hagree (b : Fin 2) : agreesOff i (Function.update y i b) y := by
    intro j hji
    simp [hji]
  have hodd0 : (Function.update y i 0) ∈ parityFiber L (-1) ↔ rest = 1 := by
    simp only [parityFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hprod]
    simp [paritySign, rest]
  have hodd1 : (Function.update y i 1) ∈ parityFiber L (-1) ↔ rest = -1 := by
    simp only [parityFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hprod]
    simp [paritySign, rest]
  rcases hrest with hrest | hrest
  · refine ⟨Function.update y i 1, ⟨hagree 1, hodd1.mpr hrest⟩, ?_⟩
    intro z hz
    have hz_update : z = Function.update y i (z i) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · exact (hz.1 j hji).trans (by simp [hji])
    have hzi : z i = 0 ∨ z i = 1 := by omega
    rcases hzi with hzi | hzi
    · exfalso
      have hz_mem : z ∈ parityFiber L (-1) := hz.2
      rw [hz_update, hzi] at hz_mem
      have hzero := hodd0.mp hz_mem
      omega
    · calc
        z = Function.update y i (z i) := hz_update
        _ = Function.update y i 1 := by rw [hzi]
  · refine ⟨Function.update y i 0, ⟨hagree 0, hodd0.mpr hrest⟩, ?_⟩
    intro z hz
    have hz_update : z = Function.update y i (z i) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · exact (hz.1 j hji).trans (by simp [hji])
    have hzi : z i = 0 ∨ z i = 1 := by omega
    rcases hzi with hzi | hzi
    · calc
        z = Function.update y i (z i) := hz_update
        _ = Function.update y i 0 := by rw [hzi]
    · exfalso
      have hz_mem : z ∈ parityFiber L (-1) := hz.2
      rw [hz_update, hzi] at hz_mem
      have hone := hodd1.mp hz_mem
      omega

#print axioms odd_parity_unique_extension

end D5.S3.Combinatorics.OddParityExtension
