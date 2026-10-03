/- GID: D5/S3/Fourier/CharacterSelection/SignedIncidenceTotalUnimodularity
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/SignedIncidenceTotalUnimodularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer endpoint boundaries are totally unimodular for arbitrary parallel directed edges and loops. -/

import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Mathlib.Tactic.Push

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity

open Matrix

def signedIncidence {V E : Type*} [DecidableEq V] (tail head : E → V) : Matrix V E ℤ :=
  fun vertex edge => (if vertex = head edge then 1 else 0) - (if vertex = tail edge then 1 else 0)

theorem signed_incidence_is_totally_unimodular
    {V E : Type*} [DecidableEq V] (tail head : E → V) :
    (signedIncidence tail head).IsTotallyUnimodular := by
  classical
  intro k f g hf hg
  induction k with
  | zero => use 1; simp
  | succ k ih =>
    let B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
      (signedIncidence tail head).submatrix f g
    by_cases hbad : ∃ j : Fin (k + 1),
        head (g j) = tail (g j) ∨
          (∀ i : Fin (k + 1), f i ≠ head (g j)) ∨
            (∀ i : Fin (k + 1), f i ≠ tail (g j))
    · obtain ⟨j, hloop | hhead | htail⟩ := hbad
      · rw [det_succ_column B j]
        refine ⟨0, ?_⟩
        simp [B, signedIncidence, hloop]
      · by_cases htail' : ∃ i : Fin (k + 1), f i = tail (g j)
        · obtain ⟨i, hi⟩ := htail'
          have hne : tail (g j) ≠ head (g j) := by
            intro h
            exact hhead i (hi.trans h)
          have hentry : B i j = -1 := by
            simp [B, signedIncidence, hne, hi]
          have hother (i' : Fin (k + 1)) (hi' : i' ≠ i) : B i' j = 0 := by
            have htail'' : f i' ≠ tail (g j) := by
              intro h
              exact hi' (hf (h.trans hi.symm))
            simp [B, signedIncidence, hhead i', htail'']
          have hind := ih (f := f ∘ i.succAbove) (g := g ∘ j.succAbove)
            (hf.comp i.succAbove_right_injective) (hg.comp j.succAbove_right_injective)
          have hdet : (B.submatrix i.succAbove j.succAbove).det ∈ Set.range SignType.cast := by
            simpa [B, Matrix.submatrix_submatrix, Function.comp_def] using hind
          rw [det_succ_column B j, Finset.sum_eq_single i]
          · rw [hentry]
            rcases hdet with ⟨s, hs⟩
            rw [← hs]
            change _ ∈ MonoidHom.mrange SignType.castHom.toMonoidHom
            refine mul_mem (mul_mem ?_ ?_) (Set.mem_range_self s)
            · apply pow_mem
              exact Set.mem_range_self (-1 : SignType)
            · exact Set.mem_range_self SignType.neg
          · intro i' _ hi'
            simp [hother i' hi']
          · simp
        · rw [det_succ_column B j]
          refine ⟨0, ?_⟩
          have htail'' : ∀ i : Fin (k + 1), f i ≠ tail (g j) := by
            simpa only [not_exists] using htail'
          simp [B, signedIncidence, hhead, htail'']
      · by_cases hhead' : ∃ i : Fin (k + 1), f i = head (g j)
        · obtain ⟨i, hi⟩ := hhead'
          have hne : head (g j) ≠ tail (g j) := by
            intro h
            exact htail i (hi.trans h)
          have hentry : B i j = 1 := by
            simp [B, signedIncidence, hne, hi]
          have hother (i' : Fin (k + 1)) (hi' : i' ≠ i) : B i' j = 0 := by
            have hhead'' : f i' ≠ head (g j) := by
              intro h
              exact hi' (hf (h.trans hi.symm))
            simp [B, signedIncidence, hhead'', htail i']
          have hind := ih (f := f ∘ i.succAbove) (g := g ∘ j.succAbove)
            (hf.comp i.succAbove_right_injective) (hg.comp j.succAbove_right_injective)
          have hdet : (B.submatrix i.succAbove j.succAbove).det ∈ Set.range SignType.cast := by
            simpa [B, Matrix.submatrix_submatrix, Function.comp_def] using hind
          rw [det_succ_column B j, Finset.sum_eq_single i]
          · rw [hentry]
            rcases hdet with ⟨s, hs⟩
            rw [← hs]
            change _ ∈ MonoidHom.mrange SignType.castHom.toMonoidHom
            refine mul_mem (mul_mem ?_ ?_) (Set.mem_range_self s)
            · apply pow_mem
              exact Set.mem_range_self (-1 : SignType)
            · exact Set.mem_range_self SignType.pos
          · intro i' _ hi'
            simp [hother i' hi']
          · simp
        · rw [det_succ_column B j]
          refine ⟨0, ?_⟩
          have hhead'' : ∀ i : Fin (k + 1), f i ≠ head (g j) := by
            simpa only [not_exists] using hhead'
          simp [B, signedIncidence, hhead'', htail]
    · push Not at hbad
      have hnonlin : ¬ LinearIndependent ℤ (fun i => B i) := by
        rw [Fintype.not_linearIndependent_iff]
        refine ⟨fun _ => 1, ?_, 0, by simp⟩
        funext j
        have hhead' := (hbad j).2.1
        have htail' := (hbad j).2.2
        obtain ⟨ih, hih⟩ := hhead'
        obtain ⟨it, hit⟩ := htail'
        have hsum_head :
            (∑ i : Fin (k + 1), if f i = head (g j) then (1 : ℤ) else 0) = 1 := by
          rw [Finset.sum_eq_single ih]
          · simp [hih]
          · intro i _ hne
            rw [if_neg]
            intro h
            exact hne (hf (h.trans hih.symm))
          · simp
        have hsum_tail :
            (∑ i : Fin (k + 1), if f i = tail (g j) then (1 : ℤ) else 0) = 1 := by
          rw [Finset.sum_eq_single it]
          · simp [hit]
          · intro i _ hne
            rw [if_neg]
            intro h
            exact hne (hf (h.trans hit.symm))
          · simp
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, one_smul, Pi.zero_apply]
        simp only [B, Matrix.submatrix_apply, signedIncidence, Finset.sum_sub_distrib]
        rw [hsum_head, hsum_tail, sub_self]
      have hzero : B.det = 0 := det_eq_zero_of_not_linearIndependent_rows hnonlin
      have hmem : B.det ∈ Set.range SignType.cast := by
        rw [hzero]
        exact ⟨0, rfl⟩
      simpa [B] using hmem

#print axioms signed_incidence_is_totally_unimodular

end D5.S3.Fourier.CharacterSelection.SignedIncidenceTotalUnimodularity
