/- GID: D5/S3/Zeros/Symmetry/ZeroOrbitCardinality
   generality: I
   mirror-B: D5/B/S3/Zeros/Symmetry/ZeroOrbitCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Count the four-point zero orbit away from the critical line. -/

import D5.S3.Zeros.Symmetry.ZeroSymmetryAction

namespace D5.S3.Zeros.Symmetry.ZeroOrbitCardinality

open D5.S3.Weil.Convention
open D5.S3.Weil.ZeroSum
open D5.S3.Zeros.Symmetry.ZeroSymmetryAction

/-- An enumerated nonreal zero off the critical line has a four-point symmetry orbit. -/
theorem zero_orbit_card_four_of_off_line (Z : ZeroData) (n : ℕ)
    (hC : Z.conjugation n ≠ n) (hOff : (Z.zero n).re ≠ criticalAbscissa) :
    ({n, Z.reflection n, Z.conjugation n,
      Z.conjugation (Z.reflection n)} : Finset ℕ).card = 4 := by
  have hR : Z.reflection n ≠ n := by
    intro h
    have hzero : 1 - Z.zero n = Z.zero n := by
      calc
        1 - Z.zero n = Z.zero (Z.reflection n) := (Z.zero_reflection n).symm
        _ = Z.zero n := congrArg Z.zero h
    have hre : 1 - (Z.zero n).re = (Z.zero n).re := by
      simpa using congrArg Complex.re hzero
    apply hOff
    rw [criticalAbscissa]
    linarith
  have hM : Z.conjugation (Z.reflection n) ≠ n := by
    intro h
    exact hOff ((mirror_index_fixed_iff_critical Z n).1 h)
  have hRC : Z.reflection n ≠ Z.conjugation n := by
    intro h
    apply hM
    simpa using congrArg Z.conjugation h
  have hRM : Z.reflection n ≠ Z.conjugation (Z.reflection n) := by
    intro h
    apply hC
    have hnC : n = Z.conjugation n := by
      calc
        n = Z.reflection (Z.reflection n) := (Z.reflection_reflection n).symm
        _ = Z.reflection (Z.conjugation (Z.reflection n)) := congrArg Z.reflection h
        _ = Z.conjugation (Z.reflection (Z.reflection n)) :=
          zero_symmetries_commute Z (Z.reflection n)
        _ = Z.conjugation n := by rw [Z.reflection_reflection]
    exact hnC.symm
  have hCM : Z.conjugation n ≠ Z.conjugation (Z.reflection n) := by
    intro h
    apply hR
    have hnR : n = Z.reflection n := by
      simpa using congrArg Z.conjugation h
    exact hnR.symm
  have hnMem :
      n ∉ ({Z.reflection n, Z.conjugation n,
        Z.conjugation (Z.reflection n)} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hR, Ne.symm hC, Ne.symm hM⟩
  have hRMem :
      Z.reflection n ∉
        ({Z.conjugation n, Z.conjugation (Z.reflection n)} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hRC, hRM⟩
  have hCMem :
      Z.conjugation n ∉ ({Z.conjugation (Z.reflection n)} : Finset ℕ) := by
    simpa only [Finset.mem_singleton] using hCM
  rw [Finset.card_insert_of_notMem hnMem, Finset.card_insert_of_notMem hRMem,
    Finset.card_insert_of_notMem hCMem]
  rfl

example (Z : ZeroData) (n : ℕ) (hC : Z.conjugation n ≠ n)
    (hOff : (Z.zero n).re ≠ criticalAbscissa) :
    ({n, Z.reflection n, Z.conjugation n,
      Z.conjugation (Z.reflection n)} : Finset ℕ).card = 4 :=
  zero_orbit_card_four_of_off_line Z n hC hOff

end D5.S3.Zeros.Symmetry.ZeroOrbitCardinality
