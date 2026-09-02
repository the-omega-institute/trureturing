/- GID: D5/S3/Zeros/Symmetry/MultiscaleFingerprintAppend
   generality: I
   mirror-B: D5/B/S3/Zeros/Symmetry/MultiscaleFingerprintAppend
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Appending a damping scale preserves the old fingerprint and exposes a new defect. -/

import D5.S3.Zeros.Symmetry.CriticalDampingFlatness
import Mathlib.Analysis.SpecialFunctions.Arcosh

namespace D5.S3.Zeros.Symmetry.MultiscaleFingerprintAppend

open D5.S3.Zeros.Symmetry.CriticalDampingFlatness

/-- The finite history of the frozen critical damping defect at prescribed scales. -/
noncomputable def multiscaleDampingFingerprint {Zero : Type*} [Fintype Zero]
    (realPart : Zero → ℝ) {n : ℕ} (scale : Fin n → ℝ) : Fin n → ℝ :=
  fun k ↦ criticalDampingDefect realPart (scale k)

/-- Appending one prescribed scale preserves every old fingerprint coordinate. If two finite
carriers have unequal defects at the appended scale, their extended fingerprints differ. -/
theorem multiscale_fingerprint_append {Zero Zero' : Type*} [Fintype Zero] [Fintype Zero']
    (realPart : Zero → ℝ) (realPart' : Zero' → ℝ) {n : ℕ}
    (scale : Fin n → ℝ) (tauNew : ℝ) :
    (∀ k : Fin n,
      multiscaleDampingFingerprint realPart (Fin.snoc scale tauNew) (Fin.castSucc k) =
        multiscaleDampingFingerprint realPart scale k) ∧
    (criticalDampingDefect realPart tauNew ≠ criticalDampingDefect realPart' tauNew →
      multiscaleDampingFingerprint realPart (Fin.snoc scale tauNew) ≠
        multiscaleDampingFingerprint realPart' (Fin.snoc scale tauNew)) := by
  constructor
  · intro k
    simp [multiscaleDampingFingerprint]
  · intro newDefectNe extendedEq
    apply newDefectNe
    have lastCoordinate := congrFun extendedEq (Fin.last n)
    simpa [multiscaleDampingFingerprint] using lastCoordinate

/-- The preregistered collision pair agrees at scale one and separates at scale two by a
strictly positive amount. Its entries are centered offsets `+1, -1` and `+b, +b, -b, -b`. -/
theorem two_scale_collision_separation :
    let b := Real.arcosh ((Real.cosh 1 + 1) / 2)
    let collisionX : Fin 2 → ℝ := ![3 / 2, -1 / 2]
    let collisionY : Fin 4 → ℝ := ![1 / 2 + b, 1 / 2 + b, 1 / 2 - b, 1 / 2 - b]
    criticalDampingDefect collisionX 1 = criticalDampingDefect collisionY 1 ∧
      criticalDampingDefect collisionX 1 = 2 * (Real.cosh 1 - 1) ∧
      criticalDampingDefect collisionY 1 = 2 * (Real.cosh 1 - 1) ∧
      criticalDampingDefect collisionX 2 - criticalDampingDefect collisionY 2 =
        2 * (Real.cosh 1 - 1) ^ 2 ∧
      0 < 2 * (Real.cosh 1 - 1) ^ 2 ∧
      criticalDampingDefect collisionX 2 ≠ criticalDampingDefect collisionY 2 := by
  dsimp
  have argumentGeOne : 1 ≤ (Real.cosh 1 + 1) / 2 := by
    linarith [Real.one_le_cosh 1]
  have coshB :
      Real.cosh (Real.arcosh ((Real.cosh 1 + 1) / 2)) =
        (Real.cosh 1 + 1) / 2 :=
    Real.cosh_arcosh argumentGeOne
  have coshTwo (x : ℝ) : Real.cosh (2 * x) = 2 * Real.cosh x ^ 2 - 1 := by
    rw [Real.cosh_two_mul, Real.sinh_sq]
    ring
  have xAtOne :
      criticalDampingDefect ![(3 / 2 : ℝ), (-1 / 2 : ℝ)] 1 =
        2 * (Real.cosh 1 - 1) := by
    simp [criticalDampingDefect, Fin.sum_univ_succ]
    norm_num
    ring
  have yAtOne :
      criticalDampingDefect
          ![1 / 2 + Real.arcosh ((Real.cosh 1 + 1) / 2),
            1 / 2 + Real.arcosh ((Real.cosh 1 + 1) / 2),
            1 / 2 - Real.arcosh ((Real.cosh 1 + 1) / 2),
            1 / 2 - Real.arcosh ((Real.cosh 1 + 1) / 2)] 1 =
        2 * (Real.cosh 1 - 1) := by
    simp [criticalDampingDefect, Fin.sum_univ_succ, coshB]
    ring
  have scaleTwoDifference :
      criticalDampingDefect ![(3 / 2 : ℝ), (-1 / 2 : ℝ)] 2 -
          criticalDampingDefect
            ![1 / 2 + Real.arcosh ((Real.cosh 1 + 1) / 2),
              1 / 2 + Real.arcosh ((Real.cosh 1 + 1) / 2),
              1 / 2 - Real.arcosh ((Real.cosh 1 + 1) / 2),
              1 / 2 - Real.arcosh ((Real.cosh 1 + 1) / 2)] 2 =
        2 * (Real.cosh 1 - 1) ^ 2 := by
    simp [criticalDampingDefect, Fin.sum_univ_succ, Real.cosh_neg, coshTwo, coshB]
    norm_num
    ring
  have positiveDifference : 0 < 2 * (Real.cosh 1 - 1) ^ 2 := by
    have coshOneGtOne : 1 < Real.cosh 1 := Real.one_lt_cosh.mpr one_ne_zero
    positivity
  refine ⟨xAtOne.trans yAtOne.symm, xAtOne, yAtOne, scaleTwoDifference,
    positiveDifference, ?_⟩
  intro equalAtTwo
  have differenceZero := sub_eq_zero.mpr equalAtTwo
  rw [scaleTwoDifference] at differenceZero
  linarith

/-- A concrete finite carrier and scale family inhabit the theorem's quantified domain. -/
noncomputable example : (Fin 1 → ℝ) × (Fin 1 → ℝ) :=
  (fun _ ↦ 1 / 2, fun _ ↦ 1)

/-- The append theorem's defect-inequality premise is satisfiable. -/
example :
    criticalDampingDefect (fun _ : Fin 1 ↦ (1 / 2 : ℝ)) 1 ≠
      criticalDampingDefect (fun _ : Fin 1 ↦ (3 / 2 : ℝ)) 1 := by
  simp only [criticalDampingDefect, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  norm_num
  exact ne_of_lt (sub_pos.mpr (Real.one_lt_cosh.mpr one_ne_zero))

#print axioms multiscale_fingerprint_append
#print axioms two_scale_collision_separation

end D5.S3.Zeros.Symmetry.MultiscaleFingerprintAppend
