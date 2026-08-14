/- GID: D5/S3/Zeros/Symmetry/ZeroSymmetryAction
   generality: I
   mirror-B: D5/B/S3/Zeros/Symmetry/ZeroSymmetryAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Transport zero reflection and conjugation symmetries to their index actions. -/

import D5.S3.Weil.ReflectionLedger
import D5.S3.Weil.ZeroSum

namespace D5.S3.Zeros.Symmetry.ZeroSymmetryAction

open D5.S3.Weil.Convention
open D5.S3.Weil.ReflectionLedger
open D5.S3.Weil.ZeroSum
open scoped ComplexConjugate

/-- Reflection and conjugation commute on every supplied duplicate-free zero enumeration. -/
theorem zero_symmetries_commute (Z : ZeroData) :
    Function.Commute Z.reflection Z.conjugation := by
  intro n
  apply Z.zero_injective
  calc
    Z.zero (Z.reflection (Z.conjugation n)) =
        1 - conj (Z.zero n) := by
      rw [Z.zero_reflection, Z.zero_conjugation]
    _ = conj (1 - Z.zero n) := by simp
    _ = Z.zero (Z.conjugation (Z.reflection n)) := by
      rw [Z.zero_conjugation, Z.zero_reflection]

/-- A conjugate-reflection index is fixed exactly when its zero lies on the critical line. -/
theorem mirror_index_fixed_iff_critical (Z : ZeroData) (n : ℕ) :
    Z.conjugation (Z.reflection n) = n ↔
      (Z.zero n).re = criticalAbscissa := by
  constructor
  · intro h
    have hzero :
        Z.zero (Z.conjugation (Z.reflection n)) = Z.zero n :=
      congrArg Z.zero h
    apply mirror_fixed_re_eq
    calc
      mirror (Z.zero n) =
          Z.zero (Z.conjugation (Z.reflection n)) := by
        rw [Z.zero_conjugation, Z.zero_reflection]
        simp [mirror, reflection]
      _ = Z.zero n := hzero
  · intro hcritical
    have hfixed : mirror (Z.zero n) = Z.zero n := by
      apply Complex.ext
      · simp [mirror, reflection, hcritical, criticalAbscissa]
        norm_num
      · simp [mirror, reflection]
    apply Z.zero_injective
    rw [Z.zero_conjugation, Z.zero_reflection]
    simpa [mirror, reflection] using hfixed

/-- Every nontrivial zero is critical exactly when every mirror index is fixed. -/
theorem all_nontrivial_zeros_critical_iff_mirror_indices_fixed (Z : ZeroData) :
    (∀ {rho : ℂ}, IsNontrivialZero rho → rho.re = criticalAbscissa) ↔
      ∀ n, Z.conjugation (Z.reflection n) = n := by
  constructor
  · intro hcritical n
    exact (mirror_index_fixed_iff_critical Z n).2
      (hcritical (Z.zero_isNontrivial n))
  · intro hfixed rho hrho
    obtain ⟨n, rfl⟩ := Z.zero_exhaustive hrho
    exact (mirror_index_fixed_iff_critical Z n).1 (hfixed n)

example (Z : ZeroData) (n : ℕ)
    (hfixed : Z.conjugation (Z.reflection n) = n) :
    (Z.zero n).re = criticalAbscissa :=
  (mirror_index_fixed_iff_critical Z n).1 hfixed

end D5.S3.Zeros.Symmetry.ZeroSymmetryAction
