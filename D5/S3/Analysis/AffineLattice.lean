/- GID: D5/S3/Analysis/AffineLattice
   generality: G
   mirror-B: none(waiver:covered-by-strong-cpaxion-theta-vacuum4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite set of consecutive representatives of an affine lattice in a half-open interval. -/

import OmegaBuild.Commands
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Omega original.

A finite set of consecutive representatives of an affine lattice in a half-open interval.
-/

compile_only_with_mathlib

set_option autoImplicit false

open Set

namespace OmegaMath.AffineLattice

/-- Representative with integer index starting at the first lattice point at or above the left endpoint. -/
noncomputable def representative (offset step left : ℝ) {n : ℕ} (k : Fin n) : ℝ :=
  offset + step * ((⌈(left - offset) / step⌉ : ℤ) + (k : ℕ) : ℤ)

/-- The representatives enumerate exactly the lattice points of an interval of length `n * step`. -/
theorem representatives_Ico (offset : ℝ) {step : ℝ} (hstep : 0 < step) (left : ℝ) (n : ℕ) :
    Function.Injective (representative offset step left : Fin n → ℝ) ∧
      Set.range (representative offset step left : Fin n → ℝ) =
        Ico left (left + n * step) ∩ Set.range (fun k : ℤ => offset + step * k) := by
  let j : ℤ := ⌈(left - offset) / step⌉
  have hjlo : left ≤ offset + step * j := by
    have h := (div_le_iff₀ hstep).mp (Int.le_ceil ((left - offset) / step))
    linarith
  have hjhi : offset + step * j < left + step := by
    have h := (lt_div_iff₀ hstep).mp (Int.lt_ceil.mp (show j - 1 < j by omega))
    push_cast at h
    linarith
  constructor
  · intro k l h
    change offset + step * ((j + (k : ℕ) : ℤ) : ℝ) =
      offset + step * ((j + (l : ℕ) : ℤ) : ℝ) at h
    simp only [add_right_inj, mul_right_inj' hstep.ne', Int.cast_inj] at h
    exact Fin.ext (by omega)
  · ext x
    constructor
    · rintro ⟨k, rfl⟩
      change (offset + step * ((j + (k : ℕ) : ℤ) : ℝ) ∈ Ico left (left + n * step)) ∧ _
      refine ⟨⟨?_, ?_⟩, ⟨j + (k : ℕ), rfl⟩⟩
      · push_cast
        nlinarith [mul_nonneg hstep.le (show 0 ≤ ((k : ℕ) : ℝ) by positivity)]
      · have hk : ((k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast k.isLt
        push_cast
        nlinarith [mul_nonneg hstep.le (sub_nonneg.mpr hk)]
    · rintro ⟨⟨hlo, hhi⟩, k, rfl⟩
      have hklo : j ≤ k := by
        apply Int.ceil_le.mpr
        exact (div_le_iff₀ hstep).mpr (by linarith)
      have hkhi : k < j + n := by
        by_contra! h
        have h' : ((j : ℝ) + n) ≤ k := by exact_mod_cast h
        have hp := mul_le_mul_of_nonneg_left h' hstep.le
        linarith
      refine ⟨⟨(k - j).toNat, by omega⟩, ?_⟩
      have he : j + ((k - j).toNat : ℤ) = k := by omega
      change offset + step * ((j + ((k - j).toNat : ℤ) : ℤ) : ℝ) = _
      rw [he]

end OmegaMath.AffineLattice
