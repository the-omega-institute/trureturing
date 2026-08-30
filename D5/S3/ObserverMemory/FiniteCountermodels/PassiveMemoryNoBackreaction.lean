/- GID: D5/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FiniteCountermodels/PassiveMemoryNoBackreaction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Passive triangular memory stores order without changing scalar spectral invariants. -/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

/-!
# Passive memory has no scalar backreaction

The upper-triangular two-channel observer used by the golden-prime memory route
can retain ordering information in its off-diagonal entry.  This module isolates
the exact finite algebraic boundary of that construction.

For a common memory update `F`, local scalar readouts `Lp`, `Lq`, and memory
injections `(L - 1) * v`, reversing two observer steps creates an explicit
nilpotent off-diagonal defect.  At the same time, changing an arbitrary memory
injection leaves trace, determinant, and characteristic polynomial unchanged.
Thus the passive triangular lift can archive order, but it cannot move the
scalar spectral roots without an additional feedback channel.

Library-search audit trail (2026-08-30):

* Exact-name and body-shape searches on the current tree and `dev` found no
  theorem combining the adjacent-swap defect with determinant, trace, and
  characteristic-polynomial blindness to the memory injection.
* `IdentityJordanFullGroupTrace` proves trace blindness for one unipotent
  representation family, but does not cover arbitrary scalar readouts or the
  adjacent-swap memory defect.
* `CanonicalPathBranchNoncommutation` supplies a finite path/branch
  noncommutation boundary, but has no matrix spectral-invariant statement.
* Pinned Mathlib supplies `Matrix.trace_fin_two`, `Matrix.det_fin_two`, and
  `Matrix.charpoly_fin_two`; no packaged passive-memory theorem was found.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix

namespace D5.S3.ObserverMemory.FiniteCountermodels.PassiveMemoryNoBackreaction

abbrev MemoryMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- Reversing two passive memory steps can change only the off-diagonal memory
entry.  Arbitrary changes of that entry leave the scalar trace, determinant,
and characteristic polynomial unchanged. -/
theorem passive_memory_no_backreaction
    (F v Lp Lq B1 B2 : ℂ) :
    let U := fun B L : ℂ => (!![F, B; 0, L] : MemoryMatrix)
    let Up := U ((Lp - 1) * v) Lp
    let Uq := U ((Lq - 1) * v) Lq
    let holonomy := Up * Uq - Uq * Up
    holonomy = !![0, (Lq - Lp) * (F - 1) * v; 0, 0] ∧
      Matrix.trace holonomy = 0 ∧
      Matrix.det holonomy = 0 ∧
      Matrix.trace (U B1 Lp) = Matrix.trace (U B2 Lp) ∧
      Matrix.det (U B1 Lp) = Matrix.det (U B2 Lp) ∧
      (U B1 Lp).charpoly = (U B2 Lp).charpoly := by
  dsimp only
  have hHolonomy :
      (!![F, (Lp - 1) * v; 0, Lp] : MemoryMatrix) *
            !![F, (Lq - 1) * v; 0, Lq] -
          !![F, (Lq - 1) * v; 0, Lq] *
            !![F, (Lp - 1) * v; 0, Lp] =
        !![0, (Lq - Lp) * (F - 1) * v; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  refine ⟨hHolonomy, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hHolonomy, Matrix.trace_fin_two]
    norm_num
  · rw [hHolonomy, Matrix.det_fin_two]
    ring
  · simp [Matrix.trace_fin_two]
  · simp [Matrix.det_fin_two]
  · simp [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]

#print axioms passive_memory_no_backreaction

/-- A concrete pair of passive memory matrices has the same diagonal update
shape but does not commute, so the off-diagonal order channel is genuinely
nontrivial. -/
theorem passive_memory_order_witness :
    let Up : MemoryMatrix := !![(2 : ℂ), 1; 0, 2]
    let Uq : MemoryMatrix := !![(2 : ℂ), 2; 0, 3]
    Up * Uq ≠ Uq * Up := by
  dsimp only
  intro h
  have h01 := congrArg (fun M : MemoryMatrix => M 0 1) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h01

#print axioms passive_memory_order_witness

end D5.S3.ObserverMemory.FiniteCountermodels.PassiveMemoryNoBackreaction
