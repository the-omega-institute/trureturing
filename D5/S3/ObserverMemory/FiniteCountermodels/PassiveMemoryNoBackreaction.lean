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
can retain ordering information in its off-diagonal entry. This module isolates
the exact finite algebraic boundary of that construction.

For a common memory update `F`, local scalar readouts `Lp`, `Lq`, and memory
injections `(L - 1) * v`, reversing two observer steps creates an explicit
nilpotent off-diagonal defect. At the same time, changing an arbitrary memory
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
* Pinned Mathlib supplies `Matrix.trace_fin_two_of`, `Matrix.det_fin_two`, and
  `Matrix.charpoly_fin_two`; no packaged passive-memory theorem was found.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix

namespace D5.S3.ObserverMemory.FiniteCountermodels.PassiveMemoryNoBackreaction

abbrev MemoryMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- The passive two-channel memory lift with memory update `F`, injection `B`,
and scalar readout `L`. -/
def passiveMemoryMatrix (F B L : ℂ) : MemoryMatrix :=
  !![F, B; 0, L]

/-- The local prime-memory lift whose injection is `(L - 1) * v`. -/
def primeMemoryMatrix (F v L : ℂ) : MemoryMatrix :=
  passiveMemoryMatrix F ((L - 1) * v) L

/-- The adjacent-swap defect of two local prime-memory lifts. -/
def memoryHolonomy (F v Lp Lq : ℂ) : MemoryMatrix :=
  primeMemoryMatrix F v Lp * primeMemoryMatrix F v Lq -
    primeMemoryMatrix F v Lq * primeMemoryMatrix F v Lp

/-- Reversing two passive memory steps changes only the off-diagonal memory
entry. -/
theorem memory_holonomy_formula (F v Lp Lq : ℂ) :
    memoryHolonomy F v Lp Lq =
      !![0, (Lq - Lp) * (F - 1) * v; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [memoryHolonomy, primeMemoryMatrix, passiveMemoryMatrix] <;> ring

#print axioms memory_holonomy_formula

/-- The passive adjacent-swap defect has zero trace. -/
theorem memory_holonomy_trace_zero (F v Lp Lq : ℂ) :
    Matrix.trace (memoryHolonomy F v Lp Lq) = 0 := by
  rw [memory_holonomy_formula, Matrix.trace_fin_two_of]
  norm_num

#print axioms memory_holonomy_trace_zero

/-- The passive adjacent-swap defect has zero determinant. -/
theorem memory_holonomy_det_zero (F v Lp Lq : ℂ) :
    Matrix.det (memoryHolonomy F v Lp Lq) = 0 := by
  rw [memory_holonomy_formula, Matrix.det_fin_two]
  simp

#print axioms memory_holonomy_det_zero

/-- Changing only the passive memory injection leaves the trace unchanged. -/
theorem passive_memory_trace_invariant (F L B1 B2 : ℂ) :
    Matrix.trace (passiveMemoryMatrix F B1 L) =
      Matrix.trace (passiveMemoryMatrix F B2 L) := by
  simp [passiveMemoryMatrix, Matrix.trace_fin_two_of]

#print axioms passive_memory_trace_invariant

/-- Changing only the passive memory injection leaves the determinant unchanged. -/
theorem passive_memory_det_invariant (F L B1 B2 : ℂ) :
    Matrix.det (passiveMemoryMatrix F B1 L) =
      Matrix.det (passiveMemoryMatrix F B2 L) := by
  simp [passiveMemoryMatrix, Matrix.det_fin_two]

#print axioms passive_memory_det_invariant

/-- Changing only the passive memory injection leaves the characteristic
polynomial unchanged. Hence the passive memory channel cannot move scalar
spectral roots. -/
theorem passive_memory_charpoly_invariant (F L B1 B2 : ℂ) :
    (passiveMemoryMatrix F B1 L).charpoly =
      (passiveMemoryMatrix F B2 L).charpoly := by
  simp [Matrix.charpoly_fin_two, passiveMemoryMatrix,
    Matrix.trace, Matrix.det_fin_two]

#print axioms passive_memory_charpoly_invariant

/-- A concrete pair of passive memory matrices does not commute, so the
order-memory channel is genuinely nontrivial. -/
theorem passive_memory_order_witness :
    passiveMemoryMatrix 2 1 2 * passiveMemoryMatrix 2 2 3 ≠
      passiveMemoryMatrix 2 2 3 * passiveMemoryMatrix 2 1 2 := by
  intro h
  have h01 := congrArg (fun M : MemoryMatrix => M 0 1) h
  norm_num [passiveMemoryMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h01

#print axioms passive_memory_order_witness

end D5.S3.ObserverMemory.FiniteCountermodels.PassiveMemoryNoBackreaction
