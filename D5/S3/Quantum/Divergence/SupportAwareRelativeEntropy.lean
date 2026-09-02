/- GID: D5/S3/Quantum/Divergence/SupportAwareRelativeEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/SupportAwareRelativeEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Quantum trace-log relative entropy is extended by top exactly outside support inclusion. -/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/- Library-search audit trail (2026-09-01):
   * Pinned Mathlib supplies the matrix continuous-functional-calculus logarithm.
     Its totalized logarithm satisfies `log 0 = 0`; it does not by itself encode
     the infinite branch of Umegaki relative entropy.
   * Repository search found only the frozen scalar trace-log expression in
     `QuantumRelativeEntropyDefectComposition`, with no support condition and
     real codomain.
   * This file first freezes the support preorder as reverse inclusion of matrix
     nullspaces, then extends the finite trace-log branch to `WithTop Real`.
     Positivity, DPI, and Petz equality remain separate future theorems. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy

open scoped CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel

/-- The vector nullspace of a finite square matrix, represented extensionally. -/
def matrixNullspace
    {n : Type*} [Fintype n] [DecidableEq n]
    (matrix : CStarMatrix n n ℂ) : Set (n -> ℂ) :=
  {vector | Matrix.mulVec matrix vector = 0}

/-- `rho` is supported inside `sigma` when every vector annihilated by `sigma`
is also annihilated by `rho`. For positive semidefinite matrices this is the
usual support-projection inclusion `supp rho <= supp sigma`. -/
def SupportContained
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : DensityState n) : Prop :=
  matrixNullspace sigma.1 ⊆ matrixNullspace rho.1

@[simp]
theorem supportContained_refl
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho : DensityState n) :
    SupportContained rho rho :=
  Set.Subset.rfl

theorem supportContained_trans
    {n : Type*} [Fintype n] [DecidableEq n]
    {rho sigma tau : DensityState n}
    (rhoSigma : SupportContained rho sigma)
    (sigmaTau : SupportContained sigma tau) :
    SupportContained rho tau :=
  Set.Subset.trans sigmaTau rhoSigma

/-- The finite scalar trace-log branch. It is mathematically appropriate only
when the first state is supported inside the second. -/
noncomputable def finiteTraceLogRelativeEntropy
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : DensityState n) : ℝ :=
  (Matrix.trace
    (rho.1 * (CFC.log rho.1 - CFC.log sigma.1))).re

open scoped Classical in
/-- Support-aware extended quantum relative entropy. The unsupported branch is
`top`; the supported branch retains the finite trace-log expression. -/
noncomputable def extendedQuantumRelativeEntropy
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : DensityState n) : WithTop ℝ :=
  if SupportContained rho sigma then
    (finiteTraceLogRelativeEntropy rho sigma : WithTop ℝ)
  else
    ⊤

@[simp]
theorem finiteTraceLogRelativeEntropy_self
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho : DensityState n) :
    finiteTraceLogRelativeEntropy rho rho = 0 := by
  simp only [finiteTraceLogRelativeEntropy, sub_self, mul_zero]
  rw [show (0 : CStarMatrix n n ℂ) = (0 : Matrix n n ℂ) from rfl,
    Matrix.trace_zero, Complex.zero_re]

@[simp]
theorem extendedQuantumRelativeEntropy_self
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho : DensityState n) :
    extendedQuantumRelativeEntropy rho rho = 0 := by
  simp [extendedQuantumRelativeEntropy]

theorem extendedQuantumRelativeEntropy_eq_coe_of_support
    {n : Type*} [Fintype n] [DecidableEq n]
    {rho sigma : DensityState n}
    (support : SupportContained rho sigma) :
    extendedQuantumRelativeEntropy rho sigma =
      finiteTraceLogRelativeEntropy rho sigma := by
  simp [extendedQuantumRelativeEntropy, support]

theorem extendedQuantumRelativeEntropy_eq_top_of_not_support
    {n : Type*} [Fintype n] [DecidableEq n]
    {rho sigma : DensityState n}
    (supportFailure : ¬SupportContained rho sigma) :
    extendedQuantumRelativeEntropy rho sigma = ⊤ := by
  simp [extendedQuantumRelativeEntropy, supportFailure]

theorem extendedQuantumRelativeEntropy_eq_top_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : DensityState n) :
    extendedQuantumRelativeEntropy rho sigma = ⊤ <->
      ¬SupportContained rho sigma := by
  classical
  by_cases support : SupportContained rho sigma
  · simp [extendedQuantumRelativeEntropy, support]
  · simp [extendedQuantumRelativeEntropy, support]

theorem extendedQuantumRelativeEntropy_ne_top_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    (rho sigma : DensityState n) :
    extendedQuantumRelativeEntropy rho sigma ≠ ⊤ <->
      SupportContained rho sigma := by
  rw [ne_eq, extendedQuantumRelativeEntropy_eq_top_iff]
  simp

#print axioms supportContained_trans
#print axioms extendedQuantumRelativeEntropy_eq_top_iff
#print axioms extendedQuantumRelativeEntropy_self

end D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
