/- GID: D5/S3/Observer/ProbabilisticClosure/ReversibleThreeStateWitness
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/ReversibleThreeStateWitness
   mirror-E: none(waiver:universal-real-parameter-family)
   anchors: []
   utility: none
   digest: An explicit reversible stochastic family has the same stationary law
     at every parameter but a nonzero squared projection-memory defect. -/

import D5.S3.Observer.ProbabilisticClosure.ReversibleProjectionMemory
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open scoped BigOperators Matrix

namespace D5.S3.Observer.ProbabilisticClosure.ReversibleThreeStateWitness

open ReversibleProjectionMemory

/-- A nearest-neighbor stochastic family when a,b >= 0 and a+b <= 1. -/
def kernel (a b : Real) : Matrix (Fin 3) (Fin 3) Real :=
  ![![1-a, a, 0], ![a, 1-a-b, b], ![0, b, 1-b]]

/-- Conditional expectation for the uniform stationary measure under the
observation that merges states zero and one and keeps state two separate. -/
def observe : Matrix (Fin 3) (Fin 3) Real :=
  ![![(1:Real)/2, 1/2, 0], ![1/2, 1/2, 0], ![0, 0, 1]]

private theorem observe_idempotent : observe * observe = observe := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [observe, Matrix.mul_apply, Fin.sum_univ_three]

private theorem observe_selfadjoint : observeᴴ = observe := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [observe, Matrix.conjTranspose_apply]

private theorem kernel_selfadjoint (a b : Real) : (kernel a b)ᴴ = kernel a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kernel, Matrix.conjTranspose_apply]

/-- All parameters share the same equilibrium measure; this does not identify
transition rates or a Markovian projected law. -/
theorem stochastic_and_stationary (a b : Real)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b ≤ 1) :
    (∀ i j, 0 ≤ kernel a b i j) ∧
      (∀ i, ∑ j, kernel a b i j = 1) ∧
      (∀ j, ∑ i, ((1:Real)/3) * kernel a b i j = 1/3) ∧
      (kernel a b)ᴴ = kernel a b := by
  refine ⟨?_, ?_, ?_, kernel_selfadjoint a b⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> dsimp [kernel] <;> linarith
  · intro i
    fin_cases i <;> simp [kernel, Fin.sum_univ_three] <;> ring
  · intro j
    fin_cases j <;> simp [kernel, Fin.sum_univ_three] <;> ring

/-- This visible transition statistic has a strictly positive two-step memory
correction for b != 0, although all stationary energies may be taken equal. -/
theorem exact_memory_entry (a b : Real) :
    defect observe (kernel a b) 2 2 = b^2/2 := by
  norm_num [defect, compressed, observe, kernel, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- The projected dynamics is exactly closed only when the cross-fiber edge
vanishes. An arbitrarily slow but nonzero coupling still has nonzero memory. -/
theorem closed_iff_cross_edge_zero (a b : Real) :
    kernel a b * observe = observe * kernel a b * observe ↔ b = 0 := by
  rw [← two_step_closure_iff observe (kernel a b)
    observe_idempotent observe_selfadjoint (kernel_selfadjoint a b)]
  constructor
  · intro h
    have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) Real => M 2 2) h
    rw [exact_memory_entry] at he
    change b^2/2 = 0 at he
    have hb2 : b * b = 0 := by nlinarith
    exact (mul_self_eq_zero.mp hb2)
  · rintro rfl
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [defect, compressed, observe, kernel, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

/-- No equilibrium-only decoder can recover even the single transition entry
K(1,2) on this valid reversible family. The input is the whole stationary vector. -/
theorem no_equilibrium_only_transition_decoder :
    ¬ ∃ f : (Fin 3 → Real) → Real,
      ∀ a b : Real, 0 < a → 0 < b → a+b < 1 →
        f (fun _ => 1/3) = kernel a b 1 2 := by
  rintro ⟨f, hf⟩
  have h₁ := hf (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num)
  have h₂ := hf (1/4) (1/2) (by norm_num) (by norm_num) (by norm_num)
  norm_num [kernel] at h₁ h₂
  linarith

#print axioms stochastic_and_stationary
#print axioms exact_memory_entry
#print axioms closed_iff_cross_edge_zero
#print axioms no_equilibrium_only_transition_decoder

end D5.S3.Observer.ProbabilisticClosure.ReversibleThreeStateWitness
