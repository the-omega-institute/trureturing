/- GID: D5/S3/Observer/ProbabilisticClosure/ThreeStateMemoryKernel
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/ThreeStateMemoryKernel
   mirror-E: none(waiver:universal-exact-memory-family)
   anchors: []
   utility: none
   digest: The existing reversible three-state chain has an exact all-lag
     geometric memory kernel, derived from its actual hidden block. -/

import D5.S3.Observer.ProbabilisticClosure.ReversibleThreeStateWitness

set_option autoImplicit false
open scoped Matrix BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.ThreeStateMemoryKernel

open ReversibleThreeStateWitness ReversibleProjectionMemory

/-- The eigenvalue of the one-dimensional hidden block, not an eigenvalue
asserted for the complete three-state chain. -/
def hiddenFactor (a b : Real) : Real := 1 - 2 * a - b / 2

/-- The actual projected block return after k hidden steps. At lag zero this
is the previously defined two-step compression defect. -/
def feedback (a b : Real) (k : Nat) : Matrix (Fin 3) (Fin 3) Real :=
  (observe * kernel a b * (1 - observe)) *
    (((1 - observe) * kernel a b * (1 - observe)) ^ k) *
      ((1 - observe) * kernel a b * observe)

/-- All lags are obtained from the actual hidden-block recurrence. This proves
an entire kernel sequence, rather than fitting one- or two-step endpoints. -/
theorem feedback_geometric (a b : Real) (k : Nat) :
    feedback a b k = (hiddenFactor a b) ^ k • defect observe (kernel a b) := by
  let Q : Matrix (Fin 3) (Fin 3) Real := 1 - observe
  let D : Matrix (Fin 3) (Fin 3) Real := Q * kernel a b * Q
  let C : Matrix (Fin 3) (Fin 3) Real := Q * kernel a b * observe
  let B : Matrix (Fin 3) (Fin 3) Real := observe * kernel a b * Q
  have hP : observe * observe = observe := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [observe, Matrix.mul_apply, Fin.sum_univ_three]
  have hQ : Q * Q = Q := by
    dsimp [Q]
    calc
      (1 - observe) * (1 - observe) = 1 - observe - observe + observe * observe := by
        noncomm_ring
      _ = 1 - observe := by rw [hP]; abel
  have hDC : D * C = hiddenFactor a b • C := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [D, C, Q, hiddenFactor, observe, kernel, Matrix.mul_apply,
        Fin.sum_univ_three] <;> ring
  have hpow : ∀ n : Nat, D ^ n * C = (hiddenFactor a b) ^ n • C := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_assoc, ih, mul_smul_comm, hDC, smul_smul, pow_succ]
  have hBC : B * C = defect observe (kernel a b) := by
    rw [defect_eq_hidden_roundtrip observe (kernel a b) hP]
    change (observe * kernel a b * Q) * (Q * kernel a b * observe) =
      observe * kernel a b * Q * kernel a b * observe
    calc
      _ = observe * kernel a b * (Q * Q) * kernel a b * observe := by
        simp only [mul_assoc]
      _ = _ := by rw [hQ]
  change B * D ^ k * C = _
  rw [mul_assoc, hpow, mul_smul_comm, hBC]

/-- Knowing the exact first two observations recovers a hidden perturbation,
but no uniformly stable inverse exists as the cross-fiber coupling tends to zero.
For every prescribed amplification C0 there are normalized nonnegative states
with equal present observations, a fixed hidden gap, and a first-step observed
gap less than 1/C0. This is an explicit family in the actual chain. -/
theorem no_uniform_hidden_recovery (C0 : Real) (hC0 : 0 < C0) :
    ∃ a b : Real, 0 < a ∧ 0 < b ∧ a + b < 1 ∧
      ∃ x y : Fin 3 → Real,
        (∀ i, 0 ≤ x i ∧ 0 ≤ y i) ∧
        (∑ i, x i) = 1 ∧ (∑ i, y i) = 1 ∧
        observe *ᵥ x = observe *ᵥ y ∧
        |(x 0 - x 1) - (y 0 - y 1)| = 1 ∧
        0 < |(kernel a b *ᵥ x) 2 - (kernel a b *ᵥ y) 2| ∧
        C0 * (∑ i, |(observe *ᵥ (kernel a b *ᵥ x)) i - (observe *ᵥ (kernel a b *ᵥ y)) i|) < 1 := by
  let b : Real := 1 / (4 * (C0 + 1))
  have hd : 0 < 4 * (C0 + 1) := by positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hprod : b * (4 * (C0 + 1)) = 1 := by
    dsimp [b]
    exact div_mul_cancel₀ 1 (ne_of_gt hd)
  have hCb : 0 < C0 * b := mul_pos hC0 hb
  have hsmall : b < 1 / 4 := by nlinarith
  have hbound : C0 * b < 1 := by nlinarith
  let x : Fin 3 → Real := ![1/2, 0, 1/2]
  let y : Fin 3 → Real := ![0, 1/2, 1/2]
  refine ⟨1/4, b, by norm_num, hb, by linarith, x, y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [x, y]
  · norm_num [x, Fin.sum_univ_three]
  · norm_num [y, Fin.sum_univ_three]
  · ext i
    fin_cases i <;> norm_num [observe, x, y, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · norm_num [x, y]
  · have he : (kernel (1/4) b *ᵥ x) 2 - (kernel (1/4) b *ᵥ y) 2 = -b/2 := by
      norm_num [observe, kernel, x, y, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
    rw [he, abs_div, abs_neg, abs_of_pos hb]
    norm_num <;> linarith
  · have he : (∑ i, |(observe *ᵥ (kernel (1/4) b *ᵥ x)) i - (observe *ᵥ (kernel (1/4) b *ᵥ y)) i|) = b := by
      have hv : observe *ᵥ (kernel (1/4) b *ᵥ x) - observe *ᵥ (kernel (1/4) b *ᵥ y) = ![b/4, b/4, -b/2] := by
        ext i
        fin_cases i <;>
          norm_num [observe, kernel, x, y, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring
      change (∑ i, |(observe *ᵥ (kernel (1/4) b *ᵥ x) - observe *ᵥ (kernel (1/4) b *ᵥ y)) i|) = b
      rw [hv, Fin.sum_univ_three]
      norm_num [abs_div, abs_neg, abs_of_pos hb] <;> ring
    rw [he]
    exact hbound

#print axioms feedback_geometric
#print axioms no_uniform_hidden_recovery

end D5.S3.Observer.ProbabilisticClosure.ThreeStateMemoryKernel
