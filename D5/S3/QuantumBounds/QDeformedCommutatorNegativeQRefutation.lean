/- GID: D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation.claim; result=D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation.result; claim=D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation.claim
   digest: A traceless three-dimensional matrix violates the negative-q commutator bound. -/

/-
proof_shape: g: not-applicable (definition)
proof_shape: claim: not-applicable (definition)
proof_shape: result: bind-only
escape_witness: g: none; claim: none; result: none
admission_basis: open-problem-resolution (#14632; Refuted)
Direct frozen dependencies:
  D5/S3/Quantum/Entanglement/MoreauYosidaFormationSelectiveLoccRefutation.mass
    (statement_id: sha256:cbea7de0ccdfe72c7fc775e14a9f812ca27c7512dd61e730014f61cea580e852).
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.Entanglement.MoreauYosidaFormationSelectiveLoccRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.QuantumBounds.QDeformedCommutatorNegativeQRefutation

open scoped BigOperators Matrix
open D5.S3.Quantum.Entanglement.MoreauYosidaFormationSelectiveLoccRefutation (mass)

/-- The dimension-dependent coefficient in equation (24). -/
def g (n : ℕ) : ℝ := ((n : ℝ) ^ 2 - 3 * n + 3) / (n * (n - 1))

/-- The inequality clause of Chruściński–Kimura–Ohno–Singal Conjecture 2. -/
def claim : Prop := ∀ (n : ℕ), 2 ≤ n → ∀ (q : ℝ), q ≤ 0 → ∀ A B : Matrix (Fin n) (Fin n) ℂ,
  (Matrix.trace A = 0 ∨ Matrix.trace B = 0) →
    mass (A * B - (q : ℂ) • (B * A)) ≤ max (g n * (1 - q) ^ 2) (1 + q ^ 2) * mass A * mass B

/-- At q = -1, a traceless three-dimensional matrix gives 16 > 12. -/
theorem result : ¬ claim := by
  let A : Matrix (Fin 3) (Fin 3) ℂ :=
    !![2, 0, 0;
       0, -1, 0;
       0, 0, -1]
  let B : Matrix (Fin 3) (Fin 3) ℂ :=
    !![1, 0, 0;
       0, 0, 0;
       0, 0, 0]
  have htrace : Matrix.trace A = 0 := by
    norm_num [A, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_succ]
  have hA : mass A = 6 := by
    change (∑ i, ∑ j, Complex.normSq (A i j)) = 6
    norm_num [A, Fin.sum_univ_succ, Complex.normSq_apply]
  have hB : mass B = 1 := by
    change (∑ i, ∑ j, Complex.normSq (B i j)) = 1
    norm_num [B, Fin.sum_univ_succ, Complex.normSq_apply]
  have hcomm : A * B - ((-1 : ℝ) : ℂ) • (B * A) =
      !![4, 0, 0;
         0, 0, 0;
         0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, B, Matrix.mul_apply, Fin.sum_univ_succ]
  have hnorm : mass (A * B - ((-1 : ℝ) : ℂ) • (B * A)) = 16 := by
    change (∑ i, ∑ j, Complex.normSq ((A * B - ((-1 : ℝ) : ℂ) • (B * A)) i j)) = 16
    rw [hcomm]
    norm_num [Fin.sum_univ_succ, Complex.normSq_apply]
  have hg : g 3 = 1 / 2 := by
    norm_num [g]
  have hmax : max (g 3 * (1 - (-1 : ℝ)) ^ 2) (1 + (-1 : ℝ) ^ 2) = 2 := by
    norm_num [hg]
  intro h
  have hbound := h 3 (by norm_num) (-1) (by norm_num) A B (Or.inl htrace)
  rw [hnorm, hmax, hA, hB] at hbound
  norm_num at hbound

#print axioms result

end D5.S3.QuantumBounds.QDeformedCommutatorNegativeQRefutation
