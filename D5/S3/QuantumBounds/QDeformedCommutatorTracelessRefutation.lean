/- GID: D5/S3/QuantumBounds/QDeformedCommutatorTracelessRefutation
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/QDeformedCommutatorTracelessRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumBounds/QDeformedCommutatorTracelessRefutation.claim; result=D5/S3/QuantumBounds/QDeformedCommutatorTracelessRefutation.result; claim=D5/S3/QuantumBounds/QDeformedCommutatorTracelessRefutation.claim
   digest: A traceless five-dimensional pair violates the q-deformed commutator bound. -/

/-
proof_shape: claim: not-applicable (definition)
proof_shape: result: bind-only
escape_witness: claim: none; result: none
admission_basis: open-problem-resolution (#13930; Refuted)
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

namespace D5.S3.QuantumBounds.QDeformedCommutatorTracelessRefutation

open scoped BigOperators Matrix
open D5.S3.Quantum.Entanglement.MoreauYosidaFormationSelectiveLoccRefutation (mass)

/-- The inequality clause of Chruściński–Kimura–Ohno–Singal Conjecture 1. -/
def claim : Prop := ∀ (n : ℕ) (q : ℝ), 0 < q → ∀ A B : Matrix (Fin n) (Fin n) ℂ,
  (Matrix.trace A = 0 ∨ Matrix.trace B = 0) →
    mass (A * B - (q : ℂ) • (B * A)) ≤ (1 + q ^ 2) * mass A * mass B

/-- At q = 2, a traceless five-dimensional pair exceeds the proposed bound by 444. -/
theorem result : ¬ claim := by
  let A : Matrix (Fin 5) (Fin 5) ℂ :=
    !![6, 42, 0, 0, 0;
       0, -3, 0, 0, 0;
       0, 0, -1, 0, 0;
       0, 0, 0, -1, 0;
       0, 0, 0, 0, -1]
  let B : Matrix (Fin 5) (Fin 5) ℂ :=
    !![6, 0, 0, 0, 0;
       -42, -3, 0, 0, 0;
       0, 0, -1, 0, 0;
       0, 0, 0, -1, 0;
       0, 0, 0, 0, -1]
  have htrace : Matrix.trace A = 0 := by
    norm_num [A, Matrix.trace, Matrix.diag_apply, Fin.sum_univ_succ]
  have hA : mass A = 1812 := by
    change (∑ i, ∑ j, Complex.normSq (A i j)) = 1812
    norm_num [A, Fin.sum_univ_succ, Complex.normSq_apply]
  have hB : mass B = 1812 := by
    change (∑ i, ∑ j, Complex.normSq (B i j)) = 1812
    norm_num [B, Fin.sum_univ_succ, Complex.normSq_apply]
  have hcomm : A * B - (2 : ℂ) • (B * A) =
      !![-1800, -630, 0, 0, 0;
         630, 3519, 0, 0, 0;
         0, 0, -1, 0, 0;
         0, 0, 0, -1, 0;
         0, 0, 0, 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A, B, Matrix.mul_apply, Fin.sum_univ_succ]
  have hnorm : mass (A * B - (2 : ℂ) • (B * A)) = 16417164 := by
    change (∑ i, ∑ j, Complex.normSq ((A * B - (2 : ℂ) • (B * A)) i j)) = 16417164
    rw [hcomm]
    norm_num [Fin.sum_univ_succ, Complex.normSq_apply]
  intro h
  have hbound := h 5 2 (by norm_num) A B (Or.inl htrace)
  norm_num only [Complex.ofReal_ofNat, hnorm, hA, hB] at hbound

#print axioms result

end D5.S3.QuantumBounds.QDeformedCommutatorTracelessRefutation
