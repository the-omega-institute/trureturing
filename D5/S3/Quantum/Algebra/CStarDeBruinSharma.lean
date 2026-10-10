/- GID: D5/S3/Quantum/Algebra/CStarDeBruinSharma
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CStarDeBruinSharma
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/CStarDeBruinSharma.claimDeBruinSharma; result=D5/S3/Quantum/Algebra/CStarDeBruinSharma.result; claim=D5/S3/Quantum/Algebra/CStarDeBruinSharma.claimDeBruinSharma
   digest: A cubic matrix polynomial refutes Krishna's C*-algebraic conjecture. -/

/-
proof_shape: defect: bind-only (consumer: first_inequality_fails)
proof_shape: first_inequality_fails: bind-only (consumer: result)
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#14845; Refuted)
Direct frozen dependencies: `D5/S3/Quantum/Algebra/CStarSchoenberg` (`factorization`; statement_id sha256:02d14b413765b9de9f51468f70efa5f28abb15de47940c90b819d00e825af29d, `negative_e11_not_posSemidef`; statement_id sha256:b046bafb8ec86715dac7bcc201125b37e18aa6b29f8a409346b775fd1a0276d6).
All proof steps instantiate Mathlib facts or normalize the explicit matrix entries.
The algebra is restricted to unital C*-algebras in Type with a compatible partial
order and StarOrderedRing. This weakens the source claim; its negation refutes it.
The degree restriction is 2 <= d; the counterexample has d = 3.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import D5.S3.Quantum.Algebra.CStarSchoenberg

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open D5.S3.Quantum.Algebra.CStarSchoenberg

namespace D5.S3.Quantum.Algebra.CStarDeBruinSharma

noncomputable section

def claimDeBruinSharma : Prop :=
  ∀ (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (d : ℕ),
    2 ≤ d → ∀ (a : Fin d → A) (b : Fin (d - 1) → A), DerivFactors d a b →
    (∑ j, a j) = 0 →
    ((∑ k, (b k * star (b k)) ^ 2) ≤
      (2 / (d : ℂ) ^ 2) • (∑ j, a j * star (a j)) ^ 2 +
      (((d : ℂ) - 4) / d) • (∑ j, (a j * star (a j)) ^ 2)) ∧
    ((∑ k, (star (b k) * b k) ^ 2) ≤
      (2 / (d : ℂ) ^ 2) • (∑ j, star (a j) * a j) ^ 2 +
      (((d : ℂ) - 4) / d) • (∑ j, (star (a j) * a j) ^ 2))

private theorem defect :
    ((2 / (3 : ℂ) ^ 2) • (∑ j, a j * star (a j)) ^ 2 +
      (((3 : ℂ) - 4) / 3) • (∑ j, (a j * star (a j)) ^ 2)) -
      (∑ k, (b k * star (b k)) ^ 2) = (-4 / 27 : ℂ) • (Matrix.single 0 0 (1 : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a, b, u, Matrix.single, y, Fin.sum_univ_succ, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, map_ofNat, map_natCast, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, dotProduct]

private theorem first_inequality_fails :
    ¬ (∑ k, (b k * star (b k)) ^ 2) ≤
      (2 / (3 : ℂ) ^ 2) • (∑ j, a j * star (a j)) ^ 2 +
      (((3 : ℂ) - 4) / 3) • (∑ j, (a j * star (a j)) ^ 2) := by
  intro h
  have hp := Matrix.le_iff.mp h
  rw [defect] at hp
  exact negative_e11_not_posSemidef (-4 / 27) (by norm_num) (by simpa using hp)

theorem result : ¬ claimDeBruinSharma := by
  intro h
  exact first_inequality_fails (h (Matrix (Fin 2) (Fin 2) ℂ) 3 (by norm_num) a b factorization sum_a).1


end
end D5.S3.Quantum.Algebra.CStarDeBruinSharma
