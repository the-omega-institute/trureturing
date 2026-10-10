/- GID: D5/S3/Quantum/Algebra/CStarKushelTyaglov
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CStarKushelTyaglov
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/CStarKushelTyaglov.claimKushelTyaglov; result=D5/S3/Quantum/Algebra/CStarKushelTyaglov.result; claim=D5/S3/Quantum/Algebra/CStarKushelTyaglov.claimKushelTyaglov
   digest: A cubic matrix polynomial refutes Krishna's C*-algebraic conjecture. -/

/-
proof_shape: defect: bind-only (consumer: result)
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#14845; Refuted)
Direct frozen dependencies: `D5/S3/Quantum/Algebra/CStarSchoenberg` (`factorization`; statement_id sha256:02d14b413765b9de9f51468f70efa5f28abb15de47940c90b819d00e825af29d, `negative_e11_not_posSemidef`; statement_id sha256:b046bafb8ec86715dac7bcc201125b37e18aa6b29f8a409346b775fd1a0276d6).
All proof steps instantiate Mathlib facts or normalize the explicit matrix entries.
The algebra is restricted to unital C*-algebras in Type with a compatible partial
order and StarOrderedRing. This weakens the source claim; its negation refutes it.
The degree restriction is 2 <= d; the counterexample has d = 3.
Conjecture 2.4 is read with n = d, as fixed in issue #14845.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import D5.S3.Quantum.Algebra.CStarSchoenberg

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open D5.S3.Quantum.Algebra.CStarSchoenberg

namespace D5.S3.Quantum.Algebra.CStarKushelTyaglov

noncomputable section

def claimKushelTyaglov : Prop :=
  ∀ (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (d : ℕ),
    2 ≤ d → ∀ (a : Fin d → A) (b : Fin (d - 1) → A), DerivFactors d a b →
    let S := ∑ j, a j
    let T := (∑ j, a j ^ 2) - (1 / (d : ℂ) ^ 2) • S ^ 2
    ((∑ k, (b k * star (b k)) ^ 2) ≤
      (((d : ℂ) - 6) / d) • (∑ j, (a j * star (a j)) ^ 2) +
      (1 / (d : ℂ) ^ 2) • (∑ j, a j * star (a j)) ^ 2 +
      (1 / (d : ℂ) ^ 2) • (T * star T) +
      (2 / (d : ℂ)) • (∑ j, a j * (a j + (1 / (d : ℂ)) • S) *
        star (a j + (1 / (d : ℂ)) • S) * star (a j)) -
      (4 / (d : ℂ) ^ 3) • (∑ j, a j * S * star S * star (a j))) ∧
    ((∑ k, (star (b k) * b k) ^ 2) ≤
      (((d : ℂ) - 6) / d) • (∑ j, (star (a j) * a j) ^ 2) +
      (1 / (d : ℂ) ^ 2) • (∑ j, star (a j) * a j) ^ 2 +
      (1 / (d : ℂ) ^ 2) • (star T * T) +
      (2 / (d : ℂ)) • (∑ j, star (a j) * star (a j + (1 / (d : ℂ)) • S) *
        (a j + (1 / (d : ℂ)) • S) * a j) -
      (4 / (d : ℂ) ^ 3) • (∑ j, star (a j) * star S * S * a j))

private theorem defect :
    let S := ∑ j, a j
    let T := (∑ j, a j ^ 2) - (1 / (3 : ℂ) ^ 2) • S ^ 2
    ((((3 : ℂ) - 6) / 3) • (∑ j, (a j * star (a j)) ^ 2) +
      (1 / (3 : ℂ) ^ 2) • (∑ j, a j * star (a j)) ^ 2 +
      (1 / (3 : ℂ) ^ 2) • (T * star T) +
      (2 / (3 : ℂ)) • (∑ j, a j * (a j + (1 / (3 : ℂ)) • S) *
        star (a j + (1 / (3 : ℂ)) • S) * star (a j)) -
      (4 / (3 : ℂ) ^ 3) • (∑ j, a j * S * star S * star (a j))) -
      (∑ k, (b k * star (b k)) ^ 2) = (-67 / 27 : ℂ) • (Matrix.single 0 0 (1 : ℂ)) := by
  dsimp only
  rw [sum_a]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a, b, u, Matrix.single, y, Fin.sum_univ_succ, pow_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, map_ofNat, map_natCast, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, dotProduct]

theorem result : ¬ claimKushelTyaglov := by
  intro h
  have hle := (h (Matrix (Fin 2) (Fin 2) ℂ) 3 (by norm_num) a b factorization).1
  have hp := Matrix.le_iff.mp hle
  have hd := defect
  dsimp only at hd
  norm_num only [Nat.cast_ofNat] at hp hd
  rw [hd] at hp
  exact negative_e11_not_posSemidef (-67 / 27) (by norm_num) (by simpa [neg_div] using hp)


end
end D5.S3.Quantum.Algebra.CStarKushelTyaglov
