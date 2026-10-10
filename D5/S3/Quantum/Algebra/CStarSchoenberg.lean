/- GID: D5/S3/Quantum/Algebra/CStarSchoenberg
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CStarSchoenberg
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Algebra/CStarSchoenberg.claimSchoenberg; result=D5/S3/Quantum/Algebra/CStarSchoenberg.result; claim=D5/S3/Quantum/Algebra/CStarSchoenberg.claimSchoenberg
   digest: A cubic matrix polynomial refutes Krishna's C*-algebraic conjecture. -/

/-
proof_shape: sum_a: bind-only (consumer: CStarSchoenberg.defect; CStarDeBruinSharma.result; CStarKushelTyaglov.defect)
proof_shape: factorization: bind-only (consumer: all three result declarations)
proof_shape: negative_e11_not_posSemidef: bind-only (consumer: CStarSchoenberg.first_inequality_fails; CStarDeBruinSharma.first_inequality_fails; CStarKushelTyaglov.result)
proof_shape: defect: bind-only (consumer: first_inequality_fails)
proof_shape: first_inequality_fails: bind-only (consumer: result)
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#14845; Refuted)
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14861
All proof steps instantiate Mathlib facts or normalize the explicit matrix entries.
The algebra is restricted to unital C*-algebras in Type with a compatible partial
order and StarOrderedRing. This weakens the source claim; its negation refutes it.
The degree restriction is 2 <= d; the counterexample has d = 3.
-/

import Mathlib.Analysis.Matrix.Order

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace D5.S3.Quantum.Algebra.CStarSchoenberg

noncomputable section

def orderedDeriv {A : Type} [Ring A] {d : ℕ} (a : Fin d → A) (z : A) : A :=
  ∑ j : Fin d, ((List.ofFn fun i => z - a i).eraseIdx j).prod

def DerivFactors {A : Type} [Ring A] (d : ℕ) (a : Fin d → A)
    (b : Fin (d - 1) → A) : Prop :=
  ∀ z : A, orderedDeriv a z = d • (List.ofFn fun k => z - b k).prod

def claimSchoenberg : Prop :=
  ∀ (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (d : ℕ),
    2 ≤ d → ∀ (a : Fin d → A) (b : Fin (d - 1) → A), DerivFactors d a b →
    ((∑ k, b k * star (b k)) ≤
      (1 / (d : ℂ) ^ 2) • ((∑ j, a j) * star (∑ j, a j)) +
      (((d : ℂ) - 2) / d) • (∑ j, a j * star (a j))) ∧
    ((∑ k, star (b k) * b k) ≤
      (1 / (d : ℂ) ^ 2) • (star (∑ j, a j) * (∑ j, a j)) +
      (((d : ℂ) - 2) / d) • (∑ j, star (a j) * a j))

def y : Matrix (Fin 2) (Fin 2) ℂ := (Matrix.single 0 0 (1 : ℂ)) + (Matrix.single 0 1 (1 : ℂ))

def a : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![(1 / 3 : ℂ) • (2 • (Matrix.single 0 1 (1 : ℂ)) + y),
  (1 / 3 : ℂ) • (-(Matrix.single 0 1 (1 : ℂ)) + y), (1 / 3 : ℂ) • (-(Matrix.single 0 1 (1 : ℂ)) - 2 • y)]
def u : Matrix (Fin 2) (Fin 2) ℂ := (1 / 3 : ℂ) • ((Matrix.single 0 1 (1 : ℂ)) + y)
def b : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := ![u, -u]

theorem sum_a : ∑ j, a j = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a, Matrix.single, y, Fin.sum_univ_succ, Matrix.smul_apply]

theorem factorization : DerivFactors 3 a b := by
  intro z
  rw [three_nsmul]
  simp [orderedDeriv, Fin.sum_univ_succ, List.ofFn_succ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a, b, u, Matrix.single, y, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem negative_e11_not_posSemidef (c : ℝ) (hc : c < 0) :
    ¬ ((c : ℂ) • (Matrix.single 0 0 (1 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef := by
  intro hp
  have h := hp.diag_nonneg (i := 0)
  have hr : 0 ≤ c := by
    simpa [Matrix.single, Matrix.smul_apply, Complex.nonneg_iff] using h
  exact (not_le_of_gt hc) hr

private theorem defect :
    ((1 / (3 : ℂ) ^ 2) • ((∑ j, a j) * star (∑ j, a j)) +
      (((3 : ℂ) - 2) / 3) • (∑ j, a j * star (a j))) -
      (∑ k, b k * star (b k)) = (-2 / 9 : ℂ) • (Matrix.single 0 0 (1 : ℂ)) := by
  rw [sum_a]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [a, b, u, Matrix.single, y, Fin.sum_univ_succ,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, map_ofNat, map_natCast, Matrix.vecMul, dotProduct]

private theorem first_inequality_fails :
    ¬ (∑ k, b k * star (b k)) ≤
      (1 / (3 : ℂ) ^ 2) • ((∑ j, a j) * star (∑ j, a j)) +
      (((3 : ℂ) - 2) / 3) • (∑ j, a j * star (a j)) := by
  intro h
  have hp := Matrix.le_iff.mp h
  rw [defect] at hp
  exact negative_e11_not_posSemidef (-2 / 9) (by norm_num) (by simpa using hp)

theorem result : ¬ claimSchoenberg := by
  intro h
  exact first_inequality_fails (h (Matrix (Fin 2) (Fin 2) ℂ) 3 (by norm_num) a b factorization).1


end
end D5.S3.Quantum.Algebra.CStarSchoenberg
