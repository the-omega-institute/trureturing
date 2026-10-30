/- GID: D5/S3/Quantum/Matrix/SpeziaPerimeterHigherExteriorTraces
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/SpeziaPerimeterHigherExteriorTraces
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Higher exterior traces of the Spezia perimeter matrix vanish. -/

/-
result: proof_shape: bind-only; escape_witness: none.
admission_basis: open-problem-resolution (#21999; Proved).
Direct frozen dependencies (result; same-delivery definitions expanded):
  compoundMatrix: D5/S3/Quantum/Schatten/CompoundMatrices.compoundMatrix
    statement_id: sha256:8980db8903b2315b1fe7fd07789d65246116b687ab0e522997b5a20064e9e5f4
  cauchyBinet: D5/S3/Quantum/Schatten/CompoundMatrices.cauchyBinet
    statement_id: sha256:6fb332c198d4506b8775454dff648409222d03ae0a60e7dbf5fca62ea37506df
  AllOrdered.fintypeLinearOrderClassical:
    D5/S3/Quantum/Schatten/CompoundMatrices.AllOrdered.fintypeLinearOrderClassical
    statement_id: sha256:51c325b1fc306f2bfe8cfe6563cf1ed7c5f0333f1c64d236078cd62a19e02d2e
M: definition; Direct frozen dependencies: none; consumer: claim, result.
claim: definition; Direct frozen dependencies: compoundMatrix above; consumer: result.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22170
The claim uses the existing compoundMatrix and Matrix.trace directly.
The literal entry formula factors through Fin 2; finite case analysis and ring
normalization, Cauchy–Binet, cardinality bounds, and trace_zero prove result.
-/

import D5.S3.Quantum.Schatten.CompoundMatrices

set_option autoImplicit false

namespace D5.S3.Quantum.Matrix.SpeziaPerimeterHigherExteriorTraces

/-- A330700 and A330287: source indices are i.val + 1 and j.val + 1.
The integer entries are interpreted in the complex numbers. -/
def M (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun i j =>
  if i.val + 1 < 3 ∨ j.val + 1 < 3 then
    ((i.val : ℂ) + 1) * ((j.val : ℂ) + 1)
  else
    2 * (((i.val : ℂ) + 1) + ((j.val : ℂ) + 1)) - 4

/-- A330700 COMMENTS, second conjecture line. `compoundMatrix` is the existing
matrix of the exterior power; for k > n its index type is empty. -/
def claim : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (k : ℕ), 2 < k →
    Matrix.trace (compoundMatrix (M n) k) = 0

theorem result : claim := by
  classical
  intro n _hn k hk
  let A : Matrix (Fin n) (Fin 2) ℂ := fun i t =>
    if t = 0 then (i.val : ℂ) + 1 else ((i.val - 1 : ℕ) : ℂ)
  let B : Matrix (Fin 2) (Fin n) ℂ := fun t j =>
    if t = 0 then (j.val : ℂ) + 1 else -((j.val - 1 : ℕ) : ℂ)
  have factor : M n = A * B := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    dsimp [A, B, M]
    split_ifs with h
    · rcases h with hi | hj
      · have hi0 : i.val - 1 = 0 := by omega
        simp [hi0]
      · have hj0 : j.val - 1 = 0 := by omega
        simp [hj0]
    · have hi : 1 ≤ i.val := by omega
      have hj : 1 ≤ j.val := by omega
      simp only [Nat.cast_sub hi, Nat.cast_sub hj, Nat.cast_one]
      ring
  have hempty : IsEmpty {S : Finset (Fin 2) // S.card = k} := ⟨fun S => by
    have hc : S.1.card ≤ 2 := card_finset_fin_le S.1
    omega⟩
  have hz : compoundMatrix (M n) k = 0 := by
    apply Matrix.ext
    intro S T
    change ((M n).submatrix _ _).det = 0
    rw [factor, Matrix.submatrix_mul A B _ (id : Fin 2 → Fin 2) _ Function.bijective_id]
    rw [cauchyBinet]
    exact Finset.sum_eq_zero fun S _ => (hempty.false S).elim
  rw [hz]
  exact Matrix.trace_zero _ _

end D5.S3.Quantum.Matrix.SpeziaPerimeterHigherExteriorTraces
