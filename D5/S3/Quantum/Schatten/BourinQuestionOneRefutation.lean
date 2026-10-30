/- GID: D5/S3/Quantum/Schatten/BourinQuestionOneRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Schatten/BourinQuestionOneRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Schatten/BourinQuestionOneRefutation.claim; result=D5/S3/Quantum/Schatten/BourinQuestionOneRefutation.result; claim=D5/S3/Quantum/Schatten/BourinQuestionOneRefutation.claim
   digest: A two-block positive map refutes Bourin's symmetric-norm inequality. -/

/-
admission_basis: open-problem-resolution (#18573; Refuted)
proof_shape: claim: definition (bind-only laws); escape_witness: none
  consumer: result
  Direct frozen dependencies: F1, F2
proof_shape: phi: definition (bind-only laws); escape_witness: none
  consumer: phi_positive, phi_reflect, cfc_phi_one, result
  Direct frozen dependencies: none
proof_shape: frobeniusNorm: definition (bind-only laws); escape_witness: none
  consumer: result
  Direct frozen dependencies: F1, F3, F4, F5, F6, F7
proof_shape: phi_positive: bind-only; escape_witness: none
  consumer: result
  Direct frozen dependencies: none
proof_shape: phi_reflect: bind-only; escape_witness: none
  consumer: result
  Direct frozen dependencies: none
proof_shape: cfc_phi_one: bind-only; escape_witness: none
  consumer: result
  Direct frozen dependencies: F8
proof_shape: cfc_one: bind-only; escape_witness: none
  consumer: result
  Direct frozen dependencies: none
proof_shape: result: bind-only; escape_witness: none
  Direct frozen dependencies: F1, F2, F3, F4, F5, F6, F7, F9, F8
Direct frozen dependencies (declaration identities):
  F1: D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.UINorm
    Lean name: D5.S3.Quantum.Schatten.UINorm
    statement_id: sha256:9b86785976d46018653b00e188157046f68dc9fbb79fc37ee324fcf5d43dcb73
  F2: D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.N
    Lean name: D5.S3.Quantum.Schatten.UINorm.N
    statement_id: sha256:224d0001974f58ba1a1fe94e60774112a6f61062047aeb270709560c459c6457
  F3: D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.mk
    Lean name: D5.S3.Quantum.Schatten.UINorm.mk
    statement_id: sha256:13d1288e28576a9f0760211a84e9bf0f3da512aa9da3641536b36ebc5adb0ef9
  F4: D5/S3/Weil/ZetaLinear/PosIndex.frobSq
    Lean name: RHLinalg.frobSq
    statement_id: sha256:87344d8035a8c18278b7631968fd9b17dbe3a4221dfb10f55432779f1064e116
  F5: D5/S3/Quantum/Matrix/CommutatorGap.frobSq_unitary_right
    Lean name: D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_right
    statement_id: sha256:63c2cd1b86c23c2972e5bf796750663ea1953eea0946f6abb48832ba5fa201e7
  F6: D5/S3/Quantum/Matrix/CommutatorGap.frobSq_unitary_left
    Lean name: D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_left
    statement_id: sha256:8a106b7c09f759560b1ae0469b6698029e4c2b0b2000528a314e20e06f5013ff
  F7: D5/S3/Quantum/GNSMatrix.frobenius_norm_sq_eq_trace
    Lean name: D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace
    statement_id: sha256:470140292aee89705512206af514f5a42fdc3948e5c9195d302613a47b859917
  F8: D5/S3/Quantum/Dynamics/EntropyProductionCoherenceDeletionIdentity.cfc_diagonal
    Lean name: D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal
    statement_id: sha256:873e4955783786d99a250879f3da4640dab6550433b567150988ca3aaede9fe0
  F9: D5/S3/Quantum/Schatten/UnitarilyInvariantNorm.nonneg
    Lean name: D5.S3.Quantum.Schatten.UINorm.nonneg
    statement_id: sha256:aa160106a67f52e618fc9d814d161163633013bcaafa358f874bf42e8ae36569
The positive-contraction sets are written as {X | 0 ≤ X ∧ X ≤ 1} in claim;
this is the defining condition of IsEffect, with no new predicate declaration.
The symmetric norms are the frozen UINorm structure, whose laws agree
with the source's norm and two-sided unitary-invariance conditions.
The diagonal map is composed from diagonalLinearMap, LinearMap.proj and smulRight.
PosIndex defines frobSq, whose equation is used when rewriting that definition.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import D5.S3.Quantum.GNSMatrix
import D5.S3.Quantum.Matrix.CommutatorGap
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
import D5.S3.Weil.ZetaLinear.PosIndex

set_option autoImplicit false

noncomputable section
namespace D5.S3.Quantum.Schatten.BourinQuestionOneRefutation
open _root_.Matrix
open scoped MatrixOrder ComplexOrder

/-- Question 1 (Bourin 2008): if a positive linear map `Φ : M_n → M_k` satisfies
`Φ⁻¹(F_k) ⊂ F_n`, then `‖f ∘ Φ(M)‖ ≤ ‖Φ ∘ f(M)‖` for all `M ≥ 0`, all symmetric norms and all
non-negative concave functions `f` on the positive half line (functional calculus `cfc`). -/
def claim : Prop :=
  ∀ (n k : ℕ) (Φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin k) (Fin k) ℂ),
    (∀ X, 0 ≤ X → 0 ≤ Φ X) →
    Φ ⁻¹' {X | 0 ≤ X ∧ X ≤ 1} ⊆ {X | 0 ≤ X ∧ X ≤ 1} →
      ∀ (M : Matrix (Fin n) (Fin n) ℂ), 0 ≤ M →
        ∀ (N : D5.S3.Quantum.Schatten.UINorm k) (f : ℝ → ℝ), ConcaveOn ℝ (Set.Ici 0) f →
          (∀ x, 0 ≤ x → 0 ≤ f x) →
            N.N (cfc f (Φ M)) ≤ N.N (Φ (cfc f M))


/-- The diagonal amplification used in the counterexample. -/
private def phi : Matrix (Fin 1) (Fin 1) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Matrix.diagonalLinearMap (Fin 2) ℂ ℂ).comp
    (((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).comp
      (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => Fin 1 → ℂ) 0)).smulRight
        (![1, (1 : ℂ) / 4] : Fin 2 → ℂ))

section Frobenius
open scoped Matrix.Norms.Frobenius

private def frobeniusNorm (k : ℕ) : D5.S3.Quantum.Schatten.UINorm k where
  N X := ‖X‖
  nonneg := norm_nonneg
  eq_zero_iff X := norm_eq_zero
  smul_eq := norm_smul
  add_le := norm_add_le
  unitary_invariant U V X hU hV := by
    have he := (D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_right
      (U * X) ⟨V, hV⟩).trans
      (D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_left X ⟨U, hU⟩)
    change RHLinalg.frobSq (U * X * V) = RHLinalg.frobSq X at he
    rw [RHLinalg.frobSq, RHLinalg.frobSq,
      ← D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace,
      ← D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace] at he
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he
end Frobenius

private theorem phi_positive : ∀ X, 0 ≤ X → 0 ≤ phi X := by
  intro X hX
  have hx : 0 ≤ X 0 0 := hX.posSemidef.diag_nonneg
  change 0 ≤ diagonal (X 0 0 • (![1, (1 : ℂ) / 4] : Fin 2 → ℂ))
  apply Matrix.PosSemidef.nonneg
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i
  · simpa [smul_eq_mul, div_eq_mul_inv] using hx
  · simpa [smul_eq_mul, div_eq_mul_inv] using div_nonneg hx (show (0 : ℂ) ≤ 4 from zero_le_four)

private theorem phi_reflect : phi ⁻¹' {X | 0 ≤ X ∧ X ≤ 1} ⊆ {X | 0 ≤ X ∧ X ≤ 1} := by
  intro X hX
  change 0 ≤ diagonal (X 0 0 • (![1, (1 : ℂ) / 4] : Fin 2 → ℂ)) ∧
    diagonal (X 0 0 • (![1, (1 : ℂ) / 4] : Fin 2 → ℂ)) ≤ 1 at hX
  have hp : 0 ≤ X 0 0 := by
    simpa [smul_eq_mul, div_eq_mul_inv] using hX.1.posSemidef.diag_nonneg (i := (0 : Fin 2))
  have hq : 0 ≤ 1 - X 0 0 := by
    simpa [smul_eq_mul, div_eq_mul_inv] using (Matrix.le_iff.mp hX.2).diag_nonneg (i := (0 : Fin 2))
  have he : X = diagonal (fun _ : Fin 1 => X 0 0) := by
    calc
      X = diagonal X.diag := (Matrix.isDiag_of_subsingleton X).diagonal_diag.symm
      _ = diagonal (fun _ : Fin 1 => X 0 0) := by
        congr 1
        funext i
        rw [Matrix.diag_apply, Fin.fin_one_eq_zero i]
  constructor
  · rw [he]
    exact (Matrix.PosSemidef.diagonal (fun _ => hp)).nonneg
  · rw [Matrix.le_iff, he, ← Matrix.diagonal_one, Matrix.diagonal_sub]
    exact Matrix.PosSemidef.diagonal (fun _ => hq)

private theorem cfc_phi_one :
    cfc Real.sqrt (phi 1) = diagonal ![(1 : ℂ), 1/2] := by
  have he : phi 1 = diagonal (fun i : Fin 2 => ((![1, 1/4] i : ℝ) : ℂ)) := by
    change diagonal ((1 : ℂ) • (![1, (1 : ℂ) / 4] : Fin 2 → ℂ)) = _
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]
  rw [he, D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal]
  congr 1
  funext i
  fin_cases i <;> norm_num [Real.sqrt_div]

private theorem cfc_one : cfc Real.sqrt (1 : Matrix (Fin 1) (Fin 1) ℂ) = 1 := by
  simp only [cfc_apply_one, Real.sqrt_one, map_one]

theorem result : ¬ claim := by
  intro h
  have hi := h 1 2 phi phi_positive phi_reflect 1 zero_le_one
    (frobeniusNorm 2) Real.sqrt Real.strictConcaveOn_sqrt.concaveOn
    (fun x _ => Real.sqrt_nonneg x)
  rw [cfc_phi_one, cfc_one] at hi
  change (frobeniusNorm 2).N (diagonal ![(1 : ℂ), 1/2]) ≤
    (frobeniusNorm 2).N (diagonal ((1 : ℂ) • (![1, (1 : ℂ) / 4] : Fin 2 → ℂ))) at hi
  have hs := mul_self_le_mul_self ((frobeniusNorm 2).nonneg (diagonal ![(1 : ℂ), 1/2])) hi
  dsimp only [frobeniusNorm] at hs
  simp only [← sq, Matrix.frobenius_norm_def, Real.rpow_two, ← Real.sqrt_eq_rpow] at hs
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at hs
  norm_num [Matrix.diagonal, Fin.sum_univ_two, Complex.norm_div] at hs

end D5.S3.Quantum.Schatten.BourinQuestionOneRefutation
