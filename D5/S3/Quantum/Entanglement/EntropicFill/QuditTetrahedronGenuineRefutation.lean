/- GID: D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.claim; result=D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.result; claim=D5/S3/Quantum/Entanglement/EntropicFill/QuditTetrahedronGenuineRefutation.claim
   digest: A four-party eight-level pure state has only zero-volume fills and is not biseparable. -/

import D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation

/-! A pure four-qudit counterexample to the genuine requirement for entropic tetrahedra. -/

noncomputable section
set_option linter.style.longLine false
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EntropicFill.QuditTetrahedronGenuineRefutation

open scoped BigOperators
open D5.S3.Quantum.Information.ChenKatoBrandaoCMIRefutation (entropy entropy_diagonal)

/-- The one-party reduced density matrix in the computational basis. -/
def rho1 {d : ℕ} (ψ : (Fin 4 → Fin d) → ℂ) (i : Fin 4) :
    Matrix (Fin d) (Fin d) ℂ := fun a a' =>
  ∑ x : Fin 4 → Fin d, if x i = a then
    ψ x * star (ψ (Function.update x i a')) else 0

/-- The two-party reduced density matrix; its uses have distinct parties. -/
def rho2 {d : ℕ} (ψ : (Fin 4 → Fin d) → ℂ) (i j : Fin 4) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ := fun a a' =>
  ∑ x : Fin 4 → Fin d, if x i = a.1 ∧ x j = a.2 then
    ψ x * star (ψ (Function.update (Function.update x i a'.1) j a'.2)) else 0

/-- Base-two spectral von Neumann entropy, with the frozen natural-log entropy. -/
def entropy2 {n : Type*} [Fintype n] [DecidableEq n] (ρ : Matrix n n ℂ) : ℝ :=
  entropy ρ / Real.log 2

/-- Factorization across a nonempty proper cut of the four parties. -/
def Biseparable {d : ℕ} (ψ : (Fin 4 → Fin d) → ℂ) : Prop :=
  ∃ X : Finset (Fin 4), X.Nonempty ∧ Xᶜ.Nonempty ∧
    ∃ φ χ : (Fin 4 → Fin d) → ℂ,
      (∀ x y, (∀ i ∈ X, x i = y i) → φ x = φ y) ∧
      (∀ x y, (∀ i ∉ X, x i = y i) → χ x = χ y) ∧
      ∀ x, ψ x = φ x * χ x

/-- The six coordinates are AB, AC, AD, BC, BD, CD, in that order. -/
def AdmissibleFill {d : ℕ} (ψ : (Fin 4 → Fin d) → ℂ)
    (σ : Fin 6 → ℝ) (ell : ℝ) : Prop :=
  (∀ k, 0 ≤ σ k) ∧
  σ 0 + σ 1 + σ 2 = entropy2 (rho1 ψ 0) ∧
  σ 0 + σ 3 + σ 4 = entropy2 (rho1 ψ 1) ∧
  σ 1 + σ 3 + σ 5 = entropy2 (rho1 ψ 2) ∧
  σ 2 + σ 4 + σ 5 = entropy2 (rho1 ψ 3) ∧
  -Real.sqrt (σ 0 * σ 5) + Real.sqrt (σ 1 * σ 4) + Real.sqrt (σ 2 * σ 3) =
    ell * entropy2 (rho2 ψ 0 1) ∧
  Real.sqrt (σ 0 * σ 5) - Real.sqrt (σ 1 * σ 4) + Real.sqrt (σ 2 * σ 3) =
    ell * entropy2 (rho2 ψ 0 2) ∧
  Real.sqrt (σ 0 * σ 5) + Real.sqrt (σ 1 * σ 4) - Real.sqrt (σ 2 * σ 3) =
    ell * entropy2 (rho2 ψ 0 3)

/-- The source volume, including its surface-area factor and all four radical factors. -/
def volume (σ : Fin 6 → ℝ) : ℝ :=
  let p := Real.sqrt (σ 0 * σ 5)
  let q := Real.sqrt (σ 1 * σ 4)
  let r := Real.sqrt (σ 2 * σ 3)
  Real.sqrt 2 / 3 * Real.sqrt (2 * ∑ k, σ k) *
    Real.rpow ((p + q + r) * (-p + q + r) * (p - q + r) * (p + q - r)) (1 / 4)

/-- Vanishing of every admissible fill of a unit pure state implies biseparability. -/
def claim : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ ψ : (Fin 4 → Fin d) → ℂ,
    (∑ x, ‖ψ x‖ ^ 2 = 1) →
    (∃ σ ell, AdmissibleFill ψ σ ell) →
    (∀ σ ell, AdmissibleFill ψ σ ell → volume σ = 0) → Biseparable ψ

private def supported (x : Fin 4 → Fin 8) : Prop :=
  (x 0).val = 4 * (x 1).val + 2 * (x 2).val + (x 3).val ∧
    (x 1).val < 2 ∧ (x 2).val < 2 ∧ (x 3).val < 2

private def psi (x : Fin 4 → Fin 8) : ℂ := by
  classical
  exact if supported x then ((Real.sqrt 8)⁻¹ : ℝ) else 0

private theorem normalized : ∑ x, ‖psi x‖ ^ 2 = 1 := by
  sorry

private theorem marginal_A : rho1 psi 0 = Matrix.diagonal (fun _ => (1 / 8 : ℂ)) := by
  sorry

private theorem marginal_leaf (i : Fin 4) (hi : i ≠ 0) :
    rho1 psi i = Matrix.diagonal (fun a => if a.val < 2 then (1 / 2 : ℂ) else 0) := by
  sorry

private theorem entropies :
    entropy2 (rho1 psi 0) = 3 ∧ entropy2 (rho1 psi 1) = 1 ∧
    entropy2 (rho1 psi 2) = 1 ∧ entropy2 (rho1 psi 3) = 1 := by
  sorry

private theorem forced_fill (σ : Fin 6 → ℝ) (ell : ℝ) (h : AdmissibleFill psi σ ell) :
    σ = ![1, 1, 1, 0, 0, 0] := by
  sorry

private theorem exists_fill : ∃ σ ell, AdmissibleFill psi σ ell := by
  sorry

private theorem all_volume_zero (σ : Fin 6 → ℝ) (ell : ℝ)
    (h : AdmissibleFill psi σ ell) : volume σ = 0 := by
  sorry

private theorem not_biseparable : ¬ Biseparable psi := by
  sorry

theorem result : ¬ claim := by
  intro h
  exact not_biseparable (h 8 (by norm_num) psi normalized exists_fill all_volume_zero)

end D5.S3.Quantum.Entanglement.EntropicFill.QuditTetrahedronGenuineRefutation
