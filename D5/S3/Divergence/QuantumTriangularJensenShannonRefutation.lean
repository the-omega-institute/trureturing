/- GID: D5/S3/Divergence/QuantumTriangularJensenShannonRefutation
   generality: I
   mirror-B: D5/B/S3/Divergence/QuantumTriangularJensenShannonRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.claim; result=D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.result; claim=D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.claim
   digest: A full-rank commuting qubit pair has QTD squared strictly greater than QJS2. -/

/- escape_witness: diag(255/256,1/256) and diag(1/256,255/256), a full-rank
   qubit pair with QTD² − QJS₂ ≥ 97793/268435456.
   Direct frozen dependencies: none (pinned Mathlib only).
   admission_basis: open-problem-resolution (#15986; Refuted)
   Per-declaration proof_shape and live consumers:
     IsState: definition; consumers=claim, state_pair
     vonNeumann2: definition; consumers=QJS2, entropy_diagonal
     QJS2: definition; consumers=claim, js_bound
     QTD: definition; consumers=claim, td_value
     claim: definition; consumer=result
     diagonalHom: definition; consumer=cfc_diagonal
     cfc_diagonal: bind-only; consumers=entropy_diagonal, td_value
     rho, sigma: definition; consumers=state_pair, pair_sum, td_value, js_bound, result
     state_pair: bind-only; consumer=result
     pair_sum: bind-only; consumers=td_value, js_bound
     entropy_diagonal: bind-only; consumer=js_bound
     log_small, log_half: bind-only; consumer=js_bound
     td_value, js_bound: bind-only; consumer=result
     result: bind-only; explicit external open-problem refutation. -/

import D5.S3.Divergence.CoherenceL1RelativeEntropyBound
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
open Matrix
open scoped ComplexOrder
namespace D5.S3.Divergence.QuantumTriangularJensenShannonRefutation

open D5.S3.Divergence.CoherenceL1RelativeEntropyBound (IsState vonNeumann2)

/-- Definition 2.10 with base-2 logarithms. -/
noncomputable def QJS2 {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  vonNeumann2 ((1/2 : ℂ) • (ρ + σ)) - (vonNeumann2 ρ + vonNeumann2 σ) / 2
/-- Definition 3.1 (the inverse square root acts on the support: `0 ^ (-1/2) = 0`). -/
noncomputable def QTD {n : ℕ} (ρ σ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (1/2 : ℝ) * (Matrix.trace ((ρ - σ) * cfc (fun x : ℝ => x ^ (-(1/2 : ℝ))) (ρ + σ) *
    (ρ - σ) * cfc (fun x : ℝ => x ^ (-(1/2 : ℝ))) (ρ + σ))).re
/-- The lower half of the bound proposed in §1.3. -/
def claim : Prop :=
  ∀ (n : ℕ) (ρ σ : Matrix (Fin n) (Fin n) ℂ), IsState ρ → IsState σ → QTD ρ σ ^ 2 ≤ QJS2 ρ σ

private def diagonalHom {n : ℕ} : (Fin n → ℂ) →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toAlgHom := Matrix.diagonalAlgHom ℂ
  map_star' a := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [Matrix.star_apply]
    · simp [Matrix.star_apply, hij, Ne.symm hij]

private lemma cfc_diagonal {n : ℕ} (d : Fin n → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (f (d i) : ℂ)) := by
  letI : ContinuousFunctionalCalculus ℝ (Fin n → ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  let z : Fin n → ℂ := fun i => (d i : ℂ)
  have hd : IsSelfAdjoint z := by ext i; simp [z, Pi.star_apply]
  have hf : ContinuousOn f (spectrum ℝ z) := by
    rw [Pi.spectrum_eq]
    apply Set.Finite.continuousOn
    exact Set.finite_iUnion fun i => (Set.finite_singleton (d i)).subset
      (CFC.spectrum_algebraMap_subset (A := ℂ) (d i))
  have hh := diagonalHom.map_cfc (R := ℝ) f z hf
    diagonalHom.toLinearMap.continuous_of_finiteDimensional hd (hd.map diagonalHom)
  change cfc f (diagonalHom z) = _
  rw [← hh, cfc_map_pi (S := ℂ) f z (by rwa [Pi.spectrum_eq] at hf) hd
    (fun i => by change star (d i : ℂ) = (d i : ℂ); simp)]
  change diagonal (fun i => cfc f (z i)) = diagonal (fun i => (f (d i) : ℂ))
  congr 1
  funext i
  simpa [z] using (cfc_algebraMap (R := ℝ) (A := ℂ) (d i) f)

private def rho : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![255/256, 1/256]
private def sigma : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1/256, 255/256]

private lemma state_pair : IsState rho ∧ IsState sigma := by
  constructor <;> constructor
  · apply Matrix.PosSemidef.diagonal
    intro i; fin_cases i <;> norm_num [rho, Complex.nonneg_iff]
  · norm_num [rho, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  · apply Matrix.PosSemidef.diagonal
    intro i; fin_cases i <;> norm_num [sigma, Complex.nonneg_iff]
  · norm_num [sigma, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

private lemma pair_sum : rho + sigma = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [rho, sigma, Matrix.diagonal]

private lemma entropy_diagonal (a b : ℝ) :
    vonNeumann2 (diagonal ![(a : ℂ), (b : ℂ)]) =
      -(a * Real.logb 2 a + b * Real.logb 2 b) := by
  have hd : ![(a : ℂ), (b : ℂ)] = fun i : Fin 2 => (![a, b] i : ℂ) := by
    funext i; fin_cases i <;> rfl
  rw [vonNeumann2, hd, cfc_diagonal]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

private lemma log_small : Real.logb 2 (1/256) = -8 := by
  have h : (1/256 : ℝ) = (2 ^ 8)⁻¹ := by norm_num
  rw [h, Real.logb_inv, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num

private lemma log_half : Real.logb 2 (1/2) = -1 := by
  rw [one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]

private lemma td_value : QTD rho sigma = (127/128 : ℝ)^2 := by
  have hc : cfc (fun x : ℝ => x ^ (-(1/2 : ℝ))) (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    have hi : (1 : Matrix (Fin 2) (Fin 2) ℂ) = diagonal (fun _ => ((1 : ℝ) : ℂ)) := by simp
    rw [hi, cfc_diagonal]
    simp
  rw [QTD, pair_sum, hc]
  norm_num [rho, sigma, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.diagonal]

private lemma js_bound : QJS2 rho sigma ≤ (31/32 : ℝ) := by
  have hm : (1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      diagonal ![((1/2 : ℝ) : ℂ), ((1/2 : ℝ) : ℂ)] := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]
  have hr : rho = diagonal ![((255/256 : ℝ) : ℂ), ((1/256 : ℝ) : ℂ)] := by
    norm_num [rho]
  have hs : sigma = diagonal ![((1/256 : ℝ) : ℂ), ((255/256 : ℝ) : ℂ)] := by
    norm_num [sigma]
  rw [QJS2, pair_sum, hm, hr, hs, entropy_diagonal, entropy_diagonal,
    entropy_diagonal, log_half, log_small]
  have hn := Real.logb_neg (b := (2 : ℝ)) (x := (255/256 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  linarith

theorem result : ¬ claim := by
  intro h
  have hb := h 2 rho sigma state_pair.1 state_pair.2
  rw [td_value] at hb
  have hn : (31/32 : ℝ) < ((127/128 : ℝ)^2)^2 := by norm_num
  exact (not_lt_of_ge (hb.trans js_bound)) hn

end D5.S3.Divergence.QuantumTriangularJensenShannonRefutation
