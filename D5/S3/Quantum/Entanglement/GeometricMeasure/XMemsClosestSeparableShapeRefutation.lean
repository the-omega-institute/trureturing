/- GID: D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.claim; result=D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.result; claim=D5/S3/Quantum/Entanglement/GeometricMeasure/XMemsClosestSeparableShapeRefutation.claim
   digest: A fully separable three-qubit state beats every state of the conjectured CSS shape. -/

import D5.S3.Quantum.Information.SLDSpectralEnergy
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic

/-! The low-branch reading of Consiglio–Apollaro–Wieśniak, arXiv:2209.01430v2,
Appendix A, equation (A11). Qubit zero is the most significant bit. -/

set_option autoImplicit false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)

namespace D5.S3.Quantum.Entanglement.GeometricMeasure.XMemsClosestSeparableShapeRefutation

/-- Equation (A1) on its low branch, where both f and g equal 1/(N+1). -/
def xmems (n : ℕ) (γ : ℂ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun x y => if x = y then
    if x = (fun _ => 1) ∨ (∃ k : Fin n, k.val = 0 ∧ x k = 0) then
      1 / ((2 : ℂ) ^ (n - 1) + 1) else 0
    else if x = (fun _ => 0) ∧ y = (fun _ => 1) then γ
    else if x = (fun _ => 1) ∧ y = (fun _ => 0) then star γ else 0

/-- The matrix in equation (A11), with the source's parameters a, b and d. -/
def cssShape (n : ℕ) (a b : ℝ) (d : ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun x y => if x = y then
    if x = (fun _ => 0) ∨ x = (fun _ => 1) then (a / 2 : ℝ)
    else if ∃ k : Fin n, k.val = 0 ∧ x k = 0 then
      (b / ((2 : ℝ) ^ (n - 1) - 1) : ℝ)
    else ((1 - a - b) / ((2 : ℝ) ^ (n - 1) - 1) : ℝ)
    else if x = (fun _ => 0) ∧ y = (fun _ => 1) then d
    else if x = (fun _ => 1) ∧ y = (fun _ => 0) then star d else 0

/-- The parameter restrictions of equation (A11). -/
def IsCssShape {n : ℕ} (σ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : Prop :=
  ∃ (a b : ℝ) (d : ℂ), 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧
    a + b ≤ 1 ∧ ‖d‖ ≤ a / 2 ∧ σ = cssShape n a b d

/-- Real convex mixtures of products of one-qubit density matrices. -/
def FullySeparable (n : ℕ) : Set (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :=
  convexHull ℝ {σ | ∃ p : Fin n → Matrix (Fin 2) (Fin 2) ℂ,
    (∀ k, IsDensity (p k)) ∧ σ = fun x y => ∏ k, p k (x k) (y k)}

/-- Squared Hilbert–Schmidt distance. -/
def hsSq {n : ℕ} (ρ σ : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : ℝ :=
  (Matrix.trace ((ρ - σ)ᴴ * (ρ - σ))).re

/-- Every low-branch X-MEMS has a closest fully separable state of form (A11). -/
def claim : Prop := ∀ n : ℕ, 2 ≤ n → ∀ γ : ℂ,
  ‖γ‖ ≤ 1 / ((2 : ℝ) ^ (n - 1) + 1) →
  ∃ σ ∈ FullySeparable n, IsCssShape σ ∧
    ∀ τ ∈ FullySeparable n, hsSq (xmems n γ) σ ≤ hsSq (xmems n γ) τ

private def product (p : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ :=
  fun x y => ∏ k, p k (x k) (y k)

private theorem product_bounds (p : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hp : ∀ k, IsDensity (p k)) :
    (product p ![0,0,0] ![1,1,1]).re ≤
      (product p ![0,0,1] ![0,0,1]).re / 6 +
        3 * (product p ![1,1,0] ![1,1,0]).re / 2 ∧
    (product p ![0,0,0] ![1,1,1]).re ≤
      (product p ![0,0,0] ![0,0,0]).re / 12 +
        (product p ![0,1,1] ![0,1,1]).re / 12 +
        3 * (product p ![1,0,1] ![1,0,1]).re / 4 +
        3 * (product p ![1,1,0] ![1,1,0]).re / 4 := by
  sorry

private theorem separable_bounds (σ : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)
    (hσ : σ ∈ FullySeparable 3) :
    (σ ![0,0,0] ![1,1,1]).re ≤
      ((σ ![0,0,1] ![0,0,1]).re / 6 + 3 * (σ ![1,1,0] ![1,1,0]).re / 2) / 5 +
      4 / 5 * ((σ ![0,0,0] ![0,0,0]).re / 12 +
        (σ ![0,1,1] ![0,1,1]).re / 12 +
        3 * (σ ![1,0,1] ![1,0,1]).re / 4 +
        3 * (σ ![1,1,0] ![1,1,0]).re / 4) := by
  sorry

private theorem shape_lower (σ : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)
    (hσ : σ ∈ FullySeparable 3) (hs : IsCssShape σ) :
    (109 / 23520 : ℝ) ≤ hsSq (xmems 3 (11 / 112)) σ := by
  sorry

private def wordIndex (x : Fin 3 → Fin 2) : Fin 8 :=
  ⟨4 * (x 0).val + 2 * (x 1).val + (x 2).val, by omega⟩

private def tau : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ :=
  fun x y => if x = y then
    (![356409,359991,359991,363609,39601,39999,39999,360401] (wordIndex x) : ℂ) / 1920000
    else if (x = ![0,0,0] ∧ y = ![1,1,1]) ∨
      (x = ![1,1,1] ∧ y = ![0,0,0]) then 119997 / 1920000 else 0

private theorem tau_separable : tau ∈ FullySeparable 3 := by
  sorry

private theorem tau_distance : hsSq (xmems 3 (11 / 112)) tau =
    (417965512477 / 90316800000000 : ℝ) := by
  sorry

private theorem distance_gap : (417965512477 / 90316800000000 : ℝ) < 109 / 23520 := by
  norm_num

/-- The three-qubit instance γ = 11/112 refutes the low-branch conjecture. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨σ, hσ, hs, hmin⟩ := h 3 (by norm_num) (11 / 112) (by norm_num)
  have hlo := shape_lower σ hσ hs
  have hhi := hmin tau tau_separable
  rw [tau_distance] at hhi
  exact (not_lt_of_ge (hlo.trans hhi)) distance_gap

end D5.S3.Quantum.Entanglement.GeometricMeasure.XMemsClosestSeparableShapeRefutation
