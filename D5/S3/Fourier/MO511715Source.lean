/- GID: D5/S3/Fourier/MO511715Source
   generality: I
   mirror-B: D5/B/S3/Fourier/MO511715Source
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Euclidean five-dimensional cutoff series and its original nested time integral. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Set
open scoped BigOperators

namespace D5.S3.Fourier.MO511715Source

noncomputable section

abbrev Lattice := Fin 5 → ℤ
abbrev Space := EuclideanSpace ℝ (Fin 5)

/-- Coordinate casting into Euclidean space, rather than the supremum-norm function space. -/
def embed (k : Lattice) : Space := WithLp.toLp 2 (fun i => (k i : ℝ))

def length (k : Lattice) : ℝ := ‖embed k‖

def frequency (k : Lattice) : ℝ := ‖(2 * Real.pi) • embed k‖

def LegalMask (ψ : Lattice → Lattice → ℝ) : Prop :=
  (∀ k l, 0 ≤ ψ k l ∧ ψ k l ≤ 1) ∧
  ∀ k l, ψ k l ≠ 0 → (9 / 64 : ℝ) * length k ≤ length l ∧
    length l ≤ (64 / 9 : ℝ) * length k

/-- The original full square is written as two independent interval integrals. -/
def timeIntegral (q L A B : ℝ) : ℝ :=
  ∫ α in (0 : ℝ)..q, Real.exp (-L * (q - α)) *
    ∫ v₁ in (0 : ℝ)..α, ∫ v₂ in (0 : ℝ)..α,
      Real.exp (-A * (q + α - 2 * v₁) - B * (q + α - 2 * v₂))

def kernel (ψ : Lattice → Lattice → ℝ) (q : ℝ) (n m₁ m₂ : Lattice) : ℝ :=
  frequency (n - m₁) ^ 2 * ψ (n - m₁) m₁ *
    timeIntegral q (frequency (n - m₁) ^ 4)
      (frequency (m₁ - m₂) ^ 4) (frequency m₂ ^ 4)

def cutoffWeight {F : Type*} [NormedAddCommGroup F] (ζ : Space → F)
    (ε : ℝ) (m₁ m₂ : Lattice) : ℝ :=
  ‖ζ (ε • embed (m₁ - m₂))‖ ^ 2 * ‖ζ (ε • embed m₂)‖ ^ 2

/-- Summation over all ordered pairs, with no removed zero modes. -/
def phi {F : Type*} [NormedAddCommGroup F] (ζ : Space → F)
    (ψ : Lattice → Lattice → ℝ) (ε q : ℝ) (n : Lattice) : ℝ :=
  ∑' m : Lattice × Lattice, kernel ψ q n m.1 m.2 * cutoffWeight ζ ε m.1 m.2

def delta {F : Type*} [NormedAddCommGroup F] (ζ : Space → F)
    (ψ : Lattice → Lattice → ℝ) (ε r : ℝ) (u : Lattice) : ℝ :=
  phi ζ ψ ε r u - phi ζ ψ ε r 0

def SmoothCutoff {F : Type*} [RCLike F] (ζ : Space → F) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧ ζ 0 = 1

def UniformEstimate {F : Type*} [RCLike F] (ζ : Space → F) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ ψ : Lattice → Lattice → ℝ, LegalMask ψ →
    ∀ r : ℝ, 0 ≤ r → ∀ u : Lattice, ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ →
      |delta ζ ψ ε₂ r u - delta ζ ψ ε₁ r u| ≤ C * |ε₂ - ε₁| ^ δ

/-- Both conventional scalar readings, with constants chosen after the fixed cutoff. -/
def claim : Prop :=
  (∀ ζ : Space → ℝ, SmoothCutoff ζ → UniformEstimate ζ) ∧
  (∀ ζ : Space → ℂ, SmoothCutoff ζ → UniformEstimate ζ)

def firstUnit : Lattice := fun i => if i = 0 then 1 else 0

/-- One mask, independent of the scales and the cutoff. -/
def selectedMask (k l : Lattice) : ℝ :=
  if k + l = firstUnit ∧ (9 / 64 : ℝ) * length k ≤ length l ∧
      length l ≤ (64 / 9 : ℝ) * length k then 1 else 0

/-- The exact change from difference variables to the original ordered indices. -/
def indexEquiv : (Lattice × Lattice) ≃ (Lattice × Lattice) where
  toFun p := (p.1 + p.2, p.2)
  invFun p := (p.1 - p.2, p.2)
  left_inv p := by ext i <;> simp
  right_inv p := by ext i <;> simp

private lemma inner_factor (q A B α : ℝ) :
    (∫ v₁ in (0 : ℝ)..α, ∫ v₂ in (0 : ℝ)..α,
      Real.exp (-A * (q + α - 2 * v₁) - B * (q + α - 2 * v₂))) =
    Real.exp (-(A + B) * (q + α)) *
      (∫ v in (0 : ℝ)..α, Real.exp (2 * A * v)) *
      (∫ v in (0 : ℝ)..α, Real.exp (2 * B * v)) := by
  have he (v w : ℝ) :
      Real.exp (-A * (q + α - 2 * v) - B * (q + α - 2 * w)) =
      Real.exp (-(A + B) * (q + α)) * Real.exp (2 * A * v) *
        Real.exp (2 * B * w) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp_rw [he, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]

private lemma inner_continuous (q A B : ℝ) : Continuous (fun α : ℝ =>
    ∫ v₁ in (0 : ℝ)..α, ∫ v₂ in (0 : ℝ)..α,
      Real.exp (-A * (q + α - 2 * v₁) - B * (q + α - 2 * v₂))) := by
  simp_rw [inner_factor]
  have hc (D : ℝ) : Continuous (fun v : ℝ => Real.exp (2 * D * v)) := by fun_prop
  exact ((by fun_prop : Continuous (fun α : ℝ => Real.exp (-(A + B) * (q + α)))).mul
    (intervalIntegral.continuous_primitive (fun a b => (hc A).intervalIntegrable a b) 0)).mul
      (intervalIntegral.continuous_primitive (fun a b => (hc B).intervalIntegrable a b) 0)

private lemma outer_continuous (q L A B : ℝ) : Continuous (fun α : ℝ =>
    Real.exp (-L * (q - α)) *
      ∫ v₁ in (0 : ℝ)..α, ∫ v₂ in (0 : ℝ)..α,
        Real.exp (-A * (q + α - 2 * v₁) - B * (q + α - 2 * v₂))) :=
  (by fun_prop : Continuous (fun α : ℝ => Real.exp (-L * (q - α)))).mul
    (inner_continuous q A B)

private lemma inner_nonneg (q A B α : ℝ) (hα : 0 ≤ α) :
    0 ≤ ∫ v₁ in (0 : ℝ)..α, ∫ v₂ in (0 : ℝ)..α,
      Real.exp (-A * (q + α - 2 * v₁) - B * (q + α - 2 * v₂)) := by
  apply intervalIntegral.integral_nonneg hα
  intro v hv
  exact intervalIntegral.integral_nonneg_of_forall hα (fun w => (Real.exp_pos _).le)

private lemma timeIntegral_nonneg (q L A B : ℝ) (hq : 0 ≤ q) :
    0 ≤ timeIntegral q L A B := by
  apply intervalIntegral.integral_nonneg hq
  intro α hα
  exact mul_nonneg (Real.exp_pos _).le (inner_nonneg q A B α hα.1)

end
end D5.S3.Fourier.MO511715Source
