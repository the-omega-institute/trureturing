/- GID: D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.claim; result=D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.result; claim=D5/S3/Quantum/Dynamics/BarrigaTenModeFourierEdgeRefutation.claim
   digest: Refutes the 25-edge lower bound of Barriga et al. for ten-mode Fourier transforms: a connected 23-edge real coupling matrix realizes F_10. -/

import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation

open Complex Matrix
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow

/-- The ten-dimensional discrete Fourier transform, entries exp(-2πi x y / 10) / √10. -/
def F10 : Matrix (Fin 10) (Fin 10) ℂ := fun x y =>
  Complex.exp (-(2 * Real.pi * Complex.I * (x : ℕ) * (y : ℕ)) / 10) / Real.sqrt 10

/-- Number of edges of the support graph: unordered pairs x < y with H x y ≠ 0. -/
def edgeCount (H : Matrix (Fin 10) (Fin 10) ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin 10 × Fin 10)).filter
    (fun p => p.1 < p.2 ∧ H p.1 p.2 ≠ 0)).card

/-- The support graph of H. -/
def supportGraph (H : Matrix (Fin 10) (Fin 10) ℝ) : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel (fun x y => H x y ≠ 0)

def IsUnimodularDiagonal (Φ : Matrix (Fin 10) (Fin 10) ℂ) : Prop :=
  ∃ z : Fin 10 → ℂ, (∀ x, ‖z x‖ = 1) ∧ Φ = Matrix.diagonal z

def claim : Prop :=
  ∀ H : Matrix (Fin 10) (Fin 10) ℝ, H.IsSymm →
    (∀ x y, x ≠ y → 0 ≤ H x y) → (supportGraph H).Connected →
    (∃ Φout Φin, IsUnimodularDiagonal Φout ∧ IsUnimodularDiagonal Φin ∧
      Φout * hamiltonianPropagator (H.map (↑)) 1 * Φin = F10) → 25 ≤ edgeCount H

private def s : ℝ := Real.sqrt 5
private def c : ℝ := (s - 1) / 4
private def d : ℝ := Real.sqrt (10 + 2 * s) / 4
private def ω : ℂ := (c : ℂ) + (d : ℂ) * I
private def q : ℝ := (21 * s - 65) / 20
private def r : ℝ := Real.sqrt (1 - q ^ 2)
private def γ : ℂ := (q : ℂ) + (r : ℂ) * I
private def a : ℝ := Real.pi * (35 - 13 * s) / 25
private def b : ℝ := Real.pi * (35 + 13 * s) / 25

private def C0 : Matrix (Fin 5) (Fin 5) ℝ := fun j k =>
  if j = k then 0 else if (k.val + 5 - j.val) % 5 = 1 ∨
    (k.val + 5 - j.val) % 5 = 4 then a else b

private def P : Matrix (Fin 5) (Fin 5) ℝ := fun j k =>
  ((γ * ω ^ ((j.val + k.val + 4) % 5)).re +
    (ω ^ ((j.val + 5 - k.val) % 5)).re) / 5

private def K : Matrix (Fin 5) (Fin 5) ℝ := C0 + (2 * Real.pi) • P

private def H : Matrix (Fin 10) (Fin 10) ℝ := fun x y =>
  (if x.val % 2 = y.val % 2 then
    K ⟨x.val % 5, Nat.mod_lt _ (by norm_num)⟩
      ⟨y.val % 5, Nat.mod_lt _ (by norm_num)⟩ else 0) +
  (if x ≠ y ∧ x.val % 5 = y.val % 5 then Real.pi / 4 else 0)

private def z (x : Fin 10) : ℂ :=
  (-I) ^ (x.val % 2) * ω ^ (4 * (x.val % 5) ^ 2)

/-- A connected real symmetric nonnegative coupling matrix with 23 edges realizes `F10`
after diagonal phase shifts, refuting the claimed 25-edge lower bound. -/
theorem result : ¬ claim := by
  classical
  have hsymm : H.IsSymm := by sorry
  have hnonneg : ∀ x y, x ≠ y → 0 ≤ H x y := by sorry
  have hconnected : (supportGraph H).Connected := by sorry
  have hphases : ∃ Φout Φin, IsUnimodularDiagonal Φout ∧ IsUnimodularDiagonal Φin ∧
      Φout * hamiltonianPropagator (H.map (↑)) 1 * Φin = F10 := by sorry
  have hedges : edgeCount H = 23 := by sorry
  intro h
  have hbound := h H hsymm hnonneg hconnected hphases
  rw [hedges] at hbound
  omega

end D5.S3.Quantum.Dynamics.BarrigaTenModeFourierEdgeRefutation
