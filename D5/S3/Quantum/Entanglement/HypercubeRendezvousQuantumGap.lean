/- GID: D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Balanced hypercube rendezvous has a dimension-independent quantum gap. -/
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
noncomputable section
open scoped BigOperators symmDiff ComplexOrder
namespace D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap
abbrev Vertex (d : ℕ) := Finset (Fin d)
abbrev Output (d t : ℕ) := {A : Vertex d // A.card = t}
abbrev Correlation (d t : ℕ) := Vertex d → Vertex d → Output d t → Output d t → ℝ
def Promised (d t : ℕ) (σ τ : Vertex d) : Prop := (σ ∆ τ).card = 2 * t
def Inputs (d t : ℕ) : Finset (Vertex d × Vertex d) := by
  classical
  exact Finset.univ.filter (fun p => Promised d t p.1 p.2)
def Wins {d t : ℕ} (σ τ : Vertex d) (A B : Output d t) : Prop :=
  Disjoint A.val B.val ∧ A.val ∪ B.val = σ ∆ τ
def value {d t : ℕ} (P : Correlation d t) : ℝ := by
  classical
  exact (∑ p ∈ Inputs d t, ∑ A, ∑ B, if Wins p.1 p.2 A B then P p.1 p.2 A B else 0) /
    ((Inputs d t).card : ℝ)
structure QStrategy (d t : ℕ) (α : Type*) (β : Type*)
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] where
  ρ : Matrix (α × β) (α × β) ℂ
  rho_psd : ρ.PosSemidef
  rho_trace : Matrix.trace ρ = 1
  E : Vertex d → Output d t → Matrix α α ℂ
  F : Vertex d → Output d t → Matrix β β ℂ
  E_psd : ∀ σ A, (E σ A).PosSemidef
  F_psd : ∀ τ B, (F τ B).PosSemidef
  E_sum : ∀ σ, (∑ A, E σ A) = 1
  F_sum : ∀ τ, (∑ B, F τ B) = 1
def QStrategy.prob {d t : ℕ} {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (S : QStrategy d t α β) : Correlation d t := fun σ τ A B =>
  (Matrix.trace (S.ρ * Matrix.kronecker (S.E σ A) (S.F τ B))).re
def IsQuantum {d t : ℕ} (P : Correlation d t) : Prop :=
  ∃ (α β : Type) (fα : Fintype α) (fβ : Fintype β)
      (dα : DecidableEq α) (dβ : DecidableEq β),
    letI : Fintype α := fα
    letI : Fintype β := fβ
    letI : DecidableEq α := dα
    letI : DecidableEq β := dβ
    ∃ S : QStrategy d t α β, S.prob = P
def IsNS {d t : ℕ} (P : Correlation d t) : Prop :=
  (∀ σ τ A B, 0 ≤ P σ τ A B) ∧ (∀ σ τ, (∑ A, ∑ B, P σ τ A B) = 1) ∧
  (∀ σ τ τ' A, (∑ B, P σ τ A B) = ∑ B, P σ τ' A B) ∧
  (∀ σ σ' τ B, (∑ A, P σ τ A B) = ∑ A, P σ' τ A B)
def QValues (d t : ℕ) : Set ℝ := {r | ∃ P : Correlation d t, IsQuantum P ∧ value P = r}
def NSValues (d t : ℕ) : Set ℝ := {r | ∃ P : Correlation d t, IsNS P ∧ value P = r}
def omegaQ (d t : ℕ) : ℝ := sSup (QValues d t)
def omegaNS (d t : ℕ) : ℝ := sSup (NSValues d t)
def claim : Prop := ∀ t d : ℕ, 2 ≤ t → 2 * t < d → omegaQ d t < omegaNS d t
private def n (d t : ℕ) : ℝ := (Nat.choose d t : ℝ)
private def kappa (d t : ℕ) : ℝ :=
  1 / ((n d t) ^ 4 * (4 * Real.sqrt 2 * (t : ℝ) + 2) ^ 2)
end D5.S3.Quantum.Entanglement.HypercubeRendezvousQuantumGap
