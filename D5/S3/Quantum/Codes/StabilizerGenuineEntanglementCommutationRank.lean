/- GID: D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Genuine entanglement forces the Makuta--Kuzaka--Augusiak commutation-rank lower bound. -/

module

public import D5.S3.Quantum.Codes.QuditStabilizerProductVector
public import Mathlib.FieldTheory.ChevalleyWarning
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Tactic

public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Module
open D5.S3.Quantum.Codes.QuditStabilizerProductVector

namespace D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank

noncomputable section

def stabilizerSubspace {N p k : ℕ} [NeZero p]
    (G : Fin k → PauliWord N p) :
    Submodule ℂ ((Fin N → ZMod p) → ℂ) :=
  { carrier := {ψ | ∀ i, (pauliWordOperator (G i)).mulVec ψ = ψ}
    zero_mem' := by simp
    add_mem' := by intro ψ φ hψ hφ i; simpa [map_add, hψ i, hφ i]
    smul_mem' := by intro c ψ hψ i; simpa [map_smul, hψ i] }

def productAcross {N p : ℕ} (Q : Set (Fin N))
    (ψ : (Fin N → ZMod p) → ℂ) : Prop :=
  ∃ u : (Q → ZMod p) → ℂ, ∃ v : (Qᶜ → ZMod p) → ℂ,
    ∀ x, ψ x = u (fun q => x q.1) * v (fun q => x q.1)

def genuinelyEntangled {N p k : ℕ} [NeZero p]
    (G : Fin k → PauliWord N p) : Prop :=
  ∀ ψ, ψ ∈ stabilizerSubspace G → ψ ≠ 0 →
    ∀ Q : Set (Fin N), Q.Nonempty → Qᶜ.Nonempty → ¬ productAcross Q ψ

def commutationSpace {N p k : ℕ} [Fact p.Prime]
    (G : Fin k → PauliWord N p) :
    Submodule (ZMod p) (Fin N → ZMod p) :=
  Submodule.span (Set.range (fun ij : Fin k × Fin k =>
    commutationVector (G ij.1) (G ij.2)))

def generatedOperators {N p k : ℕ} [NeZero p]
    (G : Fin k → PauliWord N p) : Submonoid (Matrix (Fin N → ZMod p) (Fin N → ZMod p) ℂ) :=
  Submonoid.closure (Set.range (fun i => pauliWordOperator (G i)))

def IsStabilizer {N p k : ℕ} [NeZero p]
    (G : Fin k → PauliWord N p) : Prop :=
  (∀ i j, Commute (pauliWordOperator (G i)) (pauliWordOperator (G j))) ∧
    (∀ A ∈ generatedOperators G, ∀ c : ℂ,
      A = Matrix.scalar (Fin N → ZMod p) c → c = 1)

def claim : Prop :=
  ∀ (N p k : ℕ), 1 ≤ N → Nat.Prime p →
    ∀ G : Fin k → PauliWord N p,
      @IsStabilizer N p k ⟨Nat.Prime.ne_zero ‹Nat.Prime p›⟩ G →
      @genuinelyEntangled N p k ⟨Nat.Prime.ne_zero ‹Nat.Prime p›⟩ G →
      (N - 1 + (p - 2)) / (p - 1) ≤
        Module.finrank (ZMod p) (@commutationSpace N p k ⟨‹Nat.Prime p›⟩ G)

theorem result : claim := by
  sorry

end

end D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank

end
