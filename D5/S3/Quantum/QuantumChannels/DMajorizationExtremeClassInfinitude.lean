/- GID: D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.claim; result=D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.result; claim=D5/S3/Quantum/QuantumChannels/DMajorizationExtremeClassInfinitude.claim
   digest: Infinitely many extreme classes for a two-dimensional D-majorization set. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.UnitaryGroup

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

namespace D5.S3.Quantum.QuantumChannels.DMajorizationExtremeClassInfinitude

/-- A source quantum channel is a completely positive, trace-preserving linear map. -/
def IsQuantumChannel {n : ℕ} (t : MatrixMap (Fin n) (Fin n) ℂ) : Prop :=
  t.IsCompletelyPositive ∧ ∀ x, (t x).trace = x.trace

/-- Matrix D-majorization by a channel fixing the positive diagonal matrix. -/
def DMajorizedBy {n : ℕ} (d : Fin n → ℝ) (x a : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ t : MatrixMap (Fin n) (Fin n) ℂ, IsQuantumChannel t ∧ t a = x ∧
    t (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (d i : ℂ))

/-- The set of matrices D-majorized by the specified initial matrix. -/
def majorizationSet {n : ℕ} (d : Fin n → ℝ) (a : Matrix (Fin n) (Fin n) ℂ) :
    Set (Matrix (Fin n) (Fin n) ℂ) := {x | DMajorizedBy d x a}

/-- Finiteness of the extreme classes under unitaries commuting with D. -/
def claim : Prop :=
  ∀ (n : ℕ) (d : Fin n → ℝ), (∀ i, 0 < d i) →
    ∀ a : Matrix (Fin n) (Fin n) ℂ,
      ∃ f : Finset (Matrix (Fin n) (Fin n) ℂ),
        ∀ x ∈ Set.extremePoints ℝ (majorizationSet d a),
          ∃ y ∈ f, ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ,
            u * diagonal (fun i => (d i : ℂ)) = diagonal (fun i => (d i : ℂ)) * u ∧
              x = u * y * star u

private def d : Fin 2 → ℝ := ![1 / 3, 2 / 3]
private def a : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, 0]
private def p (m : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(m : ℂ)^2 / ((m : ℂ)^2 + 1), (m : ℂ) / ((m : ℂ)^2 + 1);
     (m : ℂ) / ((m : ℂ)^2 + 1), 1 / ((m : ℂ)^2 + 1)]

private lemma pure_mem (m : ℕ) : p m ∈ majorizationSet d a := by
  sorry

private lemma density (x : Matrix (Fin 2) (Fin 2) ℂ)
    (hx : x ∈ majorizationSet d a) : x.PosSemidef ∧ x.trace = 1 := by
  sorry

private lemma pure_rigidity (m : ℕ) (x : Matrix (Fin 2) (Fin 2) ℂ)
    (hx : x.PosSemidef) (ht : x.trace = 1)
    (hk : x *ᵥ ![1, -(m : ℂ)] = 0) : x = p m := by
  sorry

private lemma pure_extreme (m : ℕ) :
    p m ∈ Set.extremePoints ℝ (majorizationSet d a) := by
  sorry

private lemma invariant (y : Matrix (Fin 2) (Fin 2) ℂ)
    (u : Matrix.unitaryGroup (Fin 2) ℂ)
    (hu : u * diagonal (fun i => (d i : ℂ)) = diagonal (fun i => (d i : ℂ)) * u) :
    (diagonal (fun i => (d i : ℂ)) * (u * y * star u)).trace =
      (diagonal (fun i => (d i : ℂ)) * y).trace := by
  sorry

private lemma invariant_injective :
    Function.Injective (fun m : ℕ => (diagonal (fun i => (d i : ℂ)) * p m).trace) := by
  sorry

/-- The two-dimensional counterexample has infinitely many extreme unitary classes. -/
theorem result : ¬ claim := by
  intro hc
  obtain ⟨f, hf⟩ := hc 2 d (by intro i; fin_cases i <;> norm_num [d]) a
  have hw (m : ℕ) := hf (p m) (pure_extreme m)
  choose y hy u hu he using hw
  have hi : Function.Injective y := by
    intro m k hmk
    apply invariant_injective
    rw [he m, he k, invariant (y m) (u m) (hu m), invariant (y k) (u k) (hu k), hmk]
  exact Set.infinite_univ.not_finite (f.finite_toSet.preimage hi.injOn |>.subset
    (by intro m _; exact hy m))

end D5.S3.Quantum.QuantumChannels.DMajorizationExtremeClassInfinitude
