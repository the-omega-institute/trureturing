/- GID: D5/S1/Dynamics/Symbolic/FiniteGraphSpectralEntropy
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/FiniteGraphSpectralEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Regular finite graph walk growth is the degree power, exposing the matrix-to-dynamics bridge. -/

/-
This is the first algebraic bridge from finite graph languages to the entropy
calculation.  `FiniteGraphEntropy` supplies the compact shift space and the
prefix-growth theorem; this file records the independent growth calculation
for a regular graph.  The result is deliberately stated as a walk-mass
identity, so it remains useful when the native entropy endpoint is added.
-/

import D5.S1.Dynamics.Symbolic.FiniteGraphEntropy
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

noncomputable section

open Classical
open Finset
open scoped BigOperators Matrix

namespace D5.S1.Dynamics.Symbolic.FiniteGraphSpectralEntropy

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The total number of length-`n` walks, with endpoints summed. -/
def walkMass (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : ℕ :=
  ∑ u, ∑ v, (G.adjMatrix ℕ ^ n) u v

private def oneVec : V → ℕ := fun _ => 1

private theorem pow_mulVec_one (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : G.IsRegularOfDegree d) (n : ℕ) :
    (G.adjMatrix ℕ ^ n) *ᵥ oneVec = fun _ => d ^ n := by
  induction n with
  | zero =>
      funext v
      simp [oneVec]
  | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec]
      have hconst : G.adjMatrix ℕ *ᵥ oneVec = d • oneVec := by
        funext v
        simpa [oneVec] using
          (G.adjMatrix_mulVec_const_apply_of_regular (α := ℕ) (a := (1 : ℕ)) hreg (v := v))
      rw [hconst]
      rw [Matrix.mulVec_smul, ih]
      funext v
      simp [pow_succ, Nat.mul_comm]

/-- For a regular finite graph, the total number of length-`n` walks is
`|V| d^n`.  This is the finite combinatorial growth identity used by the
spectral-entropy bridge, and is independent of irreducibility. -/
theorem walkMass_eq_card_mul_pow (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hreg : G.IsRegularOfDegree d) (n : ℕ) :
    walkMass G n = Fintype.card V * d ^ n := by
  have hpow := pow_mulVec_one G hreg n
  simp only [walkMass, Matrix.mulVec, oneVec] at hpow ⊢
  calc
    ∑ x, ∑ x_1, (G.adjMatrix ℕ ^ n) x x_1 =
        ∑ x, ((G.adjMatrix ℕ ^ n) *ᵥ oneVec) x := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [Matrix.mulVec, dotProduct, oneVec]
    _ = ∑ _ : V, d ^ n := by rw [hpow]
    _ = Fintype.card V * d ^ n := by simp

/-- The same mass is the sum of the cardinalities of the finite walk fibres.
This names the combinatorial interpretation supplied by Mathlib's adjacency
matrix theorem and is the interface consumed by later entropy arguments. -/
theorem walkMass_eq_sum_walk_cards (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :
    walkMass G n =
      ∑ u, ∑ v, Fintype.card {p : G.Walk u v | p.length = n} := by
  simp only [walkMass]
  simp_rw [G.adjMatrix_pow_apply_eq_card_walk]
  norm_cast

end D5.S1.Dynamics.Symbolic.FiniteGraphSpectralEntropy
