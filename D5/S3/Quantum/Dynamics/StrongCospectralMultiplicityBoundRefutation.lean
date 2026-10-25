/- GID: D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.claim; result=D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.result; claim=D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.claim
   digest: Two strongly cospectral vertices in K_{2,3} exceed the multiplicity bound. -/

import D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum

set_option autoImplicit false

open Matrix Finset
open D5.S3.Quantum.Dynamics.AverageMixingTraceMaximum (idempotent)

namespace D5.S3.Quantum.Dynamics.StrongCospectralMultiplicityBoundRefutation

/-- Strong cospectrality for the real symmetric adjacency matrix. -/
def StronglyCospectral {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : Prop :=
  ∀ θ : ℝ, ∃ c : ℝ, |c| = 1 ∧
    (idempotent G θ).mulVec (Pi.single u 1) =
      c • (idempotent G θ).mulVec (Pi.single v 1)

/-- The largest adjacency-eigenvalue multiplicity, as the supremum of eigenspace dimensions.
The dimensions are bounded by the number of vertices; non-eigenvalues contribute zero. -/
noncomputable def maxMultiplicity {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ :=
  sSup (Set.range fun θ : ℝ =>
    Module.finrank ℝ (Module.End.eigenspace (G.adjMatrix ℝ).mulVecLin θ))

/-- The proposed extension of the normal-Cayley-graph bound to connected simple graphs. -/
def claim : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.Connected →
    ∀ S : Finset (Fin n), (∀ u ∈ S, ∀ v ∈ S, StronglyCospectral G u v) →
      (S.card : ℝ) ≤ (n : ℝ) / (maxMultiplicity G : ℝ)

private def graph : SimpleGraph (Fin 5) where
  Adj u v := (u.val < 2) ≠ (v.val < 2)
  symm := by intro u v h; exact Ne.symm h
  loopless := by intro u h; exact h rfl

private instance graphDecidable : DecidableRel graph.Adj :=
  fun u v => inferInstanceAs (Decidable ((u.val < 2) ≠ (v.val < 2)))

private lemma graph_connected : graph.Connected := by
  sorry

private lemma multiplicity_lower : 3 ≤ maxMultiplicity graph := by
  sorry

private def polynomial : Matrix (Fin 5) (Fin 5) ℝ :=
  (1 / 3 : ℝ) • (graph.adjMatrix ℝ * graph.adjMatrix ℝ) - 1

private lemma polynomial_swap : polynomial *ᵥ Pi.single 0 1 = Pi.single 1 1 := by
  sorry

private lemma adjacency_cubic :
    graph.adjMatrix ℝ * graph.adjMatrix ℝ * graph.adjMatrix ℝ =
      (6 : ℝ) • graph.adjMatrix ℝ := by
  sorry

private lemma eigenvalue_support (θ : ℝ) (v : Fin 5 → ℝ) (hne : v ≠ 0)
    (hv : graph.adjMatrix ℝ *ᵥ v = θ • v) : θ = 0 ∨ θ ^ 2 = 6 := by
  sorry

private lemma polynomial_eigenvector (θ : ℝ) (v : Fin 5 → ℝ)
    (hv : graph.adjMatrix ℝ *ᵥ v = θ • v) :
    polynomial *ᵥ v = (θ ^ 2 / 3 - 1) • v := by
  sorry

private lemma projector_columns (θ : ℝ) :
    (idempotent graph θ).mulVec (Pi.single 1 1) =
      (θ ^ 2 / 3 - 1) • (idempotent graph θ).mulVec (Pi.single 0 1) := by
  sorry

private lemma strong_pair : StronglyCospectral graph 0 1 := by
  sorry

private lemma pairwise_witness :
    ∀ u ∈ ({0, 1} : Finset (Fin 5)), ∀ v ∈ ({0, 1} : Finset (Fin 5)),
      StronglyCospectral graph u v := by
  sorry

private lemma bound_contradiction (m : ℕ) (hm : 3 ≤ m) (h : (2 : ℝ) ≤ 5 / m) :
    False := by
  sorry

theorem result : ¬ claim := by
  intro h
  have hb := h 5 graph graph_connected {0, 1} pairwise_witness
  have hc : ({0, 1} : Finset (Fin 5)).card = 2 := by decide
  rw [hc] at hb
  exact bound_contradiction (maxMultiplicity graph) multiplicity_lower (by simpa using hb)

end D5.S3.Quantum.Dynamics.StrongCospectralMultiplicityBoundRefutation
