/- GID: D5/S3/Combinatorics/Graph/SubQuorum/HeawoodOrderTwoRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SubQuorum/HeawoodOrderTwoRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/SubQuorum/HeawoodOrderTwoRefutation.claim; result=D5/S3/Combinatorics/Graph/SubQuorum/HeawoodOrderTwoRefutation.result; claim=D5/S3/Combinatorics/Graph/SubQuorum/HeawoodOrderTwoRefutation.claim
   digest: The support conclusion for optimal representatives fails at projective plane order two. -/

import D5.S3.Combinatorics.Graph.SubQuorum.C4RepresentativeBounds

/-! The order-two example from the C4-free representative equality note in
subquorum-colorings, revision 48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.SubQuorum.HeawoodOrderTwoRefutation

open C4FreeRepresentatives

/-- The one-side support assertion with the order bound relaxed to two. -/
def claim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool),
    (∀ v w, G.Adj v w → color v ≠ color w) →
    NoFourCycle G.Adj → ∀ q : ℕ, 2 ≤ q →
    (∀ v, G.degree v = q + 1) →
    (∀ c, (Finset.univ.filter (fun v => color v = c)).card = q * q + q + 1) →
    ∀ (T : Finset V) (M : Finset (V × V)), Feasible G T M →
    T.card + M.card = q * q + q + 1 →
    ∃ c : Bool, (∀ v ∈ T, color v = c) ∧
      (∀ v, color v = c → v ∈ T ∪ endpoints M)

private def color (v : Fin 14) : Bool := decide (v.val < 7)

private def label (v : Fin 14) : ℕ := v.val % 7 + 1

private def dot (a b : ℕ) : ℕ :=
  ((a % 2) * (b % 2) + (a / 2 % 2) * (b / 2 % 2) + (a / 4) * (b / 4)) % 2

/-- Opposite copies of the nonzero binary labels are adjacent at zero dot product. -/
private def graph : SimpleGraph (Fin 14) where
  Adj v w := color v ≠ color w ∧ dot (label v) (label w) = 0
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

private instance : DecidableRel graph.Adj := fun v w =>
  inferInstanceAs (Decidable (color v ≠ color w ∧ dot (label v) (label w) = 0))

private def singletons : Finset (Fin 14) := {1, 2, 3, 11, 12, 13}
private def matching : Finset (Fin 14 × Fin 14) := {(0, 8)}

set_option maxRecDepth 8192 in
/-- The source's binary Heawood graph admits an optimal pair with both singleton colors. -/
theorem result : ¬ claim := by
  intro h
  have proper : ∀ v w, graph.Adj v w → color v ≠ color w := fun _ _ hadj => hadj.1
  have free : NoFourCycle graph.Adj := by
    have common : ∀ a b : Fin 14, a ≠ b →
        (Finset.univ.filter (fun v => graph.Adj a v ∧ graph.Adj b v)).card ≤ 1 := by
      decide +kernel
    intro a b x y hab hxy _ _ _ _ hax hay hbx hby
    exact hxy (Finset.card_le_one.mp (common a b hab) x
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hax, hbx⟩) y
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hay, hby⟩))
  have regular : ∀ v, graph.degree v = 3 := by
    simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
    decide +kernel
  have sides : ∀ c, (Finset.univ.filter (fun v => color v = c)).card = 7 := by
    decide +kernel
  have feasible : Feasible graph singletons matching := by
    constructor
    · decide +kernel
    · intro e he f hf hne
      simp [matching] at he hf
      exact (hne (he.trans hf.symm)).elim
    · decide +kernel
    · decide +kernel
  have optimum : Omega graph = 7 :=
    (threshold_parameters graph color proper free 3 7 (by decide) regular sides (by decide)).2.2
  have objective : singletons.card + matching.card = 7 :=
    Nat.le_antisymm ((objective_le_omega graph singletons matching feasible).trans (le_of_eq optimum))
      (by decide +kernel)
  obtain ⟨c, support, _⟩ := h (Fin 14) graph color proper free 2 (by decide)
    regular sides singletons matching feasible objective
  have same : color (1 : Fin 14) = color (11 : Fin 14) :=
    (support 1 (by decide +kernel)).trans (support 11 (by decide +kernel)).symm
  exact (by decide : color (1 : Fin 14) ≠ color (11 : Fin 14)) same

end D5.S3.Combinatorics.Graph.SubQuorum.HeawoodOrderTwoRefutation
