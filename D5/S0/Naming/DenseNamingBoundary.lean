/- GID: D5/S0/Naming/DenseNamingBoundary
   generality: G
   mirror-B: D5/B/S0/Naming/DenseNamingBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Separating discrete names force dense boundaries on locally connected-rich spaces. -/

import Mathlib.Topology.Connected.TotallyDisconnected

/- Library-search audit trail (2026-09-04):
   * Repository searches for dense naming boundaries, separating discrete readouts, and the
     generalized locally constant obstruction found no theorem with this conclusion.
   * Exact pinned-Mathlib hit `IsPreconnected.constant` states that a continuous map from a
     preconnected set to a discrete space is constant and is applied directly below.
   * Exact pinned-Mathlib hit `dense_iff_inter_open` reduces density to meeting every nonempty
     open set and is applied directly below.
   * The unrestricted source claim is false: the identity name separates the discrete two-point
     space while remaining continuous with empty stated boundary. The main theorem therefore
     assumes that every nonempty open set contains a nontrivial preconnected open subset; the
     counterexample is formalized after the theorem.
-/

namespace D5.S0.Naming.DenseNamingBoundary

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A space has enough nontrivial connected pieces for the naming-boundary argument when every
nonempty open set contains an open preconnected subset with two distinct points. -/
def HasNontrivialPreconnectedOpenPieces (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ U : Set X, IsOpen U → U.Nonempty →
    ∃ V : Set X, ∃ x y : X,
      V ⊆ U ∧ IsOpen V ∧ IsPreconnected V ∧ x ∈ V ∧ y ∈ V ∧ x ≠ y

/-- If a family of discrete-valued names separates points, and each name is continuous away from
its stated boundary, then the union of those boundaries is dense. The local connected-piece
hypothesis is the missing topological premise in the unrestricted source statement. -/
theorem dense_iUnion_namingBoundary
    {X : Type*} [TopologicalSpace X]
    {Name : ℕ → Type*} [∀ n, TopologicalSpace (Name n)] [∀ n, DiscreteTopology (Name n)]
    (names : (n : ℕ) → X → Name n) (boundary : ℕ → Set X)
    (hpieces : HasNontrivialPreconnectedOpenPieces X)
    (hcontinuous : ∀ n, ContinuousOn (names n) (boundary n)ᶜ)
    (hseparates : ∀ ⦃x y : X⦄, x ≠ y → ∃ n, names n x ≠ names n y) :
    Dense (⋃ n, boundary n) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨V, x, y, hVU, _hVOpen, hVPreconnected, hxV, hyV, hxy⟩ :=
    hpieces U hU hUne
  obtain ⟨n, hn⟩ := hseparates hxy
  by_contra hmeet
  have hUavoids : ∀ z ∈ U, z ∉ ⋃ k, boundary k := by
    intro z hzU hzBoundary
    exact hmeet ⟨z, hzU, hzBoundary⟩
  have hVsubset : V ⊆ (boundary n)ᶜ := by
    intro z hzV hzBoundary
    exact hUavoids z (hVU hzV) (Set.mem_iUnion.2 ⟨n, hzBoundary⟩)
  exact hn (hVPreconnected.constant ((hcontinuous n).mono hVsubset) hxV hyV)

/-- Without the local connected-piece premise, a separating family can have no boundary at all:
the identity name on discrete `Bool` is continuous everywhere. -/
theorem unrestricted_dense_boundary_fails :
    ∃ (names : ℕ → Bool → Bool) (boundary : ℕ → Set Bool),
      (∀ n, ContinuousOn (names n) (boundary n)ᶜ) ∧
        (∀ ⦃x y : Bool⦄, x ≠ y → ∃ n, names n x ≠ names n y) ∧
          ¬ Dense (⋃ n, boundary n) := by
  refine ⟨fun _ => id, fun _ => ∅, ?_, ?_, ?_⟩
  · intro n
    simpa using (continuous_id : Continuous (id : Bool → Bool)).continuousOn
  · intro x y hxy
    exact ⟨0, hxy⟩
  · rw [dense_iff_closure_eq]
    simp only [Set.iUnion_empty, closure_empty]
    intro hempty
    have : false ∈ (∅ : Set Bool) := by
      rw [hempty]
      trivial
    exact this

#print axioms dense_iUnion_namingBoundary
#print axioms unrestricted_dense_boundary_fails

end D5.S0.Naming.DenseNamingBoundary
