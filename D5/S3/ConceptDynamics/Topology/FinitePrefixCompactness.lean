/- GID: D5/S3/ConceptDynamics/Topology/FinitePrefixCompactness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Topology/FinitePrefixCompactness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compactness turns finite prefixes into global paths. -/

import Mathlib.Topology.Compactness.Compact

open Set TopologicalSpace

namespace D5.S3.ConceptDynamics.Topology.FinitePrefixCompactness

universe u

variable {I : ℕ → Type u}
  [∀ n, TopologicalSpace (I n)]
  [∀ n, DiscreteTopology (I n)]
  [∀ n, Finite (I n)]

private def constraint (R : ∀ n, I n → I (n + 1) → Prop) (n : ℕ) :
    Set (∀ n, I n) := {x | R n (x n) (x (n + 1))}

private def prefixConstraint (R : ∀ n, I n → I (n + 1) → Prop) (N : ℕ) :
    Set (∀ n, I n) := ⋂ n ∈ Finset.range N, constraint R n

omit [∀ n, Finite (I n)] in
private theorem constraint_isClosed (R : ∀ n, I n → I (n + 1) → Prop) (n : ℕ) :
    IsClosed (constraint R n) := by
  let q : (∀ n, I n) → I n × I (n + 1) := fun x => (x n, x (n + 1))
  have hq : Continuous q := (continuous_apply n).prodMk (continuous_apply (n + 1))
  have hrel : IsClosed {p : I n × I (n + 1) | R n p.1 p.2} :=
    isClosed_discrete _
  exact hrel.preimage hq

private theorem prefixConstraint_isClosed (R : ∀ n, I n → I (n + 1) → Prop) (N : ℕ) :
    IsClosed (prefixConstraint R N) := by
  rw [prefixConstraint]
  exact isClosed_biInter fun n _ => constraint_isClosed R n

omit [∀ n, DiscreteTopology (I n)] [∀ n, Finite (I n)] in
private theorem prefixConstraint_nonempty
    (R : ∀ n, I n → I (n + 1) → Prop)
    (hfinite : ∀ N, ∃ x : ∀ n, I n, ∀ n, n < N → R n (x n) (x (n + 1)))
    (N : ℕ) :
    (prefixConstraint R N).Nonempty := by
  obtain ⟨x, hx⟩ := hfinite N
  refine ⟨x, ?_⟩
  rw [prefixConstraint]
  simp only [mem_iInter]
  intro n hn
  exact hx n (Finset.mem_range.mp hn)

omit [∀ n, TopologicalSpace (I n)] [∀ n, DiscreteTopology (I n)] [∀ n, Finite (I n)] in
private theorem prefixConstraint_anti (R : ∀ n, I n → I (n + 1) → Prop) :
    ∀ N, prefixConstraint R (N + 1) ⊆ prefixConstraint R N := by
  intro N x hx
  rw [prefixConstraint] at hx ⊢
  simp only [mem_iInter] at hx ⊢
  intro n hn
  exact hx n (Finset.mem_range.mpr
    (lt_trans (Finset.mem_range.mp hn) (Nat.lt_succ_self N)))

/-- Compactness upgrades realizability at every finite horizon to one infinite
compatible path.  Every coordinate alphabet may vary with the time index. -/
theorem exists_global_path_of_finite_prefixes
    (R : ∀ n, I n → I (n + 1) → Prop)
    (hfinite : ∀ N, ∃ x : ∀ n, I n, ∀ n, n < N → R n (x n) (x (n + 1))) :
    ∃ x : ∀ n, I n, ∀ n, R n (x n) (x (n + 1)) := by
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (prefixConstraint R)
      (prefixConstraint_anti R)
      (prefixConstraint_nonempty R hfinite)
      (by simpa [prefixConstraint] using
        (isCompact_univ : IsCompact (Set.univ : Set (∀ n, I n))))
      (prefixConstraint_isClosed R)
  refine ⟨x, ?_⟩
  intro n
  have hstage := mem_iInter.mp hx (n + 1)
  exact mem_iInter.mp (mem_iInter.mp hstage n)
    (Finset.mem_range.mpr (Nat.lt_succ_self n))

end D5.S3.ConceptDynamics.Topology.FinitePrefixCompactness
