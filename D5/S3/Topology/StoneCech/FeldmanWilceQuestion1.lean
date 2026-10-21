/- GID: D5/S3/Topology/StoneCech/FeldmanWilceQuestion1
   generality: I
   mirror-B: D5/B/S3/Topology/StoneCech/FeldmanWilceQuestion1
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite-block map instantiates the closed fibre graph construction.
-/

import D5.S3.Topology.StoneCech.SectionClosedGraph

/-!
# Feldman–Wilce Question 1: the finite-block instance

The source problem asks for a countably compact Hausdorff (or `T₁`) space
with a closed orthogonality relation whose cliques are finite but have no
uniform finite bound.  The map below labels the block containing a point;
its fibres have sizes `n + 1`.  The generic Stone–Cech selector theorem then
supplies the required actual space and relation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Function Topology Cardinal
open D5.S3.Topology.StoneCech.SectionGoodFreshClusters
open D5.S3.Topology.StoneCech.SectionClosedGraph

namespace D5.S3.Topology.StoneCech.FeldmanWilceQuestion1

/- The countable disjoint union of finite blocks of sizes `n + 1`. -/
abbrev Block := Σ n : ℕ, Fin (n + 1)

def blockIndex : Block → ℕ := Sigma.fst

private theorem block_embedding (b : ℕ) : Function.Injective
    (fun i : Fin (b + 1) => (⟨b, i⟩ : Block)) := by
  intro i j h
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

private theorem block_finite (b : ℕ) :
    (blockIndex ⁻¹' ({b} : Set ℕ)).Finite := by
  let e : Fin (b + 1) → Block := fun i => ⟨b, i⟩
  apply (Set.finite_range e).subset
  rintro ⟨n, i⟩ hi
  have hn : n = b := by
    change blockIndex (⟨n, i⟩ : Block) ∈ ({b} : Set ℕ) at hi
    simpa [blockIndex] using (mem_singleton_iff.mp hi)
  subst n
  exact ⟨i, rfl⟩

private theorem block_unbounded (n : ℕ) :
    ∃ b : ℕ, n ≤ (blockIndex ⁻¹' ({b} : Set ℕ)).ncard := by
  let e : Fin (n + 1) → Block := fun i => ⟨n, i⟩
  have he : Function.Injective e := block_embedding n
  have hrange : Set.range e ⊆ blockIndex ⁻¹' ({n} : Set ℕ) := by
    rintro _ ⟨i, rfl⟩
    simp [e, blockIndex]
  have hcard : (Set.range e).ncard = n + 1 := by
    rw [Set.ncard_range_of_injective he, Nat.card_eq_fintype_card]
    simp
  refine ⟨n, ?_⟩
  calc
    n ≤ n + 1 := Nat.le_succ n
    _ = (Set.range e).ncard := hcard.symm
    _ ≤ (blockIndex ⁻¹' ({n} : Set ℕ)).ncard :=
      Set.ncard_le_ncard hrange (block_finite n)

/-- A direct witness package for the open problem's requested space/relation. -/
def Q1Witness (Y : Set (Ultrafilter Block)) : Prop :=
  CountablyCompactSpace (principalExtension Y) ∧
    T2Space (principalExtension Y) ∧
    T1Space (principalExtension Y) ∧
    IsClosed {p : principalExtension Y × principalExtension Y |
      (fibreGraph blockIndex Y).Adj p.1 p.2} ∧
    (∀ K : Set (principalExtension Y),
      (fibreGraph blockIndex Y).IsClique K → K.Finite) ∧
    (∀ n : ℕ, ∃ K : Set (principalExtension Y),
      K.Finite ∧ (fibreGraph blockIndex Y).IsClique K ∧ K.ncard = n) ∧
    ¬ ∃ bound : ℕ, ∀ K : Set (principalExtension Y),
      (fibreGraph blockIndex Y).IsClique K → K.ncard ≤ bound

/--
The finite-block instance resolves Feldman–Wilce Question 1 at the level of
the stated topological relation: the relation is closed in the full product,
all cliques are finite, and every finite clique size occurs.  `fibreGraph` is
an actual `SimpleGraph`, so symmetry and irreflexivity are structural fields;
the displayed `IsClosed` predicate is in the entire product, including the
diagonal.  The inherited `T2Space` instance supplies `T1Space` as well.
-/
theorem result :
    ∃ Y : Set (Ultrafilter Block), Q1Witness Y := by
  letI : Countable Block := by infer_instance
  obtain ⟨Y, _, _, _, _, _, hcompact, hclosed, hfinite,
      hunbounded⟩ :=
    exists_countablyCompact_closed_fibreGraph blockIndex block_finite block_unbounded
  refine ⟨Y, ?_⟩
  refine ⟨hcompact, ?_, ?_, hclosed, hfinite, hunbounded, ?_⟩
  · infer_instance
  · infer_instance
  · rintro ⟨bound, hbound⟩
    obtain ⟨K, _, hK, hcard⟩ := hunbounded (bound + 1)
    have h := hbound K hK
    rw [hcard] at h
    exact Nat.not_succ_le_self bound h

end D5.S3.Topology.StoneCech.FeldmanWilceQuestion1
