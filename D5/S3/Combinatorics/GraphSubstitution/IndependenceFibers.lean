/- GID: D5/S3/Combinatorics/GraphSubstitution/IndependenceFibers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GraphSubstitution/IndependenceFibers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent sets in heterogeneous graph substitution are exactly independent supports with independent fibers. -/

import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GraphSubstitution.IndependenceFibers

universe u v

variable {V : Type u} {W : V → Type v}

/-- Replace each base vertex by its own graph, completely joining fibers over base edges. -/
def substitution (B : SimpleGraph V) (H : ∀ i, SimpleGraph (W i)) :
    SimpleGraph (Σ i, W i) where
  Adj x y := B.Adj x.1 y.1 ∨
    ∃ (i : V) (a b : W i), x = ⟨i, a⟩ ∧ y = ⟨i, b⟩ ∧ (H i).Adj a b
  symm := ⟨by
    rintro x y (h | ⟨i, a, b, hx, hy, hab⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨i, b, a, hy, hx, hab.symm⟩⟩
  loopless := ⟨by
    rintro x (h | ⟨i, a, b, ha, hb, hab⟩)
    · exact B.loopless.irrefl x.1 h
    · exact hab.ne (sigma_mk_injective (ha.symm.trans hb))⟩

/-- The occupied base vertices, with no finiteness or nonempty-fiber assumption. -/
def support (T : Set (Σ i, W i)) : Set V := Sigma.fst '' T

/-- The actual selected vertices within one fiber; an unoccupied fiber is empty. -/
def fiber (T : Set (Σ i, W i)) (i : V) : Set (W i) := (Sigma.mk i) ⁻¹' T

/-- Independence decomposes over the actual support and every actual fiber. -/
theorem isIndepSet_substitution_iff (B : SimpleGraph V)
    (H : ∀ i, SimpleGraph (W i)) (T : Set (Σ i, W i)) :
    (substitution B H).IsIndepSet T ↔
      B.IsIndepSet (support T) ∧ ∀ i, (H i).IsIndepSet (fiber T i) := by
  constructor
  · intro hT
    constructor
    · rintro i ⟨x, hx, rfl⟩ j ⟨y, hy, rfl⟩ hij hadj
      exact hT hx hy (fun hxy => hij (congrArg Sigma.fst hxy)) (Or.inl hadj)
    · intro i a ha b hb hab hadj
      have hne : (⟨i, a⟩ : Σ j, W j) ≠ ⟨i, b⟩ :=
        fun h => hab (sigma_mk_injective h)
      exact hT ha hb hne (Or.inr ⟨i, a, b, rfl, rfl, hadj⟩)
  · rintro ⟨hB, hH⟩ x hx y hy _ (hadj | ⟨i, a, b, hx', hy', hab⟩)
    · exact hB ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ hadj.ne hadj
    · subst x
      subst y
      exact hH i hx hy hab.ne hab

/-- The independence complex uses Mathlib's convention of nonempty finite faces. -/
def independenceComplex {A : Type*} (G : SimpleGraph A) : AbstractSimplicialComplex A where
  faces := {s | s.Nonempty ∧ G.IsIndepSet (s : Set A)}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro t hts ht
    exact ⟨ht, hs.2.mono (fun _ hx => hts hx)⟩
  singleton_mem a := by
    refine ⟨Finset.singleton_nonempty a, ?_⟩
    intro x hx y hy hxy
    exact (hxy ((Finset.mem_singleton.mp hx).trans
      (Finset.mem_singleton.mp hy).symm)).elim

end D5.S3.Combinatorics.GraphSubstitution.IndependenceFibers
