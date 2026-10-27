/- GID: D5/S3/Geometry/OccupiedFiberSubstitution
   generality: G
   mirror-B: D5/B/S3/Geometry/OccupiedFiberSubstitution
   mirror-E: none(waiver:occupied-fiber-substitution)
   anchors: [D5/S3/Geometry/FiniteGraphVertexSubstitution]
   utility: none
   digest: Every induced heterogeneous substitution is the substitution on its occupied base and selected fibers, also at the level of independence realizations. -/
import D5.S3.Geometry.FiniteGraphVertexSubstitution

/-!
The occupied base records exactly the fibers meeting the selected vertex set.
This is a local transport for the hereditary induction associated with Carnero
Bravo, arXiv:2505.06457v2, Question 22, and does not settle that question.
-/

noncomputable section
open Set

namespace D5.S3.Geometry.OccupiedFiberSubstitution
open FiniteGraphVertexSubstitution FiniteConeCollapse FiniteSimplicialJoin

universe u w
variable {V : Type u} {D : V → Type w}

/-- Base vertices whose fiber meets the arbitrary selected vertex set. -/
def occupiedBase (T : Set (Sigma D)) : Set V := {v | ∃ d, Sigma.mk v d ∈ T}

/-- The actual selected vertices in an occupied fiber. -/
abbrev selectedFiber (T : Set (Sigma D)) (v : occupiedBase T) :=
  {d : D v.val // Sigma.mk v.val d ∈ T}

/-- Occupancy supplies a selected vertex without assuming the whole set nonempty. -/
instance selectedFiberNonempty (T : Set (Sigma D)) (v : occupiedBase T) :
    Nonempty (selectedFiber T v) :=
  v.property.elim fun d hd => ⟨⟨d, hd⟩⟩

/-- Split a selected dependent pair into its occupied base and selected fiber. -/
def vertexEquiv (T : Set (Sigma D)) : T ≃ Sigma (selectedFiber T) where
  toFun x := ⟨⟨x.val.1, ⟨x.val.2, x.property⟩⟩, ⟨x.val.2, x.property⟩⟩
  invFun x := ⟨⟨x.1.val, x.2.val⟩, x.2.property⟩
  left_inv x := by cases x; rfl
  right_inv x := by rcases x with ⟨⟨v, hv⟩, ⟨d, hd⟩⟩; rfl

/-- Substitute the induced selected fiber graphs over the induced occupied base. -/
def selectedGraph (G : SimpleGraph V) (H : ∀ v, SimpleGraph (D v))
    (T : Set (Sigma D)) : SimpleGraph (Sigma (selectedFiber T)) :=
  substitution (G.induce (occupiedBase T))
    (fun v => (H v.val).induce {d | Sigma.mk v.val d ∈ T})

/-- The explicit vertex splitting preserves and reflects actual adjacency. -/
theorem adjacency_iff (G : SimpleGraph V) (H : ∀ v, SimpleGraph (D v))
    (T : Set (Sigma D)) (x y : T) :
    ((substitution G H).induce T).Adj x y ↔
      (selectedGraph G H T).Adj (vertexEquiv T x) (vertexEquiv T y) := by
  rcases x with ⟨⟨v, a⟩, ha⟩
  rcases y with ⟨⟨z, b⟩, hb⟩
  change (G.Adj v z ∨ ∃ i c d, (Sigma.mk v a) = ⟨i, c⟩ ∧
    (Sigma.mk z b) = ⟨i, d⟩ ∧ (H i).Adj c d) ↔ _
  constructor
  · rintro (h | ⟨i, c, d, hx, hy, hcd⟩)
    · exact Or.inl h
    · cases hx
      cases hy
      exact Or.inr ⟨⟨v, ⟨a, ha⟩⟩, ⟨a, ha⟩, ⟨b, hb⟩, rfl, rfl, hcd⟩
  · rintro (h | ⟨i, c, d, hx, hy, hcd⟩)
    · exact Or.inl h
    · right
      refine ⟨i.val, c.val, d.val, ?_, ?_, hcd⟩
      · exact congrArg (fun q : Sigma (selectedFiber T) => Sigma.mk q.1.val q.2.val) hx
      · exact congrArg (fun q : Sigma (selectedFiber T) => Sigma.mk q.1.val q.2.val) hy

/-- The induced graph is genuinely isomorphic to the occupied-fiber substitution. -/
def graphIso (G : SimpleGraph V) (H : ∀ v, SimpleGraph (D v))
    (T : Set (Sigma D)) : (substitution G H).induce T ≃g selectedGraph G H T where
  toEquiv := vertexEquiv T
  map_rel_iff' := (adjacency_iff G H T _ _).symm

section Finite
variable [Fintype V] [DecidableEq V] [∀ v, Fintype (D v)] [∀ v, DecidableEq (D v)]
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Independent faces map exactly to independent faces of the selected graph. -/
theorem mapped_independence_faces (G : SimpleGraph V) (H : ∀ v, SimpleGraph (D v))
    (T : Set (Sigma D)) :
    ((independenceComplex ((substitution G H).induce T)).toPreAbstractSimplicialComplex).map
      (graphIso G H T).toEquiv.toEmbedding =
      (independenceComplex (selectedGraph G H T)).toPreAbstractSimplicialComplex := by
  classical
  let e := graphIso G H T
  ext s
  change (∃ t : Finset T, (t.Nonempty ∧
    ((substitution G H).induce T).IsIndepSet (t : Set T)) ∧ t.image e = s) ↔
      s.Nonempty ∧ (selectedGraph G H T).IsIndepSet (s : Set (Sigma (selectedFiber T)))
  constructor
  · rintro ⟨t, ⟨hn, hi⟩, rfl⟩
    refine ⟨hn.image _, ?_⟩
    intro x hx y hy hxy hadj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hi ha hb (fun h => hxy (congrArg e h)) (e.map_adj_iff.mp hadj)
  · rintro ⟨hn, hi⟩
    refine ⟨s.image e.symm, ⟨hn.image _, ?_⟩, ?_⟩
    · intro x hx y hy hxy hadj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      apply hi ha hb (fun h => hxy (congrArg e.symm h))
      simpa only [e.apply_symm_apply] using (e.map_adj_iff.mpr hadj)
    · ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
        simpa only [e.apply_symm_apply] using hb
      · intro hx
        exact ⟨e.symm x, ⟨x, hx, rfl⟩, e.apply_symm_apply x⟩

/-- Exact native realization transport for every induced subset, including the empty set. -/
def independenceHomeomorph (G : SimpleGraph V) (H : ∀ v, SimpleGraph (D v))
    (T : Set (Sigma D)) :
    Space (independenceComplex ((substitution G H).induce T)).toPreAbstractSimplicialComplex ≃ₜ
      Space (independenceComplex (selectedGraph G H T)).toPreAbstractSimplicialComplex :=
  (mapHomeomorph _ (graphIso G H T).toEquiv.toEmbedding).trans
    (Homeomorph.setCongr (congrArg realization (mapped_independence_faces G H T)))

#print axioms vertexEquiv
#print axioms adjacency_iff
#print axioms graphIso
#print axioms mapped_independence_faces
#print axioms independenceHomeomorph
end Finite
end D5.S3.Geometry.OccupiedFiberSubstitution
