/- GID: D5/S3/Topology/StableCategory/OrdinarySubdivisionTransfer
   generality: G
   mirror-B: none(waiver:support-for-the-tetrahedral-categorical-cover)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The simplicial cover transports to the ordinary iterated chain poset. -/

import D5.S3.Topology.StableCategory.InducedCategoricalCover

/-! Identify ordinary subdivisions of a simplicial complex with finite chain posets. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer

open BarycentricGraphDistance (Face)
open BarycentricBaseRigidity (sd)
open BarycentricNeighborhoodIteration (iteratedAmbient)
open ConnectedCategoryGraft (Categorical HasCategoricalCover)
open PartialOrder (NonemptyFiniteChains)
open private chainComplex isChain_finset map_fence from
  D5.S3.Topology.SubdivisionCategoricalCover

noncomputable section

variable {X Y : Type} [PartialOrder X] [PartialOrder Y]

private def homOfIso (e : X ≃o Y) : X →o Y :=
  ⟨e, e.monotone⟩

private def chainsCongr (e : X ≃o Y) : NonemptyFiniteChains X ≃o NonemptyFiniteChains Y where
  toFun s := s.map (homOfIso e)
  invFun s := s.map (homOfIso e.symm)
  left_inv s := by
    apply NonemptyFiniteChains.ext
    simp [NonemptyFiniteChains.map, Finset.image_image, Function.comp_def, homOfIso]
  right_inv s := by
    apply NonemptyFiniteChains.ext
    simp [NonemptyFiniteChains.map, Finset.image_image, Function.comp_def, homOfIso]
  map_rel_iff' := by
    intro s t
    change (s.map (homOfIso e)).finset ⊆ (t.map (homOfIso e)).finset ↔ s.finset ⊆ t.finset
    constructor
    · intro h x hx
      obtain ⟨y, hy, hxy⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).mp
        (h ((NonemptyFiniteChains.mem_map_iff _ _ _).mpr ⟨x, hx, rfl⟩))
      exact (e.injective hxy) ▸ hy
    · intro h x hx
      obtain ⟨u, hu, rfl⟩ := (NonemptyFiniteChains.mem_map_iff _ _ _).mp hx
      exact (NonemptyFiniteChains.mem_map_iff _ _ _).mpr ⟨u, h hu, rfl⟩

private def orderComplexFace (X : Type) [PartialOrder X] :
    Face (chainComplex X) ≃o NonemptyFiniteChains X where
  toFun s := ⟨s.val, s.property.1, fun u v => by
    by_cases h : u.val = v.val
    · exact Or.inl h.le
    · exact s.property.2 u.property v.property h⟩
  invFun s := ⟨s.finset, s.nonempty, isChain_finset s⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private def subdivisionFace {A : Type} (J : PreAbstractSimplicialComplex A) :
    Face (sd J) ≃o NonemptyFiniteChains (Face J) where
  toFun s := ⟨s.val, s.property.1, fun u v => by
    by_cases h : u.val = v.val
    · exact Or.inl h.le
    · exact (s.property.2.1 u.property v.property h).imp LT.lt.le LT.lt.le⟩
  invFun s := ⟨s.finset, s.nonempty, by
    intro u hu v hv h
    exact (s.comparable ⟨u, hu⟩ ⟨v, hv⟩).imp
      (fun he => lt_of_le_of_ne he h) (fun he => lt_of_le_of_ne he h.symm),
    fun f _ => f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Iterating the finite-space subdivision changes the vertex type to its
nonempty chains at every round. -/
def finiteSpaceSubdivision (X : Type) [PartialOrder X] :
    ℕ → Σ P : Type, PartialOrder P
  | 0 => ⟨X, inferInstance⟩
  | n + 1 =>
    let P := finiteSpaceSubdivision X n
    letI := P.2
    ⟨NonemptyFiniteChains P.1, inferInstance⟩

private def chainPoset (X : Type) [PartialOrder X] (n : ℕ) :
    letI : PartialOrder (finiteSpaceSubdivision X (n + 1)).1 :=
      (finiteSpaceSubdivision X (n + 1)).2
    Face (iteratedAmbient (chainComplex X) n).2 ≃o (finiteSpaceSubdivision X (n + 1)).1 := by
  induction n with
  | zero => exact orderComplexFace X
  | succ n ih =>
    letI : PartialOrder (finiteSpaceSubdivision X (n + 1)).1 :=
      (finiteSpaceSubdivision X (n + 1)).2
    change Face (sd (iteratedAmbient (chainComplex X) n).2) ≃o
      NonemptyFiniteChains (finiteSpaceSubdivision X (n + 1)).1
    exact OrderIso.trans (subdivisionFace (iteratedAmbient (chainComplex X) n).2)
      (chainsCongr ih)

private theorem transport_lower_cover (e : X ≃o Y) {k : ℕ}
    (cover : HasCategoricalCover X k) : HasCategoricalCover Y k := by
  obtain ⟨U, hU, hcover⟩ := cover
  let V (j : Fin k) := e.symm ⁻¹' U j
  refine ⟨V, ?_, fun y => hcover (e.symm y)⟩
  intro j
  refine ⟨fun _ _ hxy hy => (hU j).1 (e.symm.monotone hxy) hy, ?_⟩
  obtain ⟨b, hb⟩ := (hU j).2
  let pre : V j →o U j :=
    ⟨fun y => ⟨e.symm y.val, y.property⟩, fun _ _ h => e.symm.monotone h⟩
  let F (f : U j →o X) : V j →o Y := (homOfIso e).comp (f.comp pre)
  have start : F (OrderEmbedding.subtype (U j)).toOrderHom =
      (OrderEmbedding.subtype (V j)).toOrderHom := by
    ext y
    exact e.apply_symm_apply y.val
  have finish : F (OrderHom.const (U j) b) = OrderHom.const (V j) (e b) := by
    ext
    rfl
  have step (f g : U j →o X) (h : f ≤ g) : F f ≤ F g :=
    fun y => e.monotone ((OrderHom.le_def.mp h) (pre y))
  have h : Relation.EqvGen (· ≤ ·)
      (F (OrderEmbedding.subtype (U j)).toOrderHom) (F (OrderHom.const (U j) b)) :=
    map_fence F (fun f g hfg => .rel _ _ (step f g hfg)) hb
  rw [start, finish] at h
  exact ⟨e b, h⟩

/-- The two extra face-meeting levels in the simplicial cover construction
give the `r + 2` ordinary subdivision of the original finite poset. -/
theorem transfer_lower_cover (r k : ℕ)
    (cover : HasCategoricalCover
      (NonemptyFiniteChains (Face (iteratedAmbient (chainComplex X) r).2)) k) :
    @HasCategoricalCover (finiteSpaceSubdivision X (r + 2)).1
      (finiteSpaceSubdivision X (r + 2)).2 k := by
  letI : PartialOrder (finiteSpaceSubdivision X (r + 1)).1 :=
    (finiteSpaceSubdivision X (r + 1)).2
  exact transport_lower_cover (chainsCongr (chainPoset X r)) cover

end

end D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer
