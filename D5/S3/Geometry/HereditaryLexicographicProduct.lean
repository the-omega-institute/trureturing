/- GID: D5/S3/Geometry/HereditaryLexicographicProduct
   generality: G
   mirror-B: D5/B/S3/Geometry/HereditaryLexicographicProduct
   mirror-E: none(waiver:hereditary-lexicographic-product)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Actual finite closures give the unsuspended hereditary W product conclusion. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.CompactSphereNormalForm
import D5.S3.Geometry.OccupiedFiberSubstitution

/-!
Carnero Bravo, arXiv:2505.06457v2, Question 22. SP means contractible
or homotopy equivalent to an ordinary wedge of spheres. The SW input is
quantified over nonempty induced vertex sets: the realization of the empty
independence complex is empty and cannot have SP. The W output includes
all induced vertex sets, with the empty space represented by the empty
outer coproduct. No suspension is applied to any source property.
-/

noncomputable section
open Set Topology
open scoped ContinuousMap
attribute [local instance] Classical.propDecidable

namespace D5.S3.Geometry.HereditaryLexicographicProduct

open FiniteConeCollapse FiniteSimplicialJoin FiniteConeUnionWedge
open FiniteGraphVertexSubstitution CompactSphereNormalForm
open CompactWedgeFiniteFactor (FamilyWedge WedgeSum)
open EuclideanSphereJoin (StdSphere coordinatePoint)

-- Coordinate-gluing transport uses the original native carrier map.
open private FiniteGraphVertexSubstitution.substitution_same
  FiniteGraphVertexSubstitution.substitution_ne
  FiniteGraphVertexSubstitution.hereditarySubstitutionCore from
  D5.S3.Geometry.FiniteGraphVertexSubstitution

open private FiniteComponentClosure.vertexGluingHomeomorph from
  D5.S3.Geometry.FiniteComponentClosure

universe u v w x

/-- The source's unsuspended SP alternatives, with arbitrary original wedge indices. -/
def sourceSP (X : Type u) [TopologicalSpace X] : Prop :=
  ContractibleSpace X ∨ ∃ (J : Type v) (d : J → ℕ) (q : ∀ j, StdSphere (d j)),
    Nonempty (X ≃ₕ FamilyWedge q)

/-- The source's P alternatives; the outer coproduct is allowed to be empty. -/
def sourceP (X : Type u) [TopologicalSpace X] : Prop :=
  sourceSP.{u, w} X ∨ ∃ (A : Type v) (J : A → Type w)
    (d : ∀ a, J a → ℕ) (q : ∀ a j, StdSphere (d a j)),
    Nonempty (X ≃ₕ WedgeSum q)

/-- Hereditary source SP on nonempty induced vertex sets, the explicit empty-graph convention. -/
def sourceSW {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, S.Nonempty →
    sourceSP.{u, v} (Space (independenceComplex (G.induce S)).toPreAbstractSimplicialComplex)

/-- Hereditary source P on every induced vertex set, including the empty one. -/
def sourceW {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∀ S : Set V,
    sourceP.{u, v, w} (Space (independenceComplex (G.induce S)).toPreAbstractSimplicialComplex)

/-- The actual lexicographic product graph on the ordinary product vertex type. -/
def lexicographicProduct {V U : Type u} (G : SimpleGraph V) (H : SimpleGraph U) :
    SimpleGraph (V × U) where
  Adj x y := G.Adj x.1 y.1 ∨ (x.1 = y.1 ∧ H.Adj x.2 y.2)
  symm := ⟨fun _ _ h => h.elim (fun h => Or.inl h.symm)
    (fun h => Or.inr ⟨h.1.symm, h.2.symm⟩)⟩
  loopless := ⟨fun x h => h.elim (G.loopless.irrefl x.1) (fun h => H.loopless.irrefl x.2 h.2)⟩

private def homogeneousIso {V U : Type u} (G : SimpleGraph V) (H : SimpleGraph U) :
    substitution G (fun _ => H) ≃g lexicographicProduct G H where
  toEquiv := {
    toFun := fun x => (x.1, x.2)
    invFun := fun x => ⟨x.1, x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  map_rel_iff' := by
    rintro ⟨a, x⟩ ⟨b, y⟩
    by_cases h : a = b
    · subst b
      rw [FiniteGraphVertexSubstitution.substitution_same]
      simp [lexicographicProduct]
    · rw [FiniteGraphVertexSubstitution.substitution_ne _ _ h]
      simp [lexicographicProduct, h]

private def finiteSphereType (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ m : ℕ, ∃ _ : 0 < m, ∃ b : Fin m → List PositiveDimension,
    Nonempty (X ≃ₕ Space (FiniteComponentClosure.normalComplex m b))

private theorem finiteSphereType_hom {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y)
    (h : finiteSphereType X) : finiteSphereType Y := by
  obtain ⟨m, hm, b, ⟨f⟩⟩ := h
  exact ⟨m, hm, b, ⟨e.symm.trans f⟩⟩

private theorem model_finiteSphereType {X : Type u} [TopologicalSpace X] [Nonempty X]
    (M : HomotopyModel X) : finiteSphereType X := by
  have hm : 0 < M.size :=
    Nat.zero_lt_of_lt (M.equivalence.toFun (Classical.choice inferInstance)).1.isLt
  exact ⟨M.size, hm, M.bouquets,
    ⟨M.equivalence.trans (nativeModelHomeomorph M.size M.bouquets).symm.toHomotopyEquiv⟩⟩

private theorem sourceP_finiteSphereType {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X] (h : sourceP.{u, v, w} X) : finiteSphereType X := by
  rcases h with (hc | ⟨J, d, q, ⟨e⟩⟩) | ⟨A, J, d, q, ⟨e⟩⟩
  · letI := hc
    exact model_finiteSphereType contractibleModel
  · exact model_finiteSphereType (compactWedgeModel d q e)
  · exact model_finiteSphereType (compactModel d q e)

private theorem model_sourceP {X : Type u} [TopologicalSpace X]
    (M : HomotopyModel X) : sourceP.{u, 0, 0} X := by
  right
  exact ⟨Fin M.size, (fun k => Fin (M.bouquets k).length),
    (fun k i => ((M.bouquets k).get i).val),
    (fun k i => coordinatePoint ((M.bouquets k).get i).val), ⟨M.equivalence⟩⟩

private theorem finiteSphereType_sourceP {X : Type u} [TopologicalSpace X]
    (h : finiteSphereType X) : sourceP.{u, 0, 0} X := by
  obtain ⟨m, hm, b, ⟨e⟩⟩ := h
  exact model_sourceP ⟨m, b, e.trans (nativeModelHomeomorph m b).toHomotopyEquiv⟩

private theorem coordinateVertex_face {V : Type u} [Fintype V] [DecidableEq V]
    (M : PreAbstractSimplicialComplex V) (a : Space M) (v : V)
    (ha : a.val = Pi.single v 1) : ({v} : Finset V) ∈ M := by
  obtain ⟨s, hs, hx⟩ := a.property
  rw [← faceSimplex_eq_convexHull] at hx
  have hv : v ∈ s := by
    by_contra h
    have hz := hx.2.2 v h
    rw [ha] at hz
    simpa using hz
  exact (M.isRelLowerSet_faces hs).2 (Finset.singleton_subset_iff.mpr hv)
    (Finset.singleton_nonempty _)

private theorem finiteSphereType_join
    {V U : Type u} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (M : PreAbstractSimplicialComplex V) (N : PreAbstractSimplicialComplex U)
    (hMne : Nonempty (Space M)) (hNne : Nonempty (Space N))
    (hM : finiteSphereType (Space M)) (hN : finiteSphereType (Space N)) :
    finiteSphereType (OrdinaryJoin (Space M) (Space N)) := by
  let Q := FiniteComponentClosure.finiteComponentJoinClosure M N hM hN
  exact finiteSphereType_hom (joinHomeomorph M N hMne hNne).symm.toHomotopyEquiv Q.wplus

private theorem finiteSphereType_wedge
    {V U : Type u} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (M : PreAbstractSimplicialComplex V) (N : PreAbstractSimplicialComplex U)
    (a : Space M) (b : Space N)
    (ha : ∃ v, a.val = Pi.single v 1) (hb : ∃ w, b.val = Pi.single w 1)
    (hM : finiteSphereType (Space M)) (hN : finiteSphereType (Space N)) :
    finiteSphereType (Wedge a b) := by
  obtain ⟨v, hv⟩ := ha
  obtain ⟨w, hw⟩ := hb
  have hvm := coordinateVertex_face M a v hv
  have hwn := coordinateVertex_face N b w hw
  have ea : a = FiniteVertexCylinder.vertexPoint M v hvm := Subtype.ext hv
  have eb : b = FiniteVertexCylinder.vertexPoint N w hwn := Subtype.ext hw
  subst a
  subst b
  let Q := FiniteComponentClosure.selectedVertexWedgeClosure M N hM hN v hvm w hwn
  exact finiteSphereType_hom
    (FiniteComponentClosure.vertexGluingHomeomorph M N v w hvm hwn).symm.toHomotopyEquiv Q.wplus

private theorem substitution_finiteSphereType
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {D : V → Type u} [∀ v, Fintype (D v)] [∀ v, DecidableEq (D v)]
    [∀ v, Nonempty (D v)] (G : SimpleGraph V) (H : ∀ v, SimpleGraph (D v))
    (hbase : ∀ S : Set V, S.Nonempty →
      sourceP.{u, v, w} (Space (independenceComplex (G.induce S)).toPreAbstractSimplicialComplex))
    (hfiber : ∀ z, sourceSP.{u, x}
      (Space (independenceComplex (H z)).toPreAbstractSimplicialComplex)) :
    finiteSphereType (Space (independenceComplex (substitution G H)).toPreAbstractSimplicialComplex) := by
  apply FiniteGraphVertexSubstitution.hereditarySubstitutionCore finiteSphereType
    (fun e h => finiteSphereType_hom e h)
    (model_finiteSphereType (contractibleModel (X := PUnit.{u + 1})))
    finiteSphereType_join finiteSphereType_wedge G H
  · intro S hs
    letI : Nonempty S := hs.to_subtype
    let M := (independenceComplex (G.induce S)).toPreAbstractSimplicialComplex
    letI := realizationCompactSpace M
    letI : Nonempty (Space M) :=
      ⟨FiniteVertexCylinder.vertexPoint M (Classical.choice inferInstance) ((independenceComplex _).singleton_mem _)⟩
    exact sourceP_finiteSphereType (hbase S hs)
  · intro z
    let M := (independenceComplex (H z)).toPreAbstractSimplicialComplex
    letI := realizationCompactSpace M
    letI : Nonempty (Space M) :=
      ⟨FiniteVertexCylinder.vertexPoint M (Classical.choice inferInstance) ((independenceComplex _).singleton_mem _)⟩
    exact sourceP_finiteSphereType (Or.inl (hfiber z) : sourceP.{u, 0, x} (Space M))

private theorem occupiedInduced_finiteSphereType
    {V : Type u} [Fintype V] [DecidableEq V]
    {D : V → Type u} [∀ v, Fintype (D v)] [∀ v, DecidableEq (D v)]
    (G : SimpleGraph V) (H : ∀ v, SimpleGraph (D v))
    (hG : sourceSW.{u, v} G) (hH : ∀ z, sourceSW.{u, w} (H z))
    (T : Set (Sigma D)) (hT : T.Nonempty) :
    finiteSphereType (Space (independenceComplex
      ((substitution G H).induce T)).toPreAbstractSimplicialComplex) := by
  let B := OccupiedFiberSubstitution.occupiedBase T
  letI : Nonempty B := by
    obtain ⟨⟨z, d⟩, hd⟩ := hT
    exact ⟨⟨z, d, hd⟩⟩
  letI : ∀ z : B, Nonempty {d : D z.val | Sigma.mk z.val d ∈ T} :=
    fun z => OccupiedFiberSubstitution.selectedFiberNonempty T z
  have hb : ∀ S : Set B, S.Nonempty →
      sourceP.{u, 0, v} (Space (independenceComplex
        ((G.induce B).induce S)).toPreAbstractSimplicialComplex) := by
    intro S hs
    let e := graphIsoHomeomorph (nestedInduceIso G B S)
    have hp := hG (Subtype.val '' S) (hs.image Subtype.val)
    rcases hp with hc | ⟨J, d, q, ⟨f⟩⟩
    · left
      left
      letI := hc
      exact e.toHomotopyEquiv.contractibleSpace
    · left
      right
      exact ⟨J, d, q, ⟨e.toHomotopyEquiv.trans f⟩⟩
  have hf : ∀ z : B, sourceSP.{u, w} (Space (independenceComplex
      ((H z.val).induce {d | Sigma.mk z.val d ∈ T})).toPreAbstractSimplicialComplex) := by
    intro z
    exact hH z.val {d | Sigma.mk z.val d ∈ T} z.property
  have h := substitution_finiteSphereType (G.induce B)
    (fun z : B => (H z.val).induce {d | Sigma.mk z.val d ∈ T}) hb hf
  exact finiteSphereType_hom
    (OccupiedFiberSubstitution.independenceHomeomorph G H T).symm.toHomotopyEquiv h

private theorem emptyInduced_sourceP {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : Set V) (hT : ¬ T.Nonempty) :
    sourceP.{u, 0, 0} (Space (independenceComplex (G.induce T)).toPreAbstractSimplicialComplex) := by
  letI : IsEmpty T := ⟨fun x => hT ⟨x.val, x.property⟩⟩
  letI : IsEmpty (Space (independenceComplex (G.induce T)).toPreAbstractSimplicialComplex) := ⟨by
    intro x
    obtain ⟨s, hs, _⟩ := x.property
    obtain ⟨z, _⟩ := hs.1
    exact isEmptyElim z⟩
  exact model_sourceP emptyModel

/-- Under the original order and unsuspended source-SW hypotheses, every induced
subgraph of the actual product has source P, with an empty outer model for the
empty target. The input convention excludes only the empty induced graph from
SP, which has no nonempty model. -/
theorem result {V U : Type u} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (G : SimpleGraph V) (H : SimpleGraph U)
    (horderG : 2 ≤ Fintype.card V) (horderH : 2 ≤ Fintype.card U)
    (hG : sourceSW.{u, v} G) (hH : sourceSW.{u, w} H) :
    sourceW.{u, 0, 0} (lexicographicProduct G H) := by
  intro T
  by_cases hT : T.Nonempty
  · let e := homogeneousIso G H
    let S := e ⁻¹' T
    have hS : S.Nonempty := by
      obtain ⟨x, hx⟩ := hT
      exact ⟨e.symm x, by simpa [S] using hx⟩
    have bij : Set.BijOn e S T := ⟨fun _ hx => hx, e.injective.injOn, by
      intro x hx
      exact ⟨e.symm x, by simpa [S] using hx, e.apply_symm_apply x⟩⟩
    have h := occupiedInduced_finiteSphereType G (fun _ => H) hG (fun _ => hH) S hS
    exact finiteSphereType_sourceP
      (finiteSphereType_hom (graphIsoHomeomorph (e.induce bij)).toHomotopyEquiv h)
  · exact emptyInduced_sourceP _ T hT

#print axioms result
set_option pp.universes true in
#check @result
end D5.S3.Geometry.HereditaryLexicographicProduct
