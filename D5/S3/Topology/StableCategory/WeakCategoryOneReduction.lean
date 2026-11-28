/- GID: D5/S3/Topology/StableCategory/WeakCategoryOneReduction
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/WeakCategoryOneReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stable categorical bounds reduce to contractible order complexes. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.FaceInclusionNullhomotopy
import D5.S3.Topology.StableCategory.LocalFactorsSubdivision

/-! Reduce the stable comparison to spaces with contractible order complex. -/

noncomputable section

namespace D5.S3.Topology.WeakCategoryOneReduction

open ContinuousMap Set
open D5.S3.Geometry.FiniteSimplicialJoin (Space)
open D5.S3.Geometry.FiniteConeUnionWedge (realizationInclusion)
open D5.S3.Topology.BarycentricGraphDistance (Face)
open D5.S3.Topology.ConnectedCategoryGraft (HasCategoricalCover)
open D5.S3.Topology.FaceInclusionNullhomotopy (face_inclusion_nullhomotopic)
open D5.S3.Topology.LocalFactorsSubdivision (LocalFactors)
open D5.S3.Topology.OrderComplexNullhomotopy (orderComplex)
open D5.S3.Topology.StableCategory.LebesgueStarAssignment
  (categorical_subcomplex_cover_of_open_cover DepthVertices depthComplex iteratedRealization)
open D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer (finiteSpaceSubdivision)
open D5.S3.Topology.WeaklyContractibleFactor (factors_through_weakly_contractible)

open private contractible_of_order_fence from D5.S3.Topology.StableCategory.WeaklyContractibleFactor
open private chainComplex from D5.S3.Topology.SubdivisionCategoricalCover
open private faceEmbedding from D5.S3.Topology.StableCategory.FaceInclusionNullhomotopy
open private chainPoset chainsCongr transport_lower_cover
  from D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer
open private depthFintype depthDecEq from D5.S3.Topology.StableCategory.LebesgueStarAssignment

/-- An ordinary subdivision admits a categorical lower cover of the indicated size. -/
def StableCategoricalCover (P : Type) [PartialOrder P] (b : ℕ) : Prop :=
  ∃ r, @HasCategoricalCover (finiteSpaceSubdivision P r).1 (finiteSpaceSubdivision P r).2 b

/-- The class to which the universal inequality reduces. -/
def WeaklyContractibleCoverBound (b : ℕ) : Prop :=
  ∀ (P : Type) [PartialOrder P] [Fintype P] [DecidableEq P],
    ContractibleSpace (Space (orderComplex P)) → StableCategoricalCover P b

private theorem eventCover_of_iso {P Q : Type} [PartialOrder P] [PartialOrder Q]
    (e : P ≃o Q) {b : ℕ} (h : StableCategoricalCover P b) : StableCategoricalCover Q b := by
  obtain ⟨r, hr⟩ := h
  have iso : ∀ r, letI := (finiteSpaceSubdivision P r).2
      letI := (finiteSpaceSubdivision Q r).2
      (finiteSpaceSubdivision P r).1 ≃o (finiteSpaceSubdivision Q r).1 := by
    intro r
    induction r with
    | zero => exact e
    | succ r ih =>
      letI := (finiteSpaceSubdivision P r).2
      letI := (finiteSpaceSubdivision Q r).2
      exact chainsCongr ih
  letI := (finiteSpaceSubdivision P r).2
  letI := (finiteSpaceSubdivision Q r).2
  exact ⟨r, transport_lower_cover (iso r) hr⟩

private theorem eventCover_shift {P : Type} [ord : PartialOrder P] (n : ℕ) {b : ℕ}
    (h : @StableCategoricalCover (@finiteSpaceSubdivision P ord n).1
      (@finiteSpaceSubdivision P ord n).2 b) : StableCategoricalCover P b := by
  let S := @finiteSpaceSubdivision P ord n
  obtain ⟨r, hr⟩ := h
  have eq (r : ℕ) :
      @finiteSpaceSubdivision S.1 S.2 r = @finiteSpaceSubdivision P ord (n + r) := by
    induction r with
    | zero => rfl
    | succ r ih =>
      change (let T := @finiteSpaceSubdivision S.1 S.2 r
        letI := T.2
        (⟨PartialOrder.NonemptyFiniteChains T.1, inferInstance⟩ :
          Σ X : Type, PartialOrder X)) = _
      rw [ih]
      rfl
  let cover (T : Σ X : Type, PartialOrder X) : Prop := @HasCategoricalCover T.1 T.2 b
  exact ⟨n + r, (congrArg cover (eq r)).mp hr⟩

private theorem factors_of_region {V : Type} [Fintype V] [DecidableEq V]
    {A K : PreAbstractSimplicialComplex V} (h : A ≤ K) (p : Face K) {b : ℕ}
    (B : WeaklyContractibleCoverBound b) (H : (realizationInclusion h).Nullhomotopic) :
    ∃ (Q : Type) (ord : PartialOrder Q) (_ : Finite Q),
      letI : PartialOrder Q := ord
      ∃ (i : Face A →o Q) (q : Q →o Face K),
        q.comp i = (faceEmbedding h).toOrderHom ∧ StableCategoricalCover Q b := by
  classical
  by_cases hA : Nonempty (Face A)
  · obtain ⟨Q, ord, finiteQ, hQ, i, q, hcomp⟩ :=
      factors_through_weakly_contractible hA.some p (faceEmbedding h).toOrderHom
        (face_inclusion_nullhomotopic h p H)
    letI : PartialOrder Q := ord
    letI : Fintype Q := Fintype.ofFinite Q
    exact ⟨Q, ord, finiteQ, i.toOrderHom, q, hcomp, B Q hQ⟩
  · letI : IsEmpty (Face A) := not_nonempty_iff.mp hA
    let Q := PUnit.{1}
    have hQ : ContractibleSpace (Space (orderComplex Q)) :=
      contractible_of_order_fence PUnit.unit (.rel _ _ (fun _ => le_rfl))
    refine ⟨Q, inferInstance, inferInstance, OrderHom.const _ PUnit.unit,
      OrderHom.const _ p, ?_, B Q hQ⟩
    apply OrderHom.ext
    funext x
    exact isEmptyElim x

private theorem lowerCover_of_subcomplexes {V : Type} [Fintype V] [DecidableEq V]
    {K : PreAbstractSimplicialComplex V} {a b : ℕ} (B : WeaklyContractibleCoverBound b)
    (p : Face K) (A : Fin a → PreAbstractSimplicialComplex V) (hA : ∀ i, A i ≤ K)
    (cover : ∀ s ∈ K, ∃ i, s ∈ A i)
    (H : ∀ i, (realizationInclusion (hA i)).Nullhomotopic) :
    StableCategoricalCover (Face K) (a * b) := by
  classical
  have data := fun i => factors_of_region (hA i) p B (H i)
  choose Q ord hf hdata using data
  letI : ∀ i, PartialOrder (Q i) := ord
  choose insert project agrees hQ using hdata
  let region (i : Fin a) : Set (Face K) := {f | f.val ∈ A i}
  let restrict (i : Fin a) : region i →o Face (A i) :=
    ⟨fun f => ⟨f.val.val, f.property⟩, fun _ _ h => h⟩
  let F : LocalFactors (Face K) Q :=
    { region := region
      lower := fun i f g hfg hg =>
        ((A i).isRelLowerSet_faces hg).2 hfg (K.isRelLowerSet_faces g.property).1
      covers := fun f => cover f.val f.property
      insert := fun i => (insert i).comp (restrict i)
      project := project
      agrees := fun i f => congrFun (congrArg DFunLike.coe (agrees i)) (restrict i f) }
  exact F.cover_at_some_depth hf hQ

/-- A universal stable cover bound for weakly contractible finite posets implies
the product bound for every categorical open cover of a finite order complex. -/
theorem stable_cover_of_contractible_bound {P : Type} [PartialOrder P]
    [Fintype P] [DecidableEq P] (p : P) {a b : ℕ} (B : WeaklyContractibleCoverBound b)
    (U : Fin a → Set (Space (orderComplex P))) (hopen : ∀ i, IsOpen (U i))
    (hcover : (univ : Set (Space (orderComplex P))) ⊆ ⋃ i, U i)
    (H : ∀ i, (ContinuousMap.subtypeVal (U i)).Nullhomotopic) :
    StableCategoricalCover P (a * b) := by
  classical
  let K := orderComplex P
  let pt : Space K := D5.S3.Geometry.FiniteVertexCylinder.vertexPoint K p
    ⟨Finset.singleton_nonempty _, by simp⟩
  obtain ⟨i, _⟩ := mem_iUnion.mp (hcover (mem_univ pt))
  haveI : Nonempty (Fin a) := ⟨i⟩
  obtain ⟨n, _, A, hA, covers, _, _, contracts⟩ :=
    categorical_subcomplex_cover_of_open_cover K U hopen hcover H
  letI : Fintype (DepthVertices K n) := depthFintype K n
  letI : DecidableEq (DepthVertices K n) := depthDecEq K n
  letI := (finiteSpaceSubdivision P (n + 1)).2
  let e := chainPoset P n
  let x := (iteratedRealization K n).symm pt
  obtain ⟨s, hs, _⟩ := (D5.S3.Geometry.FiniteConeCollapse.realization_mem_iff _ _).mp x.property
  have hc := lowerCover_of_subcomplexes B (⟨s, hs⟩ : Face (depthComplex K n))
    A hA covers contracts
  exact eventCover_shift (n + 1) (eventCover_of_iso e hc)

/-- Testing the stable product bound against categorical open covers of
finite order complexes is equivalent to testing it for contractible
realizations. In particular the reduction applies to the constant two. -/
theorem stable_product_bound_iff_contractible (b : ℕ) :
    (∀ (P : Type) [PartialOrder P] [Fintype P] [DecidableEq P] (_p : P) (a : ℕ)
      (U : Fin a → Set (Space (orderComplex P))),
      (∀ i, IsOpen (U i)) →
      (univ : Set (Space (orderComplex P))) ⊆ ⋃ i, U i →
      (∀ i, (ContinuousMap.subtypeVal (U i)).Nullhomotopic) →
      StableCategoricalCover P (a * b)) ↔ WeaklyContractibleCoverBound b := by
  classical
  constructor
  · intro B P _ _ _ hP
    haveI := hP
    obtain ⟨x⟩ := (inferInstance : Nonempty (Space (orderComplex P)))
    obtain ⟨s, hs, _⟩ :=
      (D5.S3.Geometry.FiniteConeCollapse.realization_mem_iff _ _).mp x.property
    obtain ⟨p, _⟩ := (orderComplex P).isRelLowerSet_faces hs |>.1
    have result := B P p 1 (fun _ => univ) (fun _ => isOpen_univ)
      (fun x _ => mem_iUnion.mpr ⟨0, mem_univ x⟩)
      (fun _ => (id_nullhomotopic _).comp_left (ContinuousMap.subtypeVal _))
    simpa using result
  · intro B P _ _ _ p a U ho hc H
    exact stable_cover_of_contractible_bound p B U ho hc H

end D5.S3.Topology.WeakCategoryOneReduction
