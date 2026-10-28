/- GID: D5/S3/Geometry/FiniteComponentClosure/JoinModels
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteComponentClosure/JoinModels
   mirror-E: none(waiver:finite-component-closure)
   anchors: [mathlib/module/Mathlib.Topology.Homeomorph.Quotient]
   utility: none
   digest: Native bouquet joins, finite-component construction, and dimension-multiplicity reindexing. -/
import D5.S3.Geometry.FiniteComponentClosure.BasedJoin

noncomputable section
open Set Finset Topology ContinuousMap
open scoped BigOperators unitInterval

set_option maxSynthPendingDepth 12

namespace D5.S3.Geometry.FiniteComponentClosure

open private
  D5.S3.Geometry.FiniteComponentClosure.joinCongr
  D5.S3.Geometry.FiniteComponentClosure.joinHomeomorph
  D5.S3.Geometry.FiniteComponentClosure.twoPoints_singleton
  D5.S3.Geometry.FiniteComponentClosure.twoPoint
  D5.S3.Geometry.FiniteComponentClosure.sphereVertex_face
  D5.S3.Geometry.FiniteComponentClosure.coordinateHomeomorph
  D5.S3.Geometry.FiniteComponentClosure.coproductComplex
  D5.S3.Geometry.FiniteComponentClosure.mem_coproductComplex
  from D5.S3.Geometry.FiniteComponentClosure.Transport

open private
  D5.S3.Geometry.FiniteComponentClosure.bouquetInclusion
  D5.S3.Geometry.FiniteComponentClosure.bouquetInclusion_base
  D5.S3.Geometry.FiniteComponentClosure.vertexComplex
  D5.S3.Geometry.FiniteComponentClosure.bouquetVertex_face
  D5.S3.Geometry.FiniteComponentClosure.mem_bouquetComplex
  D5.S3.Geometry.FiniteComponentClosure.bouquetInclusion_intersection
  D5.S3.Geometry.FiniteComponentClosure.bouquetBases
  D5.S3.Geometry.FiniteComponentClosure.emptyBouquet_point
  D5.S3.Geometry.FiniteComponentClosure.emptyBouquetJoinEquiv
  D5.S3.Geometry.FiniteComponentClosure.normalVertex_face
  from D5.S3.Geometry.FiniteComponentClosure.Models

open private
  D5.S3.Geometry.FiniteComponentClosure.join_left_vertex
  D5.S3.Geometry.FiniteComponentClosure.join_right_vertex
  D5.S3.Geometry.FiniteComponentClosure.vertexComplex_le
  D5.S3.Geometry.FiniteComponentClosure.nativeConeHomeomorph
  from D5.S3.Geometry.FiniteComponentClosure.ConeSplits

open private
  D5.S3.Geometry.FiniteComponentClosure.sphereCast
  D5.S3.Geometry.FiniteComponentClosure.sphereCast_point
  D5.S3.Geometry.FiniteComponentClosure.SphereFamily
  D5.S3.Geometry.FiniteComponentClosure.bouquetListCast
  from D5.S3.Geometry.FiniteComponentClosure.SelectedWedge

open private
  D5.S3.Geometry.FiniteComponentClosure.basedTrans
  D5.S3.Geometry.FiniteComponentClosure.basedHomeomorphism
  D5.S3.Geometry.FiniteComponentClosure.nativeSuspensionComplex
  D5.S3.Geometry.FiniteComponentClosure.nativeSuspensionPoint
  D5.S3.Geometry.FiniteComponentClosure.vertexUnionJoinBased
  D5.S3.Geometry.FiniteComponentClosure.basedOrdinary
  D5.S3.Geometry.FiniteComponentClosure.nativeBouquetNormalization
  D5.S3.Geometry.FiniteComponentClosure.basedBouquetAppend
  D5.S3.Geometry.FiniteComponentClosure.NormalizedJoinPiece
  D5.S3.Geometry.FiniteComponentClosure.unionList
  D5.S3.Geometry.FiniteComponentClosure.mem_unionList
  D5.S3.Geometry.FiniteComponentClosure.familyJoinSpec
  D5.S3.Geometry.FiniteComponentClosure.familyJoinBased
  from D5.S3.Geometry.FiniteComponentClosure.BasedJoin

set_option maxSynthPendingDepth 12

section NativeJoinModels

private def joinSymmetry {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] :
    FiniteSimplicialJoin.OrdinaryJoin X Y ≃ₜ FiniteSimplicialJoin.OrdinaryJoin Y X := by
  let e : (X × Y × I) ≃ₜ (Y × X × I) := {
    toFun := fun p => (p.2.1, p.1, unitInterval.symm p.2.2)
    invFun := fun p => (p.2.1, p.1, unitInterval.symm p.2.2)
    left_inv := fun p => by simp
    right_inv := fun p => by simp
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  apply Homeomorph.Quotient.congr e
  intro p q
  change (p.2.2 = q.2.2 ∧ (p.2.2 = 1 ∨ p.1 = q.1) ∧
    (p.2.2 = 0 ∨ p.2.1 = q.2.1)) ↔
    (unitInterval.symm p.2.2 = unitInterval.symm q.2.2 ∧
      (unitInterval.symm p.2.2 = 1 ∨ p.2.1 = q.2.1) ∧
      (unitInterval.symm p.2.2 = 0 ∨ p.1 = q.1))
  rw [unitInterval.symm_inj, unitInterval.symm_eq_one,
    unitInterval.symm_eq_zero]
  tauto

private def nativeJoinCongr {V W V' W' : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype V'] [DecidableEq V'] [Fintype W'] [DecidableEq W']
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (K' : PreAbstractSimplicialComplex V') (L' : PreAbstractSimplicialComplex W')
    (hK : Nonempty (FiniteSimplicialJoin.Space K)) (hL : Nonempty (FiniteSimplicialJoin.Space L))
    (hK' : Nonempty (FiniteSimplicialJoin.Space K')) (hL' : Nonempty (FiniteSimplicialJoin.Space L'))
    (e : FiniteSimplicialJoin.Space K ≃ₕ FiniteSimplicialJoin.Space K')
    (d : FiniteSimplicialJoin.Space L ≃ₕ FiniteSimplicialJoin.Space L') :
    FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin K L) ≃ₕ
      FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin K' L') :=
  ((FiniteSimplicialJoin.joinHomeomorph K L hK hL).symm.toHomotopyEquiv.trans
    (joinCongr e d)).trans (FiniteSimplicialJoin.joinHomeomorph K' L' hK' hL').toHomotopyEquiv

private def nativeJoinSymmetry {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (hK : Nonempty (FiniteSimplicialJoin.Space K)) (hL : Nonempty (FiniteSimplicialJoin.Space L)) :
    FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin K L) ≃ₜ
      FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin L K) :=
  ((FiniteSimplicialJoin.joinHomeomorph K L hK hL).symm.trans joinSymmetry).trans
    (FiniteSimplicialJoin.joinHomeomorph L K hL hK)

private theorem singletonBouquetComplex (d : {n : ℕ // 0 < n}) :
    bouquetComplex [d] = (sphereComplex d.val).map (bouquetInclusion [d] ⟨0, by simp⟩) := by
  apply SetLike.ext
  intro s
  rw [mem_bouquetComplex]
  constructor
  · rintro (rfl | ⟨i, hs⟩)
    · exact ⟨{sphereVertex d.val}, sphereVertex_face d.val,
        by
          change ({sphereVertex d.val} : Finset (SphereVertices d.val)).image
            (bouquetInclusion [d] ⟨0, by simp⟩) = {none}
          exact (Finset.image_singleton _ _).trans
            (congrArg (fun v : BouquetVertices [d] => ({v} : Finset (BouquetVertices [d])))
              (bouquetInclusion_base [d] ⟨0, by simp⟩))⟩
    · have hi : i = ⟨0, by simp⟩ := by
        apply Fin.ext
        change i.val = 0
        have hi : i.val < 1 := by simpa only [List.length_singleton] using i.isLt
        omega
      subst i
      exact hs
  · intro hs
    exact Or.inr ⟨⟨0, by simp⟩, hs⟩

private def sphereSingletonBouquetHomeomorph (d : {n : ℕ // 0 < n}) :
    FiniteSimplicialJoin.Space (sphereComplex d.val) ≃ₜ
      FiniteSimplicialJoin.Space (bouquetComplex [d]) :=
  (coordinateHomeomorph (sphereComplex d.val) (bouquetInclusion [d] ⟨0, by simp⟩)).trans
    (Homeomorph.setCongr (congrArg FiniteConeCollapse.realization (singletonBouquetComplex d).symm))

private def spherePairJoinNormalization (p q : ℕ) :
    FiniteSimplicialJoin.Space
      (FiniteSimplicialJoin.simplicialJoin (sphereComplex p) (sphereComplex q)) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex [⟨p + q + 1, by omega⟩]) :=
  (((((FiniteSimplicialJoin.joinHomeomorph (sphereComplex p) (sphereComplex q)
    ⟨spherePoint p⟩ ⟨spherePoint q⟩).symm.trans
      (joinHomeomorph (sphereHomeomorph p) (sphereHomeomorph q))).trans
      (EuclideanSphereJoin.sphereJoinHomeomorph p q)).trans
      (sphereHomeomorph (p + q + 1)).symm).trans
      (sphereSingletonBouquetHomeomorph ⟨p + q + 1, by omega⟩)).toHomotopyEquiv

end NativeJoinModels

private def basedBouquetListCast {ds es : BouquetSpec} (h : ds = es) :
    SingletonRetractionBasedInverse.BasedEquivalence (bouquetPoint ds) (bouquetPoint es) := by
  subst es
  exact basedHomeomorphism (Homeomorph.refl _) _ _ rfl

section FiniteVertexFamilyAssembly

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

private def unitEmptyBouquetHomeomorph : Unit ≃ₜ FiniteSimplicialJoin.Space (bouquetComplex []) where
  toFun _ := bouquetPoint []
  invFun _ := ()
  left_inv _ := rfl
  right_inv x := (emptyBouquet_point x).symm
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

private def vertexJoinNormalization (a : V) (Z : PreAbstractSimplicialComplex W)
    (z : FiniteSimplicialJoin.Space Z) :
    FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex []) :=
  ((nativeConeHomeomorph Z a z).trans
    (joinHomeomorph unitEmptyBouquetHomeomorph (Homeomorph.refl _))).toHomotopyEquiv.trans
    (emptyBouquetJoinEquiv z)

private structure NormalizedVertexJoinPiece (Z : PreAbstractSimplicialComplex W) (a : V) where
  complex : PreAbstractSimplicialComplex V
  vertex_face : ({a} : Finset V) ∈ complex
  spec : BouquetSpec
  normalization : SingletonRetractionBasedInverse.BasedEquivalence
    (FiniteVertexCylinder.vertexPoint (FiniteSimplicialJoin.simplicialJoin complex Z)
      (Sum.inl a) (join_left_vertex complex Z a vertex_face)) (bouquetPoint spec)

private def vertexFamilyComplex (a : V) {Z : PreAbstractSimplicialComplex W}
    (ps : List (NormalizedVertexJoinPiece Z a)) : PreAbstractSimplicialComplex V :=
  vertexComplex a ⊔ unionList (ps.map (·.complex))

private def vertexFamilyJoinBased (Z : PreAbstractSimplicialComplex W)
    (z : FiniteSimplicialJoin.Space Z) (a : V)
    (ps : List (NormalizedVertexJoinPiece Z a)) :
    (hd : ps.Pairwise (fun P Q => P.complex ⊓ Q.complex = vertexComplex a)) →
    SingletonRetractionBasedInverse.BasedEquivalence
      (FiniteVertexCylinder.vertexPoint (FiniteSimplicialJoin.simplicialJoin (vertexFamilyComplex a ps) Z)
        (Sum.inl a) (join_left_vertex _ Z a (Or.inl rfl)))
      (bouquetPoint (ps.flatMap (·.spec))) := by
  induction ps with
  | nil =>
    intro hd
    let e := Homeomorph.setCongr (congrArg FiniteConeCollapse.realization
      (show FiniteSimplicialJoin.simplicialJoin (vertexFamilyComplex (Z := Z) a []) Z =
        FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z by simp [vertexFamilyComplex, unionList]))
    exact nativeBouquetNormalization _ _ _ []
      (e.toHomotopyEquiv.trans (vertexJoinNormalization a Z z))
  | cons P ps ih =>
    intro hd
    let N := vertexFamilyComplex a ps
    have hN : ({a} : Finset V) ∈ N := Or.inl rfl
    have hPN : P.complex ⊓ N = vertexComplex a := by
      apply le_antisymm
      · rintro s ⟨hs, ht⟩
        rcases ht with ht | ht
        · exact ht
        · obtain ⟨J, hJ, hJs⟩ := (mem_unionList _ s).mp ht
          obtain ⟨Q, hQ, rfl⟩ := List.mem_map.mp hJ
          exact ((List.pairwise_cons.mp hd).1 Q hQ) ▸ ⟨hs, hJs⟩
      · exact le_inf (vertexComplex_le P.complex a P.vertex_face) le_sup_left
    let F := vertexUnionJoinBased P.complex N Z a P.vertex_face hN hPN
    let e := Homeomorph.setCongr (congrArg FiniteConeCollapse.realization
      (show FiniteSimplicialJoin.simplicialJoin (vertexFamilyComplex a (P :: ps)) Z =
        FiniteSimplicialJoin.simplicialJoin (P.complex ⊔ N) Z by
        congr 1
        change vertexComplex a ⊔ (P.complex ⊔ unionList (ps.map (·.complex))) =
          P.complex ⊔ (vertexComplex a ⊔ unionList (ps.map (·.complex)))
        ac_rfl))
    let pre := basedHomeomorphism e
      (FiniteVertexCylinder.vertexPoint
        (FiniteSimplicialJoin.simplicialJoin (vertexFamilyComplex a (P :: ps)) Z)
        (Sum.inl a) (join_left_vertex _ Z a (Or.inl rfl)))
      (FiniteVertexCylinder.vertexPoint (FiniteSimplicialJoin.simplicialJoin (P.complex ⊔ N) Z)
        (Sum.inl a) (join_left_vertex _ Z a (Or.inl P.vertex_face))) (Subtype.ext rfl)
    exact basedTrans
      (basedTrans pre (basedTrans F (basedTrans
        (FiniteConeUnionWedge.basedWedgeEquivalence P.normalization
          (ih (List.pairwise_cons.mp hd).2))
        (basedBouquetAppend P.spec
          (ps.flatMap (fun R : NormalizedVertexJoinPiece Z a => R.spec))))))
      (basedBouquetListCast (List.flatMap_cons (f := fun R : NormalizedVertexJoinPiece Z a => R.spec)
        (x := P) (xs := ps)).symm)


end FiniteVertexFamilyAssembly

section BouquetJoinAssembly

private theorem mappedVertexFace {V U : Type*} [DecidableEq V] [DecidableEq U]
    (K : PreAbstractSimplicialComplex V) (e : V ↪ U) (a : V)
    (ha : ({a} : Finset V) ∈ K) : ({e a} : Finset U) ∈ K.map e :=
  ⟨{a}, ha, Finset.image_singleton e a⟩

private theorem bouquetMappedVertex (ds : BouquetSpec) (i : Fin ds.length) :
    ({none} : Finset (BouquetVertices ds)) ∈
      (sphereComplex (ds.get i).val).map (bouquetInclusion ds i) := by
  simpa only [bouquetInclusion_base] using
    mappedVertexFace (sphereComplex (ds.get i).val) (bouquetInclusion ds i)
      (sphereVertex (ds.get i).val) (sphereVertex_face _)

private theorem bouquetMappedIntersection (ds : BouquetSpec) (i j : Fin ds.length)
    (hij : i ≠ j) :
    (sphereComplex (ds.get i).val).map (bouquetInclusion ds i) ⊓
      (sphereComplex (ds.get j).val).map (bouquetInclusion ds j) = vertexComplex none := by
  apply le_antisymm
  · intro s hs
    have hn := (((sphereComplex (ds.get i).val).map (bouquetInclusion ds i)).isRelLowerSet_faces hs.1).1
    change s = {none}
    apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
    refine ⟨hn, ?_⟩
    intro u hu
    obtain ⟨A, hA, hAi⟩ := hs.1
    obtain ⟨B, hB, hBj⟩ := hs.2
    obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp (hAi.symm ▸ hu)
    obtain ⟨w, hw, hwj⟩ := Finset.mem_image.mp (hBj.symm ▸ hu)
    exact hvi.symm.trans (bouquetInclusion_intersection ds i j hij v w (hvi.trans hwj.symm))
  · exact le_inf
      (vertexComplex_le _ none (bouquetMappedVertex ds i))
      (vertexComplex_le _ none (bouquetMappedVertex ds j))

private def bouquetJoinPieces {W : Type*} [Fintype W] [DecidableEq W]
    (ds : BouquetSpec) (Z : PreAbstractSimplicialComplex W) (z : FiniteSimplicialJoin.Space Z)
    (spec : Fin ds.length → BouquetSpec)
    (E : ∀ i, FiniteSimplicialJoin.Space
      (FiniteSimplicialJoin.simplicialJoin (sphereComplex (ds.get i).val) Z) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex (spec i)))
    (i : Fin ds.length) : NormalizedVertexJoinPiece Z (none : BouquetVertices ds) where
  complex := (sphereComplex (ds.get i).val).map (bouquetInclusion ds i)
  vertex_face := bouquetMappedVertex ds i
  spec := spec i
  normalization := nativeBouquetNormalization _ _ _ (spec i)
    ((nativeJoinCongr _ Z (sphereComplex (ds.get i).val) Z
      ⟨FiniteVertexCylinder.vertexPoint _ none (bouquetMappedVertex ds i)⟩ ⟨z⟩
      ⟨spherePoint (ds.get i).val⟩ ⟨z⟩
      (coordinateHomeomorph (sphereComplex (ds.get i).val) (bouquetInclusion ds i)).symm.toHomotopyEquiv
      (HomotopyEquiv.refl _)).trans (E i))

private theorem bouquetJoinFamilyComplex {W : Type*} [Fintype W] [DecidableEq W]
    (ds : BouquetSpec) (Z : PreAbstractSimplicialComplex W) (z : FiniteSimplicialJoin.Space Z)
    (spec : Fin ds.length → BouquetSpec)
    (E : ∀ i, FiniteSimplicialJoin.Space
      (FiniteSimplicialJoin.simplicialJoin (sphereComplex (ds.get i).val) Z) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex (spec i))) :
    vertexFamilyComplex none (List.ofFn (bouquetJoinPieces ds Z z spec E)) = bouquetComplex ds := by
  apply SetLike.ext
  intro s
  rw [mem_bouquetComplex]
  change (s ∈ vertexComplex none ∨ s ∈ unionList _) ↔ _
  rw [mem_unionList]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨J, hJ, hs⟩
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hJ
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
    exact ⟨i, hs⟩
  · rintro ⟨i, hs⟩
    exact ⟨_, List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩, hs⟩

private def bouquetFamilyJoinNormalization {W : Type*} [Fintype W] [DecidableEq W]
    (ds : BouquetSpec) (Z : PreAbstractSimplicialComplex W) (z : FiniteSimplicialJoin.Space Z)
    (spec : Fin ds.length → BouquetSpec)
    (E : ∀ i, FiniteSimplicialJoin.Space
      (FiniteSimplicialJoin.simplicialJoin (sphereComplex (ds.get i).val) Z) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex (spec i))) :
    FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin (bouquetComplex ds) Z) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex ((List.ofFn spec).flatten)) := by
  let ps := List.ofFn (bouquetJoinPieces ds Z z spec E)
  have hd : ps.Pairwise (fun P Q => P.complex ⊓ Q.complex = vertexComplex none) :=
    List.pairwise_ofFn.mpr (fun i j hij => bouquetMappedIntersection ds i j (ne_of_lt hij))
  let F := vertexFamilyJoinBased Z z (none : BouquetVertices ds) ps hd
  let e := Homeomorph.setCongr (congrArg
    (fun K => FiniteConeCollapse.realization (FiniteSimplicialJoin.simplicialJoin K Z))
    (bouquetJoinFamilyComplex ds Z z spec E).symm)
  have hs : ps.flatMap (·.spec) = (List.ofFn spec).flatten := by
    simp only [ps, List.flatMap_def, List.map_ofFn]
    rfl
  exact e.toHomotopyEquiv.trans ((basedOrdinary F).trans (bouquetListCast hs).toHomotopyEquiv)

end BouquetJoinAssembly

section BouquetPairJoin

private def sphereBouquetJoinSpec (p : ℕ) (ds : BouquetSpec) : BouquetSpec :=
  (List.ofFn (fun i : Fin ds.length => [⟨p + (ds.get i).val + 1, by omega⟩])).flatten

private def sphereBouquetJoinNormalization (p : ℕ) (ds : BouquetSpec) :
    FiniteSimplicialJoin.Space
      (FiniteSimplicialJoin.simplicialJoin (sphereComplex p) (bouquetComplex ds)) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex (sphereBouquetJoinSpec p ds)) := by
  let spec : Fin ds.length → BouquetSpec := fun i => [⟨p + (ds.get i).val + 1, by omega⟩]
  let E := fun i : Fin ds.length =>
    (spherePairJoinNormalization (ds.get i).val p).trans
      (bouquetListCast (show [⟨(ds.get i).val + p + 1, by omega⟩] = spec i by
        congr 1
        apply Subtype.ext
        change (ds.get i).val + p + 1 = p + (ds.get i).val + 1
        omega)).toHomotopyEquiv
  exact (nativeJoinSymmetry (sphereComplex p) (bouquetComplex ds)
    ⟨spherePoint p⟩ ⟨bouquetPoint ds⟩).toHomotopyEquiv.trans
    (bouquetFamilyJoinNormalization ds (sphereComplex p) (spherePoint p) spec E)

private def bouquetPairJoinSpec (ds es : BouquetSpec) : BouquetSpec :=
  (List.ofFn (fun i : Fin ds.length => sphereBouquetJoinSpec (ds.get i).val es)).flatten

private def bouquetPairJoinNormalization (ds es : BouquetSpec) :
    FiniteSimplicialJoin.Space
      (FiniteSimplicialJoin.simplicialJoin (bouquetComplex ds) (bouquetComplex es)) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex (bouquetPairJoinSpec ds es)) :=
  bouquetFamilyJoinNormalization ds (bouquetComplex es) (bouquetPoint es)
    (fun i => sphereBouquetJoinSpec (ds.get i).val es)
    (fun i => sphereBouquetJoinNormalization (ds.get i).val es)

private def bouquetSuspensionSpec (ds : BouquetSpec) : BouquetSpec :=
  (List.ofFn (fun i : Fin ds.length => [⟨(ds.get i).val + 1, by omega⟩])).flatten

private def bouquetSuspensionNormalization (ds : BouquetSpec) :
    FiniteSimplicialJoin.Space (nativeSuspensionComplex (bouquetComplex ds)) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex (bouquetSuspensionSpec ds)) :=
  bouquetFamilyJoinNormalization ds twoPoints (twoPoint true)
    (fun i => [⟨(ds.get i).val + 1, by omega⟩])
    (fun i => spherePairJoinNormalization (ds.get i).val 0)

private def twoPointSuspensionNormalization :
    SingletonRetractionBasedInverse.BasedEquivalence
      (nativeSuspensionPoint twoPoints) (bouquetPoint [⟨1, by omega⟩]) :=
  nativeBouquetNormalization (nativeSuspensionComplex twoPoints) (Sum.inr true)
    (join_right_vertex twoPoints twoPoints true (twoPoints_singleton true))
    [⟨1, by omega⟩] (sphereSingletonBouquetHomeomorph ⟨1, by omega⟩).toHomotopyEquiv

end BouquetPairJoin

section NormalComponentJoinAssembly

private def normalComponentEmbedding (m : ℕ) (p : Fin m → BouquetSpec) (i : Fin m) :
    BouquetVertices (p i) ↪ NormalVertices m p where
  toFun v := (⟨i, v⟩ : NormalVertices m p)
  inj' := fun _ _ h => (@sigma_mk_injective (Fin m) (fun i => BouquetVertices (p i)) i) h


private theorem normalMappedIntersection {m : ℕ} (p : Fin m → BouquetSpec)
    (i j : Fin m) (hij : i ≠ j) :
    (bouquetComplex (p i)).map (normalComponentEmbedding m p i) ⊓
      (bouquetComplex (p j)).map (normalComponentEmbedding m p j) = ⊥ := by
  apply le_antisymm _ bot_le
  intro s hs
  obtain ⟨u, hu⟩ := (((bouquetComplex (p i)).map (normalComponentEmbedding m p i)).isRelLowerSet_faces hs.1).1
  obtain ⟨A, hA, hAi⟩ := hs.1
  obtain ⟨B, hB, hBj⟩ := hs.2
  obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp (hAi.symm ▸ hu)
  obtain ⟨w, hw, hwj⟩ := Finset.mem_image.mp (hBj.symm ▸ hu)
  exact (hij (congrArg Sigma.fst (hvi.trans hwj.symm))).elim

private def normalJoinPieces {W : Type*} [Fintype W] [DecidableEq W]
    (m : ℕ) (p : Fin m → BouquetSpec) (Z : PreAbstractSimplicialComplex W)
    (b : W) (hb : ({b} : Finset W) ∈ Z) (spec : Fin m → BouquetSpec)
    (E : ∀ i, FiniteSimplicialJoin.Space
      (FiniteSimplicialJoin.simplicialJoin (bouquetComplex (p i)) Z) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex (spec i)))
    (i : Fin m) : NormalizedJoinPiece (V := NormalVertices m p) Z b hb where
  complex := (bouquetComplex (p i)).map (normalComponentEmbedding m p i)
  vertex := ⟨i, none⟩
  vertex_face := mappedVertexFace (bouquetComplex (p i))
    (normalComponentEmbedding m p i) none (bouquetVertex_face (p i))
  spec := spec i
  normalization := nativeBouquetNormalization _ _ _ (spec i)
    ((nativeJoinCongr _ Z (bouquetComplex (p i)) Z
      ⟨FiniteVertexCylinder.vertexPoint _ ⟨i, none⟩
        (mappedVertexFace (bouquetComplex (p i)) (normalComponentEmbedding m p i)
          none (bouquetVertex_face (p i)))⟩
      ⟨FiniteVertexCylinder.vertexPoint Z b hb⟩ ⟨bouquetPoint (p i)⟩
      ⟨FiniteVertexCylinder.vertexPoint Z b hb⟩
      (coordinateHomeomorph (bouquetComplex (p i)) (normalComponentEmbedding m p i)).symm.toHomotopyEquiv
      (HomotopyEquiv.refl _)).trans (E i))

private theorem normalJoinFamilyComplex {W : Type*} [Fintype W] [DecidableEq W]
    (m : ℕ) (p : Fin m → BouquetSpec) (Z : PreAbstractSimplicialComplex W)
    (b : W) (hb : ({b} : Finset W) ∈ Z) (spec : Fin m → BouquetSpec)
    (E : ∀ i, FiniteSimplicialJoin.Space
      (FiniteSimplicialJoin.simplicialJoin (bouquetComplex (p i)) Z) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex (spec i))) :
    unionList ((List.ofFn (normalJoinPieces m p Z b hb spec E)).map (·.complex)) = normalComplex m p := by
  apply SetLike.ext
  intro s
  rw [mem_unionList]
  change _ ↔ s ∈ coproductComplex (fun i => bouquetComplex (p i))
  rw [mem_coproductComplex]
  constructor
  · rintro ⟨J, hJ, hs⟩
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hJ
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
    exact ⟨i, hs⟩
  · rintro ⟨i, hs⟩
    exact ⟨_, List.mem_map.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩, hs⟩

private theorem familyJoinSpec_eq {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {Z : PreAbstractSimplicialComplex W} {b : W} {hb : ({b} : Finset W) ∈ Z}
    (es : BouquetSpec) (ps : List (NormalizedJoinPiece (V := V) Z b hb)) (hne : ps ≠ []) :
    familyJoinSpec es ps = ps.flatMap (·.spec) ++ (List.replicate (ps.length - 1) es).flatten := by
  induction ps with
  | nil => exact False.elim (hne rfl)
  | cons P ps ih =>
    cases ps with
    | nil => simp [familyJoinSpec]
    | cons Q qs =>
      rw [familyJoinSpec, ih (by simp)]
      simp only [List.flatMap_cons, List.length_cons, Nat.add_sub_cancel,
        List.replicate_succ', List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_nil, List.append_assoc]

private def normalFamilyJoinNormalization {W : Type*} [Fintype W] [DecidableEq W]
    (m : ℕ) (hm : 0 < m) (p : Fin m → BouquetSpec) (Z : PreAbstractSimplicialComplex W)
    (b : W) (hb : ({b} : Finset W) ∈ Z) (spec : Fin m → BouquetSpec)
    (E : ∀ i, FiniteSimplicialJoin.Space
      (FiniteSimplicialJoin.simplicialJoin (bouquetComplex (p i)) Z) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex (spec i)))
    (es : BouquetSpec) (S : SingletonRetractionBasedInverse.BasedEquivalence
      (nativeSuspensionPoint Z) (bouquetPoint es)) :
    FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin (normalComplex m p) Z) ≃ₕ
      FiniteSimplicialJoin.Space
        (bouquetComplex ((List.ofFn spec).flatten ++ (List.replicate (m - 1) es).flatten)) := by
  let ps := List.ofFn (normalJoinPieces m p Z b hb spec E)
  have hne : ps ≠ [] := by intro h; have := congrArg List.length h; simp [ps] at this; omega
  have hd : ps.Pairwise (fun P Q => P.complex ⊓ Q.complex = ⊥) :=
    List.pairwise_ofFn.mpr (fun i j hij => normalMappedIntersection p i j (ne_of_lt hij))
  let F := familyJoinBased Z b hb es S ps hne hd
  let e := Homeomorph.setCongr (congrArg
    (fun K => FiniteConeCollapse.realization (FiniteSimplicialJoin.simplicialJoin K Z))
    (normalJoinFamilyComplex m p Z b hb spec E).symm)
  have hs : familyJoinSpec es ps =
      (List.ofFn spec).flatten ++ (List.replicate (m - 1) es).flatten := by
    rw [familyJoinSpec_eq es ps hne]
    simp only [ps, List.flatMap_def, List.map_ofFn, List.length_ofFn]
    rfl
  exact e.toHomotopyEquiv.trans ((basedOrdinary F).trans (bouquetListCast hs).toHomotopyEquiv)

end NormalComponentJoinAssembly

private instance normalJoinDecidableEq (m : ℕ) (p : Fin m → BouquetSpec)
    (n : ℕ) (q : Fin n → BouquetSpec) :
    DecidableEq (NormalVertices m p ⊕ NormalVertices n q) := by
  letI : DecidableEq (NormalVertices m p) := inferInstance
  letI : DecidableEq (NormalVertices n q) := inferInstance
  infer_instance

section NormalJoinConstruction

private def normalSuspensionSpec (n : ℕ) (q : Fin n → BouquetSpec) : BouquetSpec :=
  (List.ofFn (fun j => bouquetSuspensionSpec (q j))).flatten ++
    (List.replicate (n - 1) [⟨1, by omega⟩]).flatten

private def normalSuspensionNormalization (n : ℕ) (hn : 0 < n) (q : Fin n → BouquetSpec) :
    FiniteSimplicialJoin.Space (nativeSuspensionComplex (normalComplex n q)) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex (normalSuspensionSpec n q)) :=
  normalFamilyJoinNormalization n hn q twoPoints true (twoPoints_singleton true)
    (fun j => bouquetSuspensionSpec (q j)) (fun j => bouquetSuspensionNormalization (q j))
    [⟨1, by omega⟩] twoPointSuspensionNormalization

private def bouquetNormalJoinSpec (ds : BouquetSpec) (n : ℕ) (q : Fin n → BouquetSpec) : BouquetSpec :=
  (List.ofFn (fun j => bouquetPairJoinSpec ds (q j))).flatten ++
    (List.replicate (n - 1) (bouquetSuspensionSpec ds)).flatten

private def bouquetNormalJoinNormalization (ds : BouquetSpec) (n : ℕ)
    (hn : 0 < n) (q : Fin n → BouquetSpec) :
    FiniteSimplicialJoin.Space
      (FiniteSimplicialJoin.simplicialJoin (bouquetComplex ds) (normalComplex n q)) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex (bouquetNormalJoinSpec ds n q)) := by
  let E := fun j : Fin n =>
    (nativeJoinSymmetry (bouquetComplex (q j)) (bouquetComplex ds)
      ⟨bouquetPoint (q j)⟩ ⟨bouquetPoint ds⟩).toHomotopyEquiv.trans
      (bouquetPairJoinNormalization ds (q j))
  let S := nativeBouquetNormalization (nativeSuspensionComplex (bouquetComplex ds))
    (Sum.inr true) (join_right_vertex _ twoPoints true (twoPoints_singleton true))
    (bouquetSuspensionSpec ds) (bouquetSuspensionNormalization ds)
  exact (nativeJoinSymmetry (bouquetComplex ds) (normalComplex n q)
    ⟨bouquetPoint ds⟩ ⟨normalPoint n q ⟨0, hn⟩⟩).toHomotopyEquiv.trans
    (normalFamilyJoinNormalization n hn q (bouquetComplex ds) none (bouquetVertex_face ds)
      (fun j => bouquetPairJoinSpec ds (q j)) E (bouquetSuspensionSpec ds) S)

private def constructedJoinSpec (m : ℕ) (p : Fin m → BouquetSpec)
    (n : ℕ) (q : Fin n → BouquetSpec) : BouquetSpec :=
  (List.ofFn (fun i => bouquetNormalJoinSpec (p i) n q)).flatten ++
    (List.replicate (m - 1) (normalSuspensionSpec n q)).flatten

private def constructedNormalJoinNormalization (m : ℕ) (hm : 0 < m) (p : Fin m → BouquetSpec)
    (n : ℕ) (hn : 0 < n) (q : Fin n → BouquetSpec) :
    FiniteSimplicialJoin.Space
      (FiniteSimplicialJoin.simplicialJoin (normalComplex m p) (normalComplex n q)) ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex (constructedJoinSpec m p n q)) := by
  let S := nativeBouquetNormalization (nativeSuspensionComplex (normalComplex n q))
    (Sum.inr true) (join_right_vertex _ twoPoints true (twoPoints_singleton true))
    (normalSuspensionSpec n q) (normalSuspensionNormalization n hn q)
  exact normalFamilyJoinNormalization m hm p (normalComplex n q) ⟨⟨0, hn⟩, none⟩
    (normalVertex_face n q ⟨0, hn⟩) (fun i => bouquetNormalJoinSpec (p i) n q)
    (fun i => bouquetNormalJoinNormalization (p i) n hn q) (normalSuspensionSpec n q) S

end NormalJoinConstruction

section BouquetMultiplicityReindexing

private theorem specFiberCard (ds : BouquetSpec) (d : {n : ℕ // 0 < n}) :
    Fintype.card {i : Fin ds.length // ds.get i = d} = ds.count d := by
  let v : List.Vector {n : ℕ // 0 < n} ds.length := ⟨ds, rfl⟩
  calc
    _ = #{i : Fin ds.length | v.get i = d} := by
      rw [Fintype.card_subtype]
      congr 1
    _ = _ := by
      simpa only [v, List.Vector.toList, List.count, beq_eq_decide] using
        Fin.card_filter_univ_eq_vector_get_eq_count d v

private def specIndexEquiv (ds es : BouquetSpec) (h : ∀ d, ds.count d = es.count d) :
    Fin ds.length ≃ Fin es.length :=
  Equiv.ofFiberEquiv (fun d => Fintype.equivOfCardEq
    ((specFiberCard ds d).trans ((h d).trans (specFiberCard es d).symm)))

private theorem specIndexEquiv_get (ds es : BouquetSpec) (h : ∀ d, ds.count d = es.count d)
    (i : Fin ds.length) : es.get (specIndexEquiv ds es h i) = ds.get i :=
  Equiv.ofFiberEquiv_map _ i

private def sameMultiplicityFamilyHomeomorph (ds es : BouquetSpec)
    (h : ∀ d, ds.count d = es.count d) : SphereFamily ds ≃ₜ SphereFamily es := by
  let e := specIndexEquiv ds es h
  let hd := fun i : Fin ds.length => (congrArg Subtype.val (specIndexEquiv_get ds es h i)).symm
  let f : SphereFamily ds ≃ SphereFamily es :=
    Equiv.sigmaCongr e (fun i => (sphereCast (hd i)).toEquiv)
  letI (i : Fin ds.length) : CompactSpace
      (FiniteSimplicialJoin.Space (sphereComplex (ds.get i).val)) :=
    FiniteSimplicialJoin.realizationCompactSpace _
  apply Continuous.homeoOfEquivCompactToT2 (f := f)
  apply continuous_sigma
  intro i
  exact (@continuous_sigmaMk _ (fun j : Fin es.length =>
    FiniteSimplicialJoin.Space (sphereComplex (es.get j).val)) _ (e i)).comp
    (sphereCast (hd i)).continuous

private theorem sameMultiplicityFamily_base (ds es : BouquetSpec)
    (h : ∀ d, ds.count d = es.count d) (z : SphereFamily ds) :
    (sameMultiplicityFamilyHomeomorph ds es h z).2 =
      spherePoint (es.get (sameMultiplicityFamilyHomeomorph ds es h z).1).val ↔
      z.2 = spherePoint (ds.get z.1).val := by
  rcases z with ⟨i, x⟩
  let hd := (congrArg Subtype.val (specIndexEquiv_get ds es h i)).symm
  change sphereCast hd x = spherePoint _ ↔ x = spherePoint _
  rw [← sphereCast_point hd]
  exact (sphereCast hd).injective.eq_iff

private def sameMultiplicityBouquetHomeomorph (ds es : BouquetSpec)
    (h : ∀ d, ds.count d = es.count d) :
    FiniteSimplicialJoin.Space (bouquetComplex ds) ≃ₜ
      FiniteSimplicialJoin.Space (bouquetComplex es) := by
  let e := (Homeomorph.refl PUnit.{1}).sumCongr (sameMultiplicityFamilyHomeomorph ds es h)
  let q : CoordinateBouquetQuotient ds ≃ₜ CoordinateBouquetQuotient es :=
    Homeomorph.Quotient.congr e (by
      intro z w
      have hb (z : BouquetSource ds) : e z ∈ bouquetBases es ↔ z ∈ bouquetBases ds := by
        rcases z with u | z
        · rfl
        · exact sameMultiplicityFamily_base ds es h z
      change (z = w ∨ (_ ∧ _)) ↔ (e z = e w ∨ (_ ∧ _))
      rw [e.injective.eq_iff, hb, hb])
  exact ((bouquetQuotientHomeomorph ds).symm.trans q).trans (bouquetQuotientHomeomorph es)

end BouquetMultiplicityReindexing

end D5.S3.Geometry.FiniteComponentClosure
