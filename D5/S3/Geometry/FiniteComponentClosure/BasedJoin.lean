/- GID: D5/S3/Geometry/FiniteComponentClosure/BasedJoin
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteComponentClosure/BasedJoin
   mirror-E: none(waiver:finite-component-closure)
   anchors: [mathlib/module/Mathlib.Topology.Homeomorph.Quotient]
   utility: none
   digest: Based cone collapse, native suspension, and finite-family join assembly. -/
import D5.S3.Geometry.FiniteComponentClosure.SelectedWedge

noncomputable section
open Set Finset Topology ContinuousMap
open scoped BigOperators unitInterval

namespace D5.S3.Geometry.FiniteComponentClosure

open private
  D5.S3.Geometry.FiniteComponentClosure.joinHomeomorph
  D5.S3.Geometry.FiniteComponentClosure.coneHeight
  D5.S3.Geometry.FiniteComponentClosure.coneBaseSuspensionHomeomorph
  D5.S3.Geometry.FiniteComponentClosure.coneBase_north
  D5.S3.Geometry.FiniteComponentClosure.twoPoints_singleton
  D5.S3.Geometry.FiniteComponentClosure.twoPoint
  D5.S3.Geometry.FiniteComponentClosure.twoPoints_exhaust
  D5.S3.Geometry.FiniteComponentClosure.nativeCylinder
  D5.S3.Geometry.FiniteComponentClosure.coordinateLinear_single
  from D5.S3.Geometry.FiniteComponentClosure.Transport

open private
  D5.S3.Geometry.FiniteComponentClosure.vertexComplex
  D5.S3.Geometry.FiniteComponentClosure.bouquetVertex_face
  D5.S3.Geometry.FiniteComponentClosure.bouquetPath
  D5.S3.Geometry.FiniteComponentClosure.glueLeft
  D5.S3.Geometry.FiniteComponentClosure.vertexGluingHomeomorph
  from D5.S3.Geometry.FiniteComponentClosure.Models

open private
  D5.S3.Geometry.FiniteComponentClosure.wedgeSubsingletonHomeomorph
  D5.S3.Geometry.FiniteComponentClosure.finiteConeCover
  D5.S3.Geometry.FiniteComponentClosure.join_left_vertex
  D5.S3.Geometry.FiniteComponentClosure.join_right_vertex
  D5.S3.Geometry.FiniteComponentClosure.join_mono_left
  D5.S3.Geometry.FiniteComponentClosure.vertexComplex_le
  D5.S3.Geometry.FiniteComponentClosure.join_union
  D5.S3.Geometry.FiniteComponentClosure.disjoint_join_overlap
  D5.S3.Geometry.FiniteComponentClosure.join_vertex_cone
  D5.S3.Geometry.FiniteComponentClosure.nativeConeHomeomorph
  D5.S3.Geometry.FiniteComponentClosure.nativeCone_base
  D5.S3.Geometry.FiniteComponentClosure.nativeConeBaseHomeomorph
  D5.S3.Geometry.FiniteComponentClosure.realization_pullback_intersection
  D5.S3.Geometry.FiniteComponentClosure.join_intersection
  from D5.S3.Geometry.FiniteComponentClosure.ConeSplits

open private
  D5.S3.Geometry.FiniteComponentClosure.bouquetAppendHomeomorph
  D5.S3.Geometry.FiniteComponentClosure.vertexWedge_vertex
  from D5.S3.Geometry.FiniteComponentClosure.SelectedWedge

section BasedComposition

private def relativePrecompose {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {a : X} {b : Y} {f g : C(Y, Z)}
    (H : f.HomotopyRel g {b}) (u : C(X, Y)) (hu : u a = b) :
    (f.comp u).HomotopyRel (g.comp u) {a} where
  toHomotopy := H.toHomotopy.compContinuousMap u
  prop' := by
    intro t x hx
    have hx' : x = a := Set.mem_singleton_iff.mp hx
    subst x
    change H (t, u a) = f (u a)
    rw [hu]
    exact H.eq_fst t (by simp)

private def basedSymm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (E : SingletonRetractionBasedInverse.BasedEquivalence x y) :
    SingletonRetractionBasedInverse.BasedEquivalence y x where
  forward := E.backward
  backward := E.forward
  forward_point := E.backward_point
  backward_point := E.forward_point
  left := E.right
  right := E.left

private def basedTrans {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {x : X} {y : Y} {z : Z}
    (E : SingletonRetractionBasedInverse.BasedEquivalence x y)
    (F : SingletonRetractionBasedInverse.BasedEquivalence y z) :
    SingletonRetractionBasedInverse.BasedEquivalence x z where
  forward := F.forward.comp E.forward
  backward := E.backward.comp F.backward
  forward_point := by change F.forward (E.forward x) = z; rw [E.forward_point, F.forward_point]
  backward_point := by change E.backward (F.backward z) = x; rw [F.backward_point, E.backward_point]
  left := ((relativePrecompose F.left E.forward E.forward_point).compContinuousMap
    E.backward).trans E.left
  right := ((relativePrecompose E.right F.backward F.backward_point).compContinuousMap
    F.forward).trans F.right

private def basedHomeomorphism {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) (y : Y) (h : e x = y) :
    SingletonRetractionBasedInverse.BasedEquivalence x y where
  forward := ⟨e, e.continuous⟩
  backward := ⟨e.symm, e.symm.continuous⟩
  forward_point := h
  backward_point := by change e.symm y = x; rw [← h, e.symm_apply_apply]
  left := (HomotopyRel.refl (ContinuousMap.id X) {x}).cast
    (by ext z; exact (e.symm_apply_apply z).symm) rfl
  right := (HomotopyRel.refl (ContinuousMap.id Y) {y}).cast
    (by ext z; exact (e.apply_symm_apply z).symm) rfl

end BasedComposition

section CollapsedBaseTransport

/-- Transport along a collapsed basepoint trace keeps the forward map unchanged. -/
private def collapsedRebase {X Q : Type*} [TopologicalSpace X] [T1Space X]
    [TopologicalSpace Q] (z a : X) (o : Q)
    (Rz : SingletonRetractionBasedInverse.CylinderRetraction z)
    (Ra : SingletonRetractionBasedInverse.CylinderRetraction a)
    (E : SingletonRetractionBasedInverse.BasedEquivalence a o)
    (γ : Path z a) (hγ : ∀ t, E.forward (γ t) = o) :
    SingletonRetractionBasedInverse.BasedEquivalence z o := by
  let existence := SingletonRetractionBasedInverse.based_inverse z a Rz Ra
    (ContinuousMap.id X) (ContinuousMap.id X)
    (Homotopy.refl (ContinuousMap.id X)) (Homotopy.refl (ContinuousMap.id X)) γ
  let U := Classical.choose existence
  let L := Classical.choose (Classical.choose_spec existence)
  have hL : ∀ t, L (t, z) = γ t := Classical.choose_spec (Classical.choose_spec existence)
  let q := E.forward
  let s := E.backward
  let u := U.forward
  let v := U.backward
  have hqz : q z = o := by simpa [q] using hγ 0
  let A₁ : ((v.comp s).comp q).HomotopyRel (((v.comp s).comp q).comp u) {z} := {
    toHomotopy := (Homotopy.refl ((v.comp s).comp q)).comp L
    prop' := by
      intro t x hx
      have hx' : x = z := Set.mem_singleton_iff.mp hx
      subst x
      change v (s (q (L (t, z)))) = v (s (q z))
      rw [hL, hγ, hqz] }
  let A₂ : (((v.comp s).comp q).comp u).HomotopyRel (v.comp u) {z} := {
    toHomotopy := (Homotopy.refl v).comp (E.left.toHomotopy.compContinuousMap u)
    prop' := by
      intro t x hx
      have hx' : x = z := Set.mem_singleton_iff.mp hx
      subst x
      change v (E.left (t, u z)) = v (s (q (u z)))
      rw [show u z = a from U.forward_point, E.left.eq_fst t (by simp)]
      rfl }
  let B₁ : (q.comp (v.comp s)).HomotopyRel ((q.comp u).comp (v.comp s)) {o} := {
    toHomotopy := (Homotopy.refl q).comp (L.compContinuousMap (v.comp s))
    prop' := by
      intro t y hy
      have hy' : y = o := Set.mem_singleton_iff.mp hy
      subst y
      change q (L (t, v (s o))) = q (v (s o))
      rw [show s o = a from E.backward_point, show v a = z from U.backward_point,
        hL, hγ, hqz] }
  let B₂ : ((q.comp u).comp (v.comp s)).HomotopyRel (q.comp s) {o} := {
    toHomotopy := (Homotopy.refl q).comp (U.right.toHomotopy.compContinuousMap s)
    prop' := by
      intro t y hy
      have hy' : y = o := Set.mem_singleton_iff.mp hy
      subst y
      change q (U.right (t, s o)) = q (u (v (s o)))
      rw [show s o = a from E.backward_point, U.right.eq_fst t (by simp)]
      rfl }
  exact {
    forward := q
    backward := v.comp s
    forward_point := hqz
    backward_point := by
      change v (s o) = z
      rw [show s o = a from E.backward_point]
      exact U.backward_point
    left := (A₁.trans A₂).trans U.left
    right := (B₁.trans B₂).trans E.right }

end CollapsedBaseTransport

section NativeConeBaseTransport

private theorem coneVertexSegment_mem {V : Type*} [Fintype V] [DecidableEq V]
    (P : FiniteConeCollapse.ConePair V) (z : V) (hz : ({z} : Finset V) ∈ P.cone) (t : I) :
    (1 - (t : ℝ)) • Pi.single z (1 : ℝ) + (t : ℝ) • Pi.single P.apex (1 : ℝ) ∈
      FiniteConeCollapse.realization P.cone := by
  refine ⟨insert P.apex {z}, P.cone_face {z} hz, ?_⟩
  let S := (fun v : V => Pi.single v (1 : ℝ)) '' ((insert P.apex ({z} : Finset V)) : Set V)
  have hzmem : Pi.single z (1 : ℝ) ∈ convexHull ℝ S :=
    subset_convexHull ℝ S ⟨z, by simp, rfl⟩
  have hamem : Pi.single P.apex (1 : ℝ) ∈ convexHull ℝ S :=
    subset_convexHull ℝ S ⟨P.apex, by simp, rfl⟩
  simpa only [S, Finset.coe_insert, Finset.coe_singleton] using
    (convex_convexHull ℝ S) hzmem hamem
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring)

private def coneVertexPath {V : Type*} [Fintype V] [DecidableEq V]
    (P : FiniteConeCollapse.ConePair V) (z : V) (hz : ({z} : Finset V) ∈ P.cone) :
    Path (FiniteVertexCylinder.vertexPoint P.ambient z (P.inclusion hz)) P.apexPoint where
  toFun t := ⟨(1 - (t : ℝ)) • Pi.single z 1 + (t : ℝ) • Pi.single P.apex 1, by
    obtain ⟨s, hs, hv⟩ := coneVertexSegment_mem P z hz t
    exact ⟨s, P.inclusion hs, hv⟩⟩
  continuous_toFun := by apply Continuous.subtype_mk; fun_prop
  source' := by apply Subtype.ext; simp [FiniteVertexCylinder.vertexPoint]
  target' := by apply Subtype.ext; simp [FiniteConeCollapse.ConePair.apexPoint]

/-- The original finite-cone quotient map, rebased at any actual vertex of the cone. -/
private def nativeConeRebasedCollapse {V : Type*} [Fintype V] [DecidableEq V]
    (P : FiniteConeCollapse.ConePair V) (z : V) (hz : ({z} : Finset V) ∈ P.cone) :
    SingletonRetractionBasedInverse.BasedEquivalence
      (FiniteVertexCylinder.vertexPoint P.ambient z (P.inclusion hz))
      (P.quotientMap P.apexPoint) := by
  let E : SingletonRetractionBasedInverse.BasedEquivalence
      P.apexPoint (P.quotientMap P.apexPoint) := {
    forward := P.quotientMap
    backward := P.collapseInverse
    forward_point := rfl
    backward_point := (P.basedCollapse.1.fst_eq_snd (by simp)).symm
    left := P.basedCollapse.1.symm
    right := P.basedCollapse.2.symm }
  apply collapsedRebase _ _ _ (nativeCylinder P.ambient z (P.inclusion hz))
    (nativeCylinder P.ambient P.apex (P.inclusion P.apex_face)) E (coneVertexPath P z hz)
  intro t
  apply Quotient.sound
  apply Or.inr
  constructor
  · exact coneVertexSegment_mem P z hz t
  · exact ⟨{P.apex}, P.apex_face, subset_convexHull ℝ _ ⟨P.apex, by simp, rfl⟩⟩

end NativeConeBaseTransport

section BasedConeCovers

private abbrev collapseOf {V : Type*} [Fintype V] [DecidableEq V]
    (X C : PreAbstractSimplicialComplex V) :=
  FiniteConeUnionWedge.Collapse
    {x : FiniteSimplicialJoin.Space X | x.val ∈ FiniteConeCollapse.realization C}

private def collapseVertex {V : Type*} [Fintype V] [DecidableEq V]
    (X C : PreAbstractSimplicialComplex V) (z : V) (hz : ({z} : Finset V) ∈ X) :
    collapseOf X C := Quotient.mk _ (FiniteVertexCylinder.vertexPoint X z hz)

private def wedgePoint {X Y : Type*} (x : X) (y : Y) :
    FiniteConeUnionWedge.Wedge x y := Quotient.mk _ (Sum.inl x)

/-- The cover quotient and the cone collapse share the chosen native cone vertex. -/
private def coneCoverBased {V : Type*} [Fintype V] [DecidableEq V]
    (X Y C : PreAbstractSimplicialComplex V) (a z : V)
    (hzX : ({z} : Finset V) ∈ X) (hzY : ({z} : Finset V) ∈ Y)
    (haC : ({a} : Finset V) ∈ C) (hzC : ({z} : Finset V) ∈ C)
    (hC : C ≤ X ⊔ Y) (hXY : X ⊓ Y ≤ C)
    (hcone : ∀ s ∈ C, insert a s ∈ C) :
    SingletonRetractionBasedInverse.BasedEquivalence
      (FiniteVertexCylinder.vertexPoint (X ⊔ Y) z (Or.inl hzX))
      (wedgePoint (collapseVertex X C z hzX) (collapseVertex Y C z hzY)) := by
  let Q : FiniteConeCollapse.ConePair V := ⟨X ⊔ Y, C, hC, a, haC, hcone⟩
  let P := finiteConeCover X Y C z z hzX hzY hzC hzC hXY
  let e := P.quotientWedgeHomeomorph
  let ω := wedgePoint (collapseVertex X C z hzX) (collapseVertex Y C z hzY)
  have he : e ω = Q.quotientMap Q.apexPoint := by
    change Quotient.mk _ (FiniteVertexCylinder.vertexPoint (X ⊔ Y) z (Or.inl hzX)) =
      Quotient.mk _ Q.apexPoint
    apply Quotient.sound
    exact Or.inr ⟨(FiniteVertexCylinder.vertexPoint C z hzC).property,
      (FiniteVertexCylinder.vertexPoint C a haC).property⟩
  exact basedTrans (nativeConeRebasedCollapse Q z hzC)
    (basedSymm (basedHomeomorphism e ω (Q.quotientMap Q.apexPoint) he))

private def unionConeCollapseBased {V : Type*} [Fintype V] [DecidableEq V]
    (X D : PreAbstractSimplicialComplex V) (a z : V)
    (hzX : ({z} : Finset V) ∈ X) (hzD : ({z} : Finset V) ∈ D)
    (haD : ({a} : Finset V) ∈ D)
    (hcone : ∀ s ∈ D, insert a s ∈ D) :
    SingletonRetractionBasedInverse.BasedEquivalence
      (FiniteVertexCylinder.vertexPoint (X ⊔ D) z (Or.inl hzX))
      (collapseVertex X D z hzX) := by
  letI : Subsingleton (collapseOf D D) := ⟨fun x y =>
    Quotient.inductionOn₂ x y (fun x y => Quotient.sound (Or.inr ⟨x.property, y.property⟩))⟩
  let e := wedgeSubsingletonHomeomorph (collapseVertex X D z hzX) (collapseVertex D D z hzD)
  exact basedTrans
    (coneCoverBased X D D a z hzX hzD haD hzD le_sup_right inf_le_right hcone)
    (basedHomeomorphism e _ _ rfl)

end BasedConeCovers

section BasedAuxiliarySplit

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Two native cone collapses based at the same vertex split the base quotient. -/
private def auxiliaryBasedQuotientSplit
    (N : PreAbstractSimplicialComplex V) (Z : PreAbstractSimplicialComplex W)
    (d : V) (hNd : N ⊓ vertexComplex d = ⊥)
    (v : V) (hv : ({v} : Finset V) ∈ N)
    (b : W) (hb : ({b} : Finset W) ∈ Z) :
    let X := FiniteSimplicialJoin.simplicialJoin N Z
    let D := FiniteSimplicialJoin.simplicialJoin (vertexComplex d) Z
    let C := FiniteSimplicialJoin.simplicialJoin (vertexComplex v) Z
    let B := FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z
    SingletonRetractionBasedInverse.BasedEquivalence
      (collapseVertex X B (Sum.inr b) (join_right_vertex N Z b hb))
      (wedgePoint
        (collapseVertex X C (Sum.inr b) (join_right_vertex N Z b hb))
        (collapseVertex D B (Sum.inr b) (join_right_vertex (vertexComplex d) Z b hb))) := by
  let X := FiniteSimplicialJoin.simplicialJoin N Z
  let D := FiniteSimplicialJoin.simplicialJoin (vertexComplex d) Z
  let C := FiniteSimplicialJoin.simplicialJoin (vertexComplex v) Z
  let B := FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z
  have hCX : C ≤ X := join_mono_left (vertexComplex_le N v hv) Z
  have hXD : X ⊓ D = B := disjoint_join_overlap N (vertexComplex d) Z hNd
  have hdv : vertexComplex d ⊓ vertexComplex v = ⊥ := by
    apply le_antisymm _ bot_le
    intro s hs
    have h : s ∈ N ⊓ vertexComplex d := ⟨vertexComplex_le N v hv hs.2, hs.1⟩
    exact hNd ▸ h
  have hDC : D ⊓ C = B := disjoint_join_overlap _ _ Z hdv
  let eA : collapseOf X D ≃ₜ collapseOf X B :=
    Homeomorph.Quotient.congrRight (by
      intro x y
      have h := realization_pullback_intersection X D B hXD
      change (x = y ∨ (_ ∧ _)) ↔ (x = y ∨ (_ ∧ _))
      rw [h])
  let eD : collapseOf D C ≃ₜ collapseOf D B :=
    Homeomorph.Quotient.congrRight (by
      intro x y
      have h := realization_pullback_intersection D C B hDC
      change (x = y ∨ (_ ∧ _)) ↔ (x = y ∨ (_ ∧ _))
      rw [h])
  let hzX := join_right_vertex N Z b hb
  let hzD := join_right_vertex (vertexComplex d) Z b hb
  let hzC := join_right_vertex (vertexComplex v) Z b hb
  let UA := basedTrans
    (unionConeCollapseBased X D (Sum.inl d) (Sum.inr b) hzX hzD
      (join_left_vertex (vertexComplex d) Z d rfl) (join_vertex_cone Z d))
    (basedHomeomorphism eA (collapseVertex X D (Sum.inr b) hzX)
      (collapseVertex X B (Sum.inr b) hzX) rfl)
  let UW := coneCoverBased X D C (Sum.inl v) (Sum.inr b) hzX hzD
    (join_left_vertex (vertexComplex v) Z v rfl) hzC (hCX.trans le_sup_left)
    (by rw [hXD]; exact join_mono_left bot_le Z) (join_vertex_cone Z v)
  let WD := FiniteConeUnionWedge.basedWedgeEquivalence
    (basedHomeomorphism (Homeomorph.refl (collapseOf X C))
      (collapseVertex X C (Sum.inr b) hzX) _ rfl)
    (basedHomeomorphism eD (collapseVertex D C (Sum.inr b) hzD)
      (collapseVertex D B (Sum.inr b) hzD) rfl)
  exact basedTrans (basedSymm UA) (basedTrans UW WD)

end BasedAuxiliarySplit

section NativeSuspensionPresentation

private def boolTwoPointHomeomorph : Bool ≃ₜ FiniteSimplicialJoin.Space twoPoints := by
  apply Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective twoPoint ⟨?_, ?_⟩) continuous_of_discreteTopology
  · intro x y h
    by_contra hxy
    have hv := congrArg (fun z : FiniteSimplicialJoin.Space twoPoints => z.val x) h
    simpa [twoPoint, FiniteVertexCylinder.vertexPoint, Pi.single_apply, hxy, Ne.symm hxy] using hv
  · intro x
    rcases twoPoints_exhaust x with h | h
    · exact ⟨true, h.symm⟩
    · exact ⟨false, h.symm⟩

private def nativeSuspensionComplex {W : Type*} [DecidableEq W]
    (Z : PreAbstractSimplicialComplex W) :=
  FiniteSimplicialJoin.simplicialJoin Z twoPoints

private def nativeSuspensionPoint {W : Type*} [Fintype W] [DecidableEq W]
    (Z : PreAbstractSimplicialComplex W) :
    FiniteSimplicialJoin.Space (nativeSuspensionComplex Z) :=
  FiniteVertexCylinder.vertexPoint _ (Sum.inr true)
    (join_right_vertex Z twoPoints true (twoPoints_singleton true))

private def nativeConeSuspensionHomeomorph {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (Z : PreAbstractSimplicialComplex W) (d : V) (b : W)
    (hb : ({b} : Finset W) ∈ Z) :
    collapseOf (FiniteSimplicialJoin.simplicialJoin (vertexComplex d) Z)
      (FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z) ≃ₜ
      FiniteSimplicialJoin.Space (nativeSuspensionComplex Z) :=
  ((nativeConeBaseHomeomorph Z d (FiniteVertexCylinder.vertexPoint Z b hb)).trans
    (joinHomeomorph (Homeomorph.refl _) boolTwoPointHomeomorph)).trans
    (FiniteSimplicialJoin.joinHomeomorph Z twoPoints
      ⟨FiniteVertexCylinder.vertexPoint Z b hb⟩ ⟨twoPoint true⟩)

private theorem nativeConeSuspension_base {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (Z : PreAbstractSimplicialComplex W) (d : V) (b : W)
    (hb : ({b} : Finset W) ∈ Z) :
    nativeConeSuspensionHomeomorph Z d b hb
      (collapseVertex (FiniteSimplicialJoin.simplicialJoin (vertexComplex d) Z)
        (FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z)
        (Sum.inr b) (join_right_vertex (vertexComplex d) Z b hb)) =
      nativeSuspensionPoint Z := by
  let z := FiniteVertexCylinder.vertexPoint Z b hb
  let x := FiniteVertexCylinder.vertexPoint
    (FiniteSimplicialJoin.simplicialJoin (vertexComplex d) Z) (Sum.inr b)
    (join_right_vertex (vertexComplex d) Z b hb)
  have hx : coneHeight (nativeConeHomeomorph Z d z x) = 1 :=
    (nativeCone_base Z d z x).mp
      (FiniteVertexCylinder.vertexPoint
        (FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z)
        (Sum.inr b) (join_right_vertex ⊥ Z b hb)).property
  have hn := coneBase_north (nativeConeHomeomorph Z d z x) hx z
  change (FiniteSimplicialJoin.joinHomeomorph Z twoPoints ⟨z⟩ ⟨twoPoint true⟩)
    ((joinHomeomorph (Homeomorph.refl _) boolTwoPointHomeomorph)
      (coneBaseSuspensionHomeomorph (Quotient.mk _ (nativeConeHomeomorph Z d z x)))) = _
  rw [hn]
  apply Subtype.ext
  change FiniteSimplicialJoin.representative Z twoPoints (z, twoPoint true, (1 : I)) =
    Pi.single (Sum.inr true) 1
  ext w
  cases w <;>
    simp [FiniteSimplicialJoin.representative, twoPoint, FiniteVertexCylinder.vertexPoint,
      Pi.single_apply]

private def nativeConeCollapseAtVertex {V : Type*} [Fintype V] [DecidableEq V]
    (P : FiniteConeCollapse.ConePair V) (z : V) (hz : ({z} : Finset V) ∈ P.cone) :
    SingletonRetractionBasedInverse.BasedEquivalence
      (FiniteVertexCylinder.vertexPoint P.ambient z (P.inclusion hz))
      (collapseVertex P.ambient P.cone z (P.inclusion hz)) := by
  exact basedTrans (nativeConeRebasedCollapse P z hz)
    (basedHomeomorphism (Homeomorph.refl _) (P.quotientMap P.apexPoint) _
      (Quotient.sound (Or.inr ⟨(FiniteVertexCylinder.vertexPoint P.cone P.apex
        P.apex_face).property, (FiniteVertexCylinder.vertexPoint P.cone z hz).property⟩)))

end NativeSuspensionPresentation

section BasedDisjointJoin

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- The actual two-component join split, with all three native factors based at vertices. -/
private def twoComponentJoinBased
    (M N : PreAbstractSimplicialComplex V) (Z : PreAbstractSimplicialComplex W)
    (hMN : M ⊓ N = ⊥) (a : V) (ha : ({a} : Finset V) ∈ M)
    (v : V) (hv : ({v} : Finset V) ∈ N)
    (b : W) (hb : ({b} : Finset W) ∈ Z) :
    SingletonRetractionBasedInverse.BasedEquivalence
      (FiniteVertexCylinder.vertexPoint (FiniteSimplicialJoin.simplicialJoin (M ⊔ N) Z)
        (Sum.inr b) (join_right_vertex (M ⊔ N) Z b hb))
      (wedgePoint
        (FiniteVertexCylinder.vertexPoint (FiniteSimplicialJoin.simplicialJoin M Z)
          (Sum.inr b) (join_right_vertex M Z b hb))
        (wedgePoint
          (FiniteVertexCylinder.vertexPoint (FiniteSimplicialJoin.simplicialJoin N Z)
            (Sum.inr b) (join_right_vertex N Z b hb))
          (nativeSuspensionPoint Z))) := by
  let X := FiniteSimplicialJoin.simplicialJoin M Z
  let Y := FiniteSimplicialJoin.simplicialJoin N Z
  let C := FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z
  let D := FiniteSimplicialJoin.simplicialJoin (vertexComplex v) Z
  let B := FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z
  have hNa : N ⊓ vertexComplex a = ⊥ := by
    apply le_antisymm _ bot_le
    intro s hs
    have h : s ∈ M ⊓ N := ⟨vertexComplex_le M a ha hs.2, hs.1⟩
    exact hMN ▸ h
  have hYC : Y ⊓ C = B := disjoint_join_overlap N (vertexComplex a) Z hNa
  have hCX : C ≤ X := join_mono_left (vertexComplex_le M a ha) Z
  let hzX := join_right_vertex M Z b hb
  let hzY := join_right_vertex N Z b hb
  let hzC := join_right_vertex (vertexComplex a) Z b hb
  let hzD := join_right_vertex (vertexComplex v) Z b hb
  let PM : FiniteConeCollapse.ConePair (V ⊕ W) :=
    ⟨X, C, hCX, Sum.inl a, join_left_vertex (vertexComplex a) Z a rfl, join_vertex_cone Z a⟩
  let PN : FiniteConeCollapse.ConePair (V ⊕ W) :=
    ⟨Y, D, join_mono_left (vertexComplex_le N v hv) Z, Sum.inl v,
      join_left_vertex (vertexComplex v) Z v rfl, join_vertex_cone Z v⟩
  let eY : collapseOf Y C ≃ₜ collapseOf Y B :=
    Homeomorph.Quotient.congrRight (by
      intro x y
      have h := realization_pullback_intersection Y C B hYC
      change (x = y ∨ (_ ∧ _)) ↔ (x = y ∨ (_ ∧ _))
      rw [h])
  let S := basedHomeomorphism (nativeConeSuspensionHomeomorph Z a b hb)
    (collapseVertex C B (Sum.inr b) hzC) (nativeSuspensionPoint Z)
    (nativeConeSuspension_base Z a b hb)
  let NY := basedTrans
    (basedHomeomorphism eY (collapseVertex Y C (Sum.inr b) hzY)
      (collapseVertex Y B (Sum.inr b) hzY) rfl)
    (basedTrans (auxiliaryBasedQuotientSplit N Z a hNa v hv b hb)
      (FiniteConeUnionWedge.basedWedgeEquivalence
        (basedSymm (nativeConeCollapseAtVertex PN (Sum.inr b) hzD)) S))
  let F := coneCoverBased X Y C (Sum.inl a) (Sum.inr b) hzX hzY
    (join_left_vertex (vertexComplex a) Z a rfl) hzC (hCX.trans le_sup_left)
    (by rw [disjoint_join_overlap M N Z hMN]; exact join_mono_left bot_le Z)
    (join_vertex_cone Z a)
  let pre := basedHomeomorphism
    (Homeomorph.setCongr (congrArg FiniteConeCollapse.realization (join_union M N Z)))
    (FiniteVertexCylinder.vertexPoint (FiniteSimplicialJoin.simplicialJoin (M ⊔ N) Z)
      (Sum.inr b) (join_right_vertex (M ⊔ N) Z b hb))
    (FiniteVertexCylinder.vertexPoint (X ⊔ Y) (Sum.inr b) (Or.inl hzX))
    (Subtype.ext rfl)
  exact basedTrans pre (basedTrans F (FiniteConeUnionWedge.basedWedgeEquivalence
    (basedSymm (nativeConeCollapseAtVertex PM (Sum.inr b) hzC)) NY))

end BasedDisjointJoin

section BasedVertexJoinDistribution

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- Join distribution over a native union at one vertex, with relative inverse homotopies. -/
private def vertexUnionJoinBased
    (M N : PreAbstractSimplicialComplex V) (Z : PreAbstractSimplicialComplex W)
    (a : V) (haM : ({a} : Finset V) ∈ M) (haN : ({a} : Finset V) ∈ N)
    (hMN : M ⊓ N = vertexComplex a) :
    SingletonRetractionBasedInverse.BasedEquivalence
      (FiniteVertexCylinder.vertexPoint (FiniteSimplicialJoin.simplicialJoin (M ⊔ N) Z)
        (Sum.inl a) (join_left_vertex (M ⊔ N) Z a (Or.inl haM)))
      (wedgePoint
        (FiniteVertexCylinder.vertexPoint (FiniteSimplicialJoin.simplicialJoin M Z)
          (Sum.inl a) (join_left_vertex M Z a haM))
        (FiniteVertexCylinder.vertexPoint (FiniteSimplicialJoin.simplicialJoin N Z)
          (Sum.inl a) (join_left_vertex N Z a haN))) := by
  let X := FiniteSimplicialJoin.simplicialJoin M Z
  let Y := FiniteSimplicialJoin.simplicialJoin N Z
  let C := FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z
  let hCX := join_mono_left (vertexComplex_le M a haM) Z
  let hCY := join_mono_left (vertexComplex_le N a haN) Z
  let haX := join_left_vertex M Z a haM
  let haY := join_left_vertex N Z a haN
  let haC := join_left_vertex (vertexComplex a) Z a rfl
  let PM : FiniteConeCollapse.ConePair (V ⊕ W) :=
    ⟨X, C, hCX, Sum.inl a, haC, join_vertex_cone Z a⟩
  let PN : FiniteConeCollapse.ConePair (V ⊕ W) :=
    ⟨Y, C, hCY, Sum.inl a, haC, join_vertex_cone Z a⟩
  let F := coneCoverBased X Y C (Sum.inl a) (Sum.inl a) haX haY haC haC
    (hCX.trans le_sup_left) (by rw [join_intersection, hMN]) (join_vertex_cone Z a)
  let pre := basedHomeomorphism
    (Homeomorph.setCongr (congrArg FiniteConeCollapse.realization (join_union M N Z)))
    (FiniteVertexCylinder.vertexPoint (FiniteSimplicialJoin.simplicialJoin (M ⊔ N) Z)
      (Sum.inl a) (join_left_vertex (M ⊔ N) Z a (Or.inl haM)))
    (FiniteVertexCylinder.vertexPoint (X ⊔ Y) (Sum.inl a) (Or.inl haX))
    (Subtype.ext rfl)
  exact basedTrans pre (basedTrans F (FiniteConeUnionWedge.basedWedgeEquivalence
    (basedSymm (nativeConeCollapseAtVertex PM (Sum.inl a) haC))
    (basedSymm (nativeConeCollapseAtVertex PN (Sum.inl a) haC))))

end BasedVertexJoinDistribution

section NativeBasedNormalization

private def basedOrdinary {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (E : SingletonRetractionBasedInverse.BasedEquivalence x y) : X ≃ₕ Y where
  toFun := E.forward
  invFun := E.backward
  left_inv := ⟨E.left.toHomotopy⟩
  right_inv := ⟨E.right.toHomotopy⟩

private def nativeBouquetNormalization {V : Type*} [Fintype V] [DecidableEq V]
    (K : PreAbstractSimplicialComplex V) (a : V) (ha : ({a} : Finset V) ∈ K)
    (ds : BouquetSpec)
    (e : FiniteSimplicialJoin.Space K ≃ₕ FiniteSimplicialJoin.Space (bouquetComplex ds)) :
    SingletonRetractionBasedInverse.BasedEquivalence
      (FiniteVertexCylinder.vertexPoint K a ha) (bouquetPoint ds) :=
  Classical.choose (SingletonRetractionBasedInverse.based_inverse _ _
    (nativeCylinder K a ha) (nativeCylinder (bouquetComplex ds) none (bouquetVertex_face ds))
    e.toFun e.invFun e.left_inv.some e.right_inv.some
    (bouquetPath ds (e.toFun (FiniteVertexCylinder.vertexPoint K a ha))))

/-- Normalize through a native presentation; no cylinder on the presented space is used. -/
private def normalizeViaNativePresentation {V X : Type*}
    [Fintype V] [DecidableEq V] [TopologicalSpace X]
    (K : PreAbstractSimplicialComplex V) (a : V) (ha : ({a} : Finset V) ∈ K)
    (x : X) (E : SingletonRetractionBasedInverse.BasedEquivalence
      (FiniteVertexCylinder.vertexPoint K a ha) x)
    (ds : BouquetSpec) (e : X ≃ₕ FiniteSimplicialJoin.Space (bouquetComplex ds)) :
    SingletonRetractionBasedInverse.BasedEquivalence x (bouquetPoint ds) :=
  basedTrans (basedSymm E)
    (nativeBouquetNormalization K a ha ds ((basedOrdinary E).trans e))

private def nativeWedgePresentation {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (a : V) (ha : ({a} : Finset V) ∈ K) (b : W) (hb : ({b} : Finset W) ∈ L) :
    SingletonRetractionBasedInverse.BasedEquivalence
      (vertexWedgePoint K L a b ha)
      (wedgePoint (FiniteVertexCylinder.vertexPoint K a ha)
        (FiniteVertexCylinder.vertexPoint L b hb)) := by
  let e := vertexGluingHomeomorph K L a b ha hb
  have he : e (wedgePoint (FiniteVertexCylinder.vertexPoint K a ha)
      (FiniteVertexCylinder.vertexPoint L b hb)) = vertexWedgePoint K L a b ha := by
    apply Subtype.ext
    exact coordinateLinear_single (glueLeft a b) a
  exact basedSymm (basedHomeomorphism e _ _ he)

private def basedBouquetAppend (ds es : BouquetSpec) :
    SingletonRetractionBasedInverse.BasedEquivalence
      (wedgePoint (bouquetPoint ds) (bouquetPoint es)) (bouquetPoint (ds ++ es)) :=
  normalizeViaNativePresentation
    (vertexWedgeComplex (bouquetComplex ds) (bouquetComplex es) none none)
    (Quotient.mk _ (Sum.inl none))
    (vertexWedge_vertex (bouquetComplex ds) (bouquetComplex es) none none (bouquetVertex_face ds))
    _ (nativeWedgePresentation (bouquetComplex ds) (bouquetComplex es)
      none (bouquetVertex_face ds) none (bouquetVertex_face es))
    (ds ++ es) (bouquetAppendHomeomorph ds es).toHomotopyEquiv

end NativeBasedNormalization

section FiniteFamilyJoinAssembly

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

private structure NormalizedJoinPiece (Z : PreAbstractSimplicialComplex W)
    (b : W) (hb : ({b} : Finset W) ∈ Z) where
  complex : PreAbstractSimplicialComplex V
  vertex : V
  vertex_face : ({vertex} : Finset V) ∈ complex
  spec : BouquetSpec
  normalization : SingletonRetractionBasedInverse.BasedEquivalence
    (FiniteVertexCylinder.vertexPoint (FiniteSimplicialJoin.simplicialJoin complex Z)
      (Sum.inr b) (join_right_vertex complex Z b hb)) (bouquetPoint spec)

private def unionList (ps : List (PreAbstractSimplicialComplex V)) :
    PreAbstractSimplicialComplex V := ps.foldr (· ⊔ ·) ⊥

private theorem mem_unionList (ps : List (PreAbstractSimplicialComplex V)) (s : Finset V) :
    s ∈ unionList ps ↔ ∃ P ∈ ps, s ∈ P := by
  induction ps with
  | nil =>
    constructor
    · intro h; exact False.elim h
    · rintro ⟨P, hP, _⟩; cases hP
  | cons P ps ih =>
    change (s ∈ P ∨ s ∈ unionList ps) ↔ _
    simp only [ih, List.mem_cons, exists_eq_or_imp]

private def familyJoinSpec (es : BouquetSpec) {Z : PreAbstractSimplicialComplex W}
    {b : W} {hb : ({b} : Finset W) ∈ Z} : List (NormalizedJoinPiece (V := V) Z b hb) → BouquetSpec
  | [] => []
  | [P] => P.spec
  | P :: Q :: ps => P.spec ++ (familyJoinSpec es (Q :: ps) ++ es)

/-- Assemble finitely many disjoint native components, retaining one suspension per extra component. -/
private def familyJoinBased (Z : PreAbstractSimplicialComplex W) (b : W)
    (hb : ({b} : Finset W) ∈ Z) (es : BouquetSpec)
    (S : SingletonRetractionBasedInverse.BasedEquivalence
      (nativeSuspensionPoint Z) (bouquetPoint es))
    (ps : List (NormalizedJoinPiece (V := V) Z b hb)) :
    (hne : ps ≠ []) →
    (hd : ps.Pairwise (fun P Q => P.complex ⊓ Q.complex = ⊥)) →
    SingletonRetractionBasedInverse.BasedEquivalence
      (FiniteVertexCylinder.vertexPoint
        (FiniteSimplicialJoin.simplicialJoin (unionList (ps.map (·.complex))) Z)
        (Sum.inr b) (join_right_vertex _ Z b hb)) (bouquetPoint (familyJoinSpec es ps)) := by
  induction ps with
  | nil => intro hne; exact False.elim (hne rfl)
  | cons P ps ih =>
    intro hne hd
    cases ps with
    | nil =>
      let e := Homeomorph.setCongr (congrArg FiniteConeCollapse.realization
        (show FiniteSimplicialJoin.simplicialJoin
          (unionList ([P].map (·.complex))) Z =
          FiniteSimplicialJoin.simplicialJoin P.complex Z by simp [unionList]))
      exact basedTrans (basedHomeomorphism e _
        (FiniteVertexCylinder.vertexPoint (FiniteSimplicialJoin.simplicialJoin P.complex Z)
          (Sum.inr b) (join_right_vertex P.complex Z b hb)) (Subtype.ext rfl)) P.normalization
    | cons Q qs =>
      let tail := Q :: qs
      let N := unionList (tail.map (·.complex))
      have hN : ({Q.vertex} : Finset V) ∈ N := by
        apply (mem_unionList _ _).mpr
        exact ⟨Q.complex, by simp [tail], Q.vertex_face⟩
      have hPN : P.complex ⊓ N = ⊥ := by
        apply le_antisymm _ bot_le
        rintro s ⟨hs, ht⟩
        obtain ⟨J, hJ, hJs⟩ := (mem_unionList _ s).mp ht
        obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hJ
        exact ((List.pairwise_cons.mp hd).1 R hR) ▸ ⟨hs, hJs⟩
      let F := twoComponentJoinBased P.complex N Z hPN P.vertex P.vertex_face
        Q.vertex hN b hb
      let T := basedTrans
        (FiniteConeUnionWedge.basedWedgeEquivalence
          (ih (by simp) (List.pairwise_cons.mp hd).2) S)
        (basedBouquetAppend (familyJoinSpec es tail) es)
      exact basedTrans F (basedTrans
        (FiniteConeUnionWedge.basedWedgeEquivalence P.normalization T)
        (basedBouquetAppend P.spec (familyJoinSpec es tail ++ es)))

end FiniteFamilyJoinAssembly

end D5.S3.Geometry.FiniteComponentClosure
