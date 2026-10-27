import D5.S3.Geometry.EuclideanSphereJoin
import D5.S3.Geometry.FiniteVertexCylinder
import D5.S3.Geometry.FiniteConeUnionWedge
import D5.S3.Geometry.SingletonRetractionBasedInverse

/-!
Finite coordinate models for the finite-component closure problem in
Carnero Bravo, arXiv:2505.06457v2, Question 22. The intended closure includes
point components and uses ordinary, unreduced joins. The arbitrary-index
reduction and the graph-substitution induction are separate obligations.
-/

noncomputable section
open Set Finset Topology ContinuousMap
open scoped BigOperators unitInterval

namespace D5.S3.Geometry.FiniteComponentClosure


section JoinTransport

variable {X Y X' Y' : Type*}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

private def joinMap (f : C(X, X')) (g : C(Y, Y')) :
    C(FiniteSimplicialJoin.OrdinaryJoin X Y, FiniteSimplicialJoin.OrdinaryJoin X' Y') where
  toFun := Quotient.map' (fun p => (f p.1, g p.2.1, p.2.2)) (by
    rintro p q ⟨ht, hx, hy⟩
    exact ⟨ht, hx.imp id (congrArg f), hy.imp id (congrArg g)⟩)
  continuous_toFun := (by fun_prop : Continuous
    (fun p : X × Y × I => (f p.1, g p.2.1, p.2.2))).quotient_map' _

private def joinHomotopy {f₀ f₁ : C(X, X')} {g₀ g₁ : C(Y, Y')}
    (H : f₀.Homotopy f₁) (K : g₀.Homotopy g₁) :
    (joinMap f₀ g₀).Homotopy (joinMap f₁ g₁) where
  toFun z := Quotient.map' (fun p => (H (z.1, p.1), K (z.1, p.2.1), p.2.2))
    (by
      rintro p q ⟨ht, hx, hy⟩
      exact ⟨ht, hx.imp id (congrArg (fun x => H (z.1, x))),
        hy.imp id (congrArg (fun y => K (z.1, y)))⟩) z.2
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact continuous_quotient_mk'.comp (by fun_prop)
  map_zero_left := by
    intro z
    induction z using Quotient.inductionOn with
    | h p => simp [joinMap, H.apply_zero, K.apply_zero]
  map_one_left := by
    intro z
    induction z using Quotient.inductionOn with
    | h p => simp [joinMap, H.apply_one, K.apply_one]

private theorem joinMap_id :
    joinMap (ContinuousMap.id X) (ContinuousMap.id Y) =
      ContinuousMap.id (FiniteSimplicialJoin.OrdinaryJoin X Y) := by
  ext z
  induction z using Quotient.inductionOn with
  | h p => rfl

private theorem joinMap_comp {X'' Y'' : Type*} [TopologicalSpace X''] [TopologicalSpace Y'']
    (f : C(X, X')) (g : C(Y, Y')) (f' : C(X', X'')) (g' : C(Y', Y'')) :
    (joinMap f' g').comp (joinMap f g) = joinMap (f'.comp f) (g'.comp g) := by
  ext z
  induction z using Quotient.inductionOn with
  | h p => rfl

private def joinCongr (e : X ≃ₕ X') (d : Y ≃ₕ Y') :
    FiniteSimplicialJoin.OrdinaryJoin X Y ≃ₕ FiniteSimplicialJoin.OrdinaryJoin X' Y' where
  toFun := joinMap e.toFun d.toFun
  invFun := joinMap e.invFun d.invFun
  left_inv := by
    rw [joinMap_comp]
    exact ⟨by simpa only [joinMap_id] using joinHomotopy e.left_inv.some d.left_inv.some⟩
  right_inv := by
    rw [joinMap_comp]
    exact ⟨by simpa only [joinMap_id] using joinHomotopy e.right_inv.some d.right_inv.some⟩

private def joinHomeomorph (e : X ≃ₜ X') (d : Y ≃ₜ Y') :
    FiniteSimplicialJoin.OrdinaryJoin X Y ≃ₜ FiniteSimplicialJoin.OrdinaryJoin X' Y' :=
  Homeomorph.Quotient.congr (e.prodCongr (d.prodCongr (Homeomorph.refl I))) (by
    intro p q
    change (p.2.2 = q.2.2 ∧ (p.2.2 = 1 ∨ p.1 = q.1) ∧
      (p.2.2 = 0 ∨ p.2.1 = q.2.1)) ↔
      (p.2.2 = q.2.2 ∧ (p.2.2 = 1 ∨ e p.1 = e q.1) ∧
      (p.2.2 = 0 ∨ d p.2.1 = d q.2.1))
    simp only [e.injective.eq_iff, d.injective.eq_iff])

private def joinSegment (x : X) (y : Y) (a b : I) :
    Path (Quotient.mk _ (x, y, a) : FiniteSimplicialJoin.OrdinaryJoin X Y)
      (Quotient.mk _ (x, y, b)) where
  toFun s := Quotient.mk _ (x, y,
    (⟨(1 - (s : ℝ)) * (a : ℝ) + (s : ℝ) * (b : ℝ),
      ⟨add_nonneg (mul_nonneg (sub_nonneg.mpr s.property.2) a.property.1)
          (mul_nonneg s.property.1 b.property.1),
        by
          have h₁ := mul_nonneg (sub_nonneg.mpr s.property.2) (sub_nonneg.mpr a.property.2)
          have h₂ := mul_nonneg s.property.1 (sub_nonneg.mpr b.property.2)
          nlinarith⟩⟩ : I))
  continuous_toFun := continuous_quotient_mk'.comp (by fun_prop)
  source' := by
    apply Quotient.sound
    exact ⟨Subtype.ext (by simp), Or.inr rfl, Or.inr rfl⟩
  target' := by
    apply Quotient.sound
    exact ⟨Subtype.ext (by simp), Or.inr rfl, Or.inr rfl⟩

private def joinPath (x₀ : X) (y₀ : Y)
    (z : FiniteSimplicialJoin.OrdinaryJoin X Y) :
    Path z (Quotient.mk _ (x₀, y₀, (0 : I))) := by
  let p := Quotient.out z
  have hp : (Quotient.mk _ p : FiniteSimplicialJoin.OrdinaryJoin X Y) = z := Quotient.out_eq z
  rcases p with ⟨x, y, t⟩
  have h₀ : (Quotient.mk _ (x, y, (0 : I)) : FiniteSimplicialJoin.OrdinaryJoin X Y) =
      Quotient.mk _ (x, y₀, (0 : I)) :=
    Quotient.sound ⟨rfl, Or.inr rfl, Or.inl rfl⟩
  have h₁ : (Quotient.mk _ (x, y₀, (1 : I)) : FiniteSimplicialJoin.OrdinaryJoin X Y) =
      Quotient.mk _ (x₀, y₀, (1 : I)) :=
    Quotient.sound ⟨rfl, Or.inl rfl, Or.inr rfl⟩
  exact (((joinSegment x y t 0).trans ((joinSegment x y₀ 0 1).cast h₀ rfl)).trans
    ((joinSegment x₀ y₀ 1 0).cast h₁ rfl)).cast hp.symm rfl

/-- The point factor is a contractible cone, even when the other factor is disconnected. -/
private def pointJoinContraction [Subsingleton X] (x₀ : X) (y₀ : Y) :
    (ContinuousMap.id (FiniteSimplicialJoin.OrdinaryJoin X Y)).Homotopy
      (ContinuousMap.const _ (Quotient.mk _ (x₀, y₀, (0 : I)))) where
  toFun z := Quotient.map' (fun p => (p.1, p.2.1,
    (⟨(1 - (z.1 : ℝ)) * (p.2.2 : ℝ),
      ⟨mul_nonneg (sub_nonneg.mpr z.1.property.2) p.2.2.property.1,
        by
          have h := mul_nonneg (sub_nonneg.mpr z.1.property.2) (sub_nonneg.mpr p.2.2.property.2)
          nlinarith [z.1.property.1]⟩⟩ : I)))
    (by
      rintro p q ⟨ht, _, hy⟩
      refine ⟨by rw [ht], Or.inr (Subsingleton.elim _ _), ?_⟩
      rcases hy with hy | hy
      · left; apply Subtype.ext; simp [hy]
      · exact Or.inr hy) z.2
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact continuous_quotient_mk'.comp (by fun_prop)
  map_zero_left := by
    intro z
    induction z using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      exact ⟨Subtype.ext (by simp), Or.inr rfl, Or.inr rfl⟩
  map_one_left := by
    intro z
    induction z using Quotient.inductionOn with
    | h p =>
      apply Quotient.sound
      exact ⟨Subtype.ext (by simp), Or.inr (Subsingleton.elim _ _),
        Or.inl (Subtype.ext (by simp))⟩

end JoinTransport

section TwoPoints

/-- The two-point complex has singleton faces only. -/
def twoPoints : PreAbstractSimplicialComplex Bool where
  faces := {s | s.card = 1}
  isRelLowerSet_faces := by
    intro s hs
    change s.card = 1 at hs
    refine ⟨Finset.card_pos.mp (by omega), ?_⟩
    intro r hrs hr
    have := Finset.card_le_card hrs
    have := Finset.card_pos.mpr hr
    change r.card = 1
    omega

private theorem twoPoints_singleton (b : Bool) :
    ({b} : Finset Bool) ∈ twoPoints := by
  change ({b} : Finset Bool).card = 1
  simp

private def twoPoint (b : Bool) : FiniteSimplicialJoin.Space twoPoints :=
  FiniteVertexCylinder.vertexPoint twoPoints b (twoPoints_singleton b)

private theorem singleton_coordinates {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) {x : V → ℝ} (hx : x ∈ FiniteConeCollapse.faceSimplex {v}) : x = Pi.single v 1 := by
  have hv : x v = 1 := by
    rw [← hx.2.1]
    symm
    exact Finset.sum_eq_single v (fun w _ hw => hx.2.2 w (by simpa using hw))
      (by simp)
  ext w
  by_cases hw : w = v
  · subst w; simpa using hv
  · simpa [Pi.single_apply, hw, Ne.symm hw] using hx.2.2 w (by simpa using hw)

private theorem twoPoints_exhaust (x : FiniteSimplicialJoin.Space twoPoints) :
    x = twoPoint true ∨ x = twoPoint false := by
  obtain ⟨s, hs, hx⟩ := x.property
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hs
  rw [← FiniteConeCollapse.faceSimplex_eq_convexHull] at hx
  have he : x = twoPoint b := Subtype.ext (singleton_coordinates b hx)
  cases b
  · exact Or.inr he
  · exact Or.inl he

private def twoPointSphereMap : FiniteSimplicialJoin.Space twoPoints → EuclideanSphereJoin.StdSphere 0 := fun x =>
  ⟨(EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => x.val true - x.val false), by
    change _ ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1
    rw [EuclideanSpace.sphere_zero_eq 1 (by norm_num)]
    rcases twoPoints_exhaust x with rfl | rfl <;>
      norm_num [twoPoint, FiniteVertexCylinder.vertexPoint, EuclideanSpace.equiv, Pi.single_apply]⟩

private theorem twoPointSphereMap_bijective : Function.Bijective twoPointSphereMap := by
  constructor
  · intro x y h
    have h₀ := congrArg (fun z : EuclideanSphereJoin.StdSphere 0 => z.val 0) h
    rcases twoPoints_exhaust x with rfl | rfl <;>
      rcases twoPoints_exhaust y with rfl | rfl
    · rfl
    · norm_num [twoPointSphereMap, twoPoint, FiniteVertexCylinder.vertexPoint, EuclideanSpace.equiv,
        Pi.single_apply] at h₀
    · norm_num [twoPointSphereMap, twoPoint, FiniteVertexCylinder.vertexPoint, EuclideanSpace.equiv,
        Pi.single_apply] at h₀
    · rfl
  · intro y
    have hy : y.val 0 ^ 2 = 1 := by
      have hy := y.property
      change y.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 at hy
      rw [EuclideanSpace.sphere_zero_eq 1 (by norm_num)] at hy
      simpa using hy
    have he : y.val 0 = 1 ∨ y.val 0 = -1 := by
      rcases mul_self_eq_mul_self_iff.mp (show y.val 0 * y.val 0 = 1 * 1 by nlinarith) with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases he with he | he
    · refine ⟨twoPoint true, ?_⟩
      apply Subtype.ext
      apply PiLp.ext
      intro i
      have : i = 0 := Fin.eq_zero i
      subst i
      simpa [twoPointSphereMap, twoPoint, FiniteVertexCylinder.vertexPoint, EuclideanSpace.equiv,
        Pi.single_apply] using he.symm
    · refine ⟨twoPoint false, ?_⟩
      apply Subtype.ext
      apply PiLp.ext
      intro i
      have : i = 0 := Fin.eq_zero i
      subst i
      simpa [twoPointSphereMap, twoPoint, FiniteVertexCylinder.vertexPoint, EuclideanSpace.equiv,
        Pi.single_apply] using he.symm

/-- The actual two coordinate vertices are the zero-sphere in one Euclidean dimension. -/
def twoPointSphereHomeomorph : FiniteSimplicialJoin.Space twoPoints ≃ₜ EuclideanSphereJoin.StdSphere 0 := by
  have hfinite : (Set.univ : Set (FiniteSimplicialJoin.Space twoPoints)).Finite := by
    apply Set.Finite.subset (Set.toFinite {twoPoint true, twoPoint false})
    intro x _
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using twoPoints_exhaust x
  letI : Finite (FiniteSimplicialJoin.Space twoPoints) := Set.finite_univ_iff.mp hfinite
  letI : CompactSpace (FiniteSimplicialJoin.Space twoPoints) := inferInstance
  apply Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective twoPointSphereMap twoPointSphereMap_bijective)
  apply Continuous.subtype_mk
  exact (EuclideanSpace.equiv (Fin 1) ℝ).symm.continuous.comp (by fun_prop)

end TwoPoints

/-- Recursively tagged vertices of the iterated two-point sphere. -/
def SphereVertices : ℕ → Type
  | 0 => Bool
  | d + 1 => SphereVertices d ⊕ Bool

instance sphereVerticesFintype : (d : ℕ) → Fintype (SphereVertices d)
  | 0 => inferInstanceAs (Fintype Bool)
  | d + 1 =>
    letI := sphereVerticesFintype d
    inferInstanceAs (Fintype (SphereVertices d ⊕ Bool))

instance sphereVerticesDecidableEq : (d : ℕ) → DecidableEq (SphereVertices d)
  | 0 => inferInstanceAs (DecidableEq Bool)
  | d + 1 =>
    letI := sphereVerticesDecidableEq d
    inferInstanceAs (DecidableEq (SphereVertices d ⊕ Bool))

/-- The finite crosspolytope sphere, including its disconnected zero-dimensional case. -/
def sphereComplex : (d : ℕ) → PreAbstractSimplicialComplex (SphereVertices d)
  | 0 => twoPoints
  | d + 1 => FiniteSimplicialJoin.simplicialJoin (sphereComplex d) twoPoints

def sphereVertex : (d : ℕ) → SphereVertices d
  | 0 => true
  | d + 1 => Sum.inl (sphereVertex d)

private theorem sphereVertex_face (d : ℕ) :
    ({sphereVertex d} : Finset (SphereVertices d)) ∈ sphereComplex d := by
  induction d with
  | zero => exact twoPoints_singleton true
  | succ d ih =>
    change ({Sum.inl (sphereVertex d)} : Finset (SphereVertices d ⊕ Bool)).Nonempty ∧
      (({Sum.inl (sphereVertex d)} : Finset (SphereVertices d ⊕ Bool)).toLeft = ∅ ∨
        ({Sum.inl (sphereVertex d)} : Finset (SphereVertices d ⊕ Bool)).toLeft ∈ sphereComplex d) ∧
      (({Sum.inl (sphereVertex d)} : Finset (SphereVertices d ⊕ Bool)).toRight = ∅ ∨
        ({Sum.inl (sphereVertex d)} : Finset (SphereVertices d ⊕ Bool)).toRight ∈ twoPoints)
    have hl : ({Sum.inl (sphereVertex d)} : Finset (SphereVertices d ⊕ Bool)).toLeft =
        {sphereVertex d} := by ext v; simp
    have hr : ({Sum.inl (sphereVertex d)} : Finset (SphereVertices d ⊕ Bool)).toRight =
        ∅ := by ext v; simp
    refine ⟨by simp, Or.inr ?_, Or.inl hr⟩
    rw [hl]
    exact ih

def spherePoint (d : ℕ) : FiniteSimplicialJoin.Space (sphereComplex d) :=
  FiniteVertexCylinder.vertexPoint _ _ (sphereVertex_face d)

/-- The sphere model is identified with the actual standard sphere, using actual join maps. -/
def sphereHomeomorph : (d : ℕ) → FiniteSimplicialJoin.Space (sphereComplex d) ≃ₜ EuclideanSphereJoin.StdSphere d
  | 0 => twoPointSphereHomeomorph
  | d + 1 =>
    (FiniteSimplicialJoin.joinHomeomorph (sphereComplex d) twoPoints ⟨spherePoint d⟩ ⟨twoPoint true⟩).symm.trans
      ((joinHomeomorph (sphereHomeomorph d) twoPointSphereHomeomorph).trans
        (by simpa using EuclideanSphereJoin.sphereJoinHomeomorph d 0))

private def spherePath (d : ℕ) (hd : 0 < d)
    (x : FiniteSimplicialJoin.Space (sphereComplex d)) : Path x (spherePoint d) := by
  cases d with
  | zero => omega
  | succ d =>
    let e := FiniteSimplicialJoin.joinHomeomorph (sphereComplex d) twoPoints
      ⟨spherePoint d⟩ ⟨twoPoint true⟩
    have hbase : e (Quotient.mk _ (spherePoint d, twoPoint true, (0 : I))) =
        spherePoint (d + 1) := by
      apply Subtype.ext
      change FiniteSimplicialJoin.representative (sphereComplex d) twoPoints
        (spherePoint d, twoPoint true, (0 : I)) = Pi.single (Sum.inl (sphereVertex d)) 1
      funext v
      cases v <;>
        simp [FiniteSimplicialJoin.representative, spherePoint,
          FiniteVertexCylinder.vertexPoint, Pi.single_apply]
    exact ((joinPath (spherePoint d) (twoPoint true) (e.symm x)).map e.continuous).cast
      (e.apply_symm_apply x).symm hbase.symm

private def nativeCylinder {V : Type*} [Fintype V] [DecidableEq V]
    (M : PreAbstractSimplicialComplex V) (a : V) (ha : ({a} : Finset V) ∈ M) :
    SingletonRetractionBasedInverse.CylinderRetraction
      (FiniteVertexCylinder.vertexPoint M a ha) where
  map := FiniteVertexCylinder.retraction M a ha
  fixed z hz := FiniteVertexCylinder.retraction_fixed M a ha ⟨z, hz⟩

section CoordinateEmbeddings

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

private def coordinateLinear (e : V ↪ W) : (V → ℝ) →ₗ[ℝ] (W → ℝ) where
  toFun x w := ∑ v, if e v = w then x v else 0
  map_add' x y := by
    ext w
    change (∑ v, if e v = w then x v + y v else 0) =
      (∑ v, if e v = w then x v else 0) + ∑ v, if e v = w then y v else 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp
  map_smul' c x := by
    ext w
    change (∑ v, if e v = w then c * x v else 0) = c * ∑ v, if e v = w then x v else 0
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp

private theorem coordinateLinear_at (e : V ↪ W) (x : V → ℝ) (v : V) :
    coordinateLinear e x (e v) = x v := by
  simp [coordinateLinear, e.injective.eq_iff]

private theorem coordinateLinear_single (e : V ↪ W) (v : V) :
    coordinateLinear e (Pi.single v 1) = Pi.single (e v) 1 := by
  ext w
  change (∑ u, if e u = w then Pi.single v (1 : ℝ) u else 0) = (Pi.single (e v) (1 : ℝ) : W → ℝ) w
  rw [Finset.sum_eq_single v]
  · simp [Pi.single_apply, eq_comm]
  · intro u _ hu
    simp [Pi.single_apply, hu, Ne.symm hu]
  · simp

private theorem realization_map (M : PreAbstractSimplicialComplex V) (e : V ↪ W) :
    FiniteConeCollapse.realization (M.map e) =
      coordinateLinear e '' FiniteConeCollapse.realization M := by
  have hface (s : Finset V) :
      coordinateLinear e '' convexHull ℝ
        ((fun v : V => Pi.single v (1 : ℝ)) '' (s : Set V)) =
      convexHull ℝ ((fun w : W => Pi.single w (1 : ℝ)) ''
        (s.image e : Set W)) := by
    rw [LinearMap.image_convexHull]
    congr 1
    simp only [Set.image_image, Finset.coe_image]
    congr 1
    funext v
    exact coordinateLinear_single e v
  ext y
  constructor
  · rintro ⟨t, ⟨s, hs, rfl⟩, hy⟩
    rw [← hface] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, ⟨s, hs, hx⟩, rfl⟩
  · rintro ⟨x, ⟨s, hs, hx⟩, rfl⟩
    refine ⟨s.image e, ⟨s, hs, rfl⟩, ?_⟩
    rw [← hface]
    exact ⟨x, hx, rfl⟩

private def coordinateForward (M : PreAbstractSimplicialComplex V) (e : V ↪ W) :
    C(FiniteSimplicialJoin.Space M, FiniteSimplicialJoin.Space (M.map e)) where
  toFun x := ⟨coordinateLinear e x.val,
    (Set.ext_iff.mp (realization_map M e) _).mpr ⟨x.val, x.property, rfl⟩⟩
  continuous_toFun := Continuous.subtype_mk
    ((coordinateLinear e).continuous_of_finiteDimensional.comp continuous_subtype_val) _

private theorem coordinateRestriction_mem (M : PreAbstractSimplicialComplex V) (e : V ↪ W)
    (y : FiniteSimplicialJoin.Space (M.map e)) :
    (fun v => y.val (e v)) ∈ FiniteConeCollapse.realization M := by
  obtain ⟨x, hx, he⟩ := (Set.ext_iff.mp (realization_map M e) y.val).mp y.property
  have h : (fun v => y.val (e v)) = x := by
    funext v
    exact (congrFun he (e v)).symm.trans (coordinateLinear_at e x v)
  exact h.symm ▸ hx

private def coordinateBackward (M : PreAbstractSimplicialComplex V) (e : V ↪ W) :
    C(FiniteSimplicialJoin.Space (M.map e), FiniteSimplicialJoin.Space M) where
  toFun y := ⟨fun v => y.val (e v), coordinateRestriction_mem M e y⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun y : FiniteSimplicialJoin.Space (M.map e) => fun v : V => y.val (e v))
    exact continuous_pi fun v => (continuous_apply (e v)).comp
      (continuous_subtype_val : Continuous (fun y : FiniteSimplicialJoin.Space (M.map e) => y.val))

private def coordinateHomeomorph (M : PreAbstractSimplicialComplex V) (e : V ↪ W) :
    FiniteSimplicialJoin.Space M ≃ₜ FiniteSimplicialJoin.Space (M.map e) where
  toFun := coordinateForward M e
  invFun := coordinateBackward M e
  left_inv x := Subtype.ext (funext (coordinateLinear_at e x.val))
  right_inv y := by
    apply Subtype.ext
    change coordinateLinear e (fun v => y.val (e v)) = y.val
    obtain ⟨x, _, he⟩ := (Set.ext_iff.mp (realization_map M e) y.val).mp y.property
    have hr : (fun v => y.val (e v)) = x := by
      funext v
      exact (congrFun he (e v)).symm.trans (coordinateLinear_at e x v)
    exact (congrArg (coordinateLinear e) hr).trans he
  continuous_toFun := (coordinateForward M e).continuous
  continuous_invFun := (coordinateBackward M e).continuous

end CoordinateEmbeddings

section CoordinateCoproducts

variable {A : Type*} [Fintype A] [DecidableEq A]
  {V : A → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
  (M : ∀ i, PreAbstractSimplicialComplex (V i))

private def coproductComplex : PreAbstractSimplicialComplex (Σ i, V i) :=
  ⨆ i, (M i).map (Sigma.mk i)

private theorem mem_coproductComplex (s : Finset (Σ i, V i)) :
    s ∈ coproductComplex M ↔ ∃ i, s ∈ (M i).map (Sigma.mk i) := by
  change (s ∈ ⋃ K ∈ Set.range (fun i => (M i).map (Sigma.mk i)), K.faces) ↔ _
  simp only [Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro ⟨K, ⟨i, rfl⟩, hs⟩; exact ⟨i, hs⟩
  · rintro ⟨i, hs⟩; exact ⟨_, ⟨i, rfl⟩, hs⟩

private theorem coproductInclusion_mem (i : A) (x : FiniteSimplicialJoin.Space (M i)) :
    coordinateLinear ⟨Sigma.mk i, sigma_mk_injective⟩ x.val ∈
      FiniteConeCollapse.realization (coproductComplex M) := by
  obtain ⟨s, hs, hx⟩ := (coordinateForward (M i) ⟨Sigma.mk i, sigma_mk_injective⟩ x).property
  exact ⟨s, (mem_coproductComplex M s).mpr ⟨i, hs⟩, hx⟩

private def coproductInclusion (i : A) :
    C(FiniteSimplicialJoin.Space (M i), FiniteSimplicialJoin.Space (coproductComplex M)) where
  toFun x := ⟨coordinateLinear ⟨Sigma.mk i, sigma_mk_injective⟩ x.val,
    coproductInclusion_mem M i x⟩
  continuous_toFun := Continuous.subtype_mk
    ((coordinateLinear ⟨Sigma.mk i, sigma_mk_injective⟩).continuous_of_finiteDimensional.comp
      continuous_subtype_val) _

private def coproductMap : (Σ i, FiniteSimplicialJoin.Space (M i)) →
    FiniteSimplicialJoin.Space (coproductComplex M) := fun x => coproductInclusion M x.1 x.2

private theorem sum_coordinates {U : Type*} [Fintype U] [DecidableEq U]
    {K : PreAbstractSimplicialComplex U} (x : FiniteSimplicialJoin.Space K) :
    ∑ u, x.val u = 1 := by
  obtain ⟨s, _, hx⟩ := x.property
  rw [← FiniteConeCollapse.faceSimplex_eq_convexHull] at hx
  exact hx.2.1

private theorem coordinateLinear_off (i j : A) (hij : i ≠ j) (x : V j → ℝ) (v : V i) :
    coordinateLinear ⟨Sigma.mk j, sigma_mk_injective⟩ x ⟨i, v⟩ = 0 := by
  apply Finset.sum_eq_zero
  intro w _
  have h : (⟨j, w⟩ : Σ i, V i) ≠ ⟨i, v⟩ := fun h => hij (congrArg Sigma.fst h).symm
  simp [h]

private theorem coordinateLinear_same (i : A) (x : V i → ℝ) (v : V i) :
    coordinateLinear ⟨Sigma.mk i, sigma_mk_injective⟩ x ⟨i, v⟩ = x v :=
  coordinateLinear_at ⟨Sigma.mk i, sigma_mk_injective⟩ x v

private theorem coproductMap_bijective : Function.Bijective (coproductMap M) := by
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ h
    have hij : i = j := by
      by_contra hij
      have hsum := congrArg (fun z : FiniteSimplicialJoin.Space (coproductComplex M) =>
        ∑ v : V i, z.val ⟨i, v⟩) h
      have hleft : (∑ v : V i, (coproductInclusion M i x).val ⟨i, v⟩) = 1 := by
        simpa only [coproductInclusion, ContinuousMap.coe_mk, coordinateLinear_same]
          using sum_coordinates x
      have hright : (∑ v : V i, (coproductInclusion M j y).val ⟨i, v⟩) = 0 := by
        simp only [coproductInclusion, ContinuousMap.coe_mk, coordinateLinear_off i j hij,
          Finset.sum_const_zero]
      change (∑ v : V i, (coproductInclusion M i x).val ⟨i, v⟩) =
        (∑ v : V i, (coproductInclusion M j y).val ⟨i, v⟩) at hsum
      rw [hleft, hright] at hsum
      norm_num at hsum
    subst j
    apply congrArg (Sigma.mk i)
    apply Subtype.ext
    funext v
    have hv := congrArg (fun z : FiniteSimplicialJoin.Space (coproductComplex M) =>
      z.val ⟨i, v⟩) h
    simpa only [coproductMap, coproductInclusion, ContinuousMap.coe_mk, coordinateLinear_same]
      using hv
  · intro y
    obtain ⟨s, hs, hy⟩ := y.property
    obtain ⟨i, hs⟩ := (mem_coproductComplex M s).mp hs
    let z : FiniteSimplicialJoin.Space ((M i).map (Sigma.mk i)) := ⟨y.val, s, hs, hy⟩
    let x := (coordinateHomeomorph (M i) ⟨Sigma.mk i, sigma_mk_injective⟩).symm z
    refine ⟨⟨i, x⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun w : FiniteSimplicialJoin.Space ((M i).map (Sigma.mk i)) => w.val)
      ((coordinateHomeomorph (M i) ⟨Sigma.mk i, sigma_mk_injective⟩).apply_symm_apply z)

/-- Disjoint finite coordinate pieces have precisely the topological coproduct realization. -/
private def coproductHomeomorph :
    (Σ i, FiniteSimplicialJoin.Space (M i)) ≃ₜ
      FiniteSimplicialJoin.Space (coproductComplex M) := by
  letI (i : A) : CompactSpace (FiniteSimplicialJoin.Space (M i)) :=
    FiniteSimplicialJoin.realizationCompactSpace (M i)
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (coproductMap M) (coproductMap_bijective M))
    (continuous_sigma fun i => (coproductInclusion M i).continuous)

end CoordinateCoproducts

abbrev BouquetSpec := List {d : ℕ // 0 < d}

/-- One common vertex and the separately tagged nonbase vertices of every sphere. -/
abbrev BouquetVertices (ds : BouquetSpec) :=
  Option (Σ i : Fin ds.length,
    {v : SphereVertices (ds.get i).val // v ≠ sphereVertex (ds.get i).val})

private def bouquetInclusion (ds : BouquetSpec) (i : Fin ds.length) :
    SphereVertices (ds.get i).val ↪ BouquetVertices ds where
  toFun v := if h : v = sphereVertex (ds.get i).val then none else some ⟨i, ⟨v, h⟩⟩
  inj' := by
    intro v w h
    change (if h : v = sphereVertex (ds.get i).val then none else some ⟨i, ⟨v, h⟩⟩ : BouquetVertices ds) =
      (if h : w = sphereVertex (ds.get i).val then none else some ⟨i, ⟨w, h⟩⟩ : BouquetVertices ds) at h
    by_cases hv : v = sphereVertex (ds.get i).val
    · by_cases hw : w = sphereVertex (ds.get i).val
      · exact hv.trans hw.symm
      · rw [dif_pos hv, dif_neg hw] at h
        cases h
    · by_cases hw : w = sphereVertex (ds.get i).val
      · rw [dif_neg hv, dif_pos hw] at h
        cases h
      · rw [dif_neg hv, dif_neg hw] at h
        have hs : (⟨i, ⟨v, hv⟩⟩ : Σ k : Fin ds.length,
            {v : SphereVertices (ds.get k).val // v ≠ sphereVertex (ds.get k).val}) =
            ⟨i, ⟨w, hw⟩⟩ := Option.some.inj h
        have hs' : (⟨v, hv⟩ : {v : SphereVertices (ds.get i).val //
            v ≠ sphereVertex (ds.get i).val}) = ⟨w, hw⟩ :=
          (@sigma_mk_injective (Fin ds.length)
            (fun k => {v : SphereVertices (ds.get k).val //
              v ≠ sphereVertex (ds.get k).val}) i) hs
        exact congrArg Subtype.val hs'

private theorem bouquetInclusion_base (ds : BouquetSpec) (i : Fin ds.length) :
    bouquetInclusion ds i (sphereVertex (ds.get i).val) = none := by
  exact dif_pos rfl

private theorem bouquetInclusion_off (ds : BouquetSpec) (i : Fin ds.length)
    (v : SphereVertices (ds.get i).val) (hv : v ≠ sphereVertex (ds.get i).val) :
    bouquetInclusion ds i v = some ⟨i, ⟨v, hv⟩⟩ := by
  exact dif_neg hv

/-- The singleton complex retains a genuine point when a sphere list is empty. -/
private def vertexComplex {V : Type*} [DecidableEq V] (v : V) :
    PreAbstractSimplicialComplex V where
  faces := {{v}}
  isRelLowerSet_faces := by
    rintro s rfl
    refine ⟨by simp, ?_⟩
    intro t hts ht
    exact Set.mem_singleton_iff.mpr (Finset.eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨ht, fun w hw => Finset.mem_singleton.mp (hts hw)⟩)

/-- The literal finite coordinate bouquet; no zero-dimensional sphere is a summand. -/
def bouquetComplex (ds : BouquetSpec) : PreAbstractSimplicialComplex (BouquetVertices ds) :=
  vertexComplex none ⊔ ⨆ i, (sphereComplex (ds.get i).val).map (bouquetInclusion ds i)

private theorem bouquetVertex_face (ds : BouquetSpec) :
    ({none} : Finset (BouquetVertices ds)) ∈ bouquetComplex ds := Or.inl rfl

def bouquetPoint (ds : BouquetSpec) : FiniteSimplicialJoin.Space (bouquetComplex ds) :=
  FiniteVertexCylinder.vertexPoint _ _ (bouquetVertex_face ds)

private theorem mem_bouquetComplex (ds : BouquetSpec) (s : Finset (BouquetVertices ds)) :
    s ∈ bouquetComplex ds ↔ s = {none} ∨
      ∃ i, s ∈ (sphereComplex (ds.get i).val).map (bouquetInclusion ds i) := by
  change (s ∈ vertexComplex none ∨ s ∈ ⋃ K ∈ Set.range
    (fun i => (sphereComplex (ds.get i).val).map (bouquetInclusion ds i)), K.faces) ↔ _
  apply or_congr Iff.rfl
  simp only [Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro ⟨K, ⟨i, rfl⟩, hs⟩; exact ⟨i, hs⟩
  · rintro ⟨i, hs⟩; exact ⟨_, ⟨i, rfl⟩, hs⟩

private def bouquetPiece (ds : BouquetSpec) (i : Fin ds.length) :
    C(FiniteSimplicialJoin.Space (sphereComplex (ds.get i).val),
      FiniteSimplicialJoin.Space (bouquetComplex ds)) where
  toFun x := ⟨coordinateLinear (bouquetInclusion ds i) x.val, by
    obtain ⟨s, hs, hx⟩ := (coordinateHomeomorph (sphereComplex (ds.get i).val)
      (bouquetInclusion ds i) x).property
    exact ⟨s, (mem_bouquetComplex ds s).mpr (Or.inr ⟨i, hs⟩), hx⟩⟩
  continuous_toFun := Continuous.subtype_mk
    ((coordinateLinear (bouquetInclusion ds i)).continuous_of_finiteDimensional.comp
      continuous_subtype_val) _

private theorem bouquetPiece_base (ds : BouquetSpec) (i : Fin ds.length) :
    bouquetPiece ds i (spherePoint (ds.get i).val) = bouquetPoint ds := by
  apply Subtype.ext
  change coordinateLinear (bouquetInclusion ds i)
    (Pi.single (sphereVertex (ds.get i).val) 1) = Pi.single none 1
  rw [coordinateLinear_single, bouquetInclusion_base]

private theorem bouquetPiece_injective (ds : BouquetSpec) (i : Fin ds.length) :
    Function.Injective (bouquetPiece ds i) := by
  intro x y h
  apply Subtype.ext
  funext v
  have := congrArg (fun z : FiniteSimplicialJoin.Space (bouquetComplex ds) =>
    z.val (bouquetInclusion ds i v)) h
  simpa only [bouquetPiece, ContinuousMap.coe_mk, coordinateLinear_at] using this

private theorem bouquetInclusion_intersection (ds : BouquetSpec)
    (i j : Fin ds.length) (hij : i ≠ j)
    (v : SphereVertices (ds.get i).val) (w : SphereVertices (ds.get j).val)
    (h : bouquetInclusion ds i v = bouquetInclusion ds j w) :
    bouquetInclusion ds i v = none := by
  by_cases hv : v = sphereVertex (ds.get i).val
  · subst v
    exact bouquetInclusion_base ds i
  · by_cases hw : w = sphereVertex (ds.get j).val
    · subst w
      exact h.trans (bouquetInclusion_base ds j)
    · rw [bouquetInclusion_off ds i v hv, bouquetInclusion_off ds j w hw] at h
      exact (hij (congrArg Sigma.fst (Option.some.inj h))).elim

private theorem coordinates_eq_vertex {V : Type*} [Fintype V] [DecidableEq V]
    {M : PreAbstractSimplicialComplex V} (x : FiniteSimplicialJoin.Space M)
    (a : V) (ha : ({a} : Finset V) ∈ M) (hz : ∀ v, v ≠ a → x.val v = 0) :
    x = FiniteVertexCylinder.vertexPoint M a ha := by
  apply Subtype.ext
  apply singleton_coordinates a
  obtain ⟨s, _, hx⟩ := x.property
  rw [← FiniteConeCollapse.faceSimplex_eq_convexHull] at hx
  exact ⟨hx.1, hx.2.1, fun v hv => hz v (by simpa using hv)⟩

private theorem bouquetPiece_intersection (ds : BouquetSpec)
    (i j : Fin ds.length) (hij : i ≠ j)
    (x : FiniteSimplicialJoin.Space (sphereComplex (ds.get i).val))
    (y : FiniteSimplicialJoin.Space (sphereComplex (ds.get j).val))
    (h : bouquetPiece ds i x = bouquetPiece ds j y) :
    x = spherePoint (ds.get i).val ∧ y = spherePoint (ds.get j).val := by
  have hx : x = spherePoint (ds.get i).val := by
    apply coordinates_eq_vertex x _ (sphereVertex_face _)
    intro v hv
    have he := congrArg (fun z : FiniteSimplicialJoin.Space (bouquetComplex ds) =>
      z.val (bouquetInclusion ds i v)) h
    have hz : coordinateLinear (bouquetInclusion ds j) y.val (bouquetInclusion ds i v) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      have hne : bouquetInclusion ds j w ≠ bouquetInclusion ds i v := by
        intro hh
        have := bouquetInclusion_intersection ds i j hij v w hh.symm
        rw [bouquetInclusion_off ds i v hv] at this
        cases this
      simp [hne]
    simpa only [bouquetPiece, ContinuousMap.coe_mk, coordinateLinear_at, hz] using he
  refine ⟨hx, bouquetPiece_injective ds j ?_⟩
  rw [← h, hx, bouquetPiece_base, bouquetPiece_base]

/-- The quotient source includes a separate common vertex, so the empty family is a point. -/
abbrev BouquetSource (ds : BouquetSpec) :=
  PUnit.{1} ⊕ (Σ i : Fin ds.length, FiniteSimplicialJoin.Space (sphereComplex (ds.get i).val))

private def bouquetBases (ds : BouquetSpec) : Set (BouquetSource ds) :=
  {z | Sum.elim (fun _ => True) (fun x => x.2 = spherePoint (ds.get x.1).val) z}

abbrev CoordinateBouquetQuotient (ds : BouquetSpec) :=
  FiniteConeUnionWedge.Collapse (bouquetBases ds)

private def bouquetSourceMap (ds : BouquetSpec) :
    C(BouquetSource ds, FiniteSimplicialJoin.Space (bouquetComplex ds)) where
  toFun := Sum.elim (fun _ => bouquetPoint ds) (fun x => bouquetPiece ds x.1 x.2)
  continuous_toFun := continuous_const.sumElim
    (continuous_sigma fun i => (bouquetPiece ds i).continuous)

private theorem bouquetSourceMap_base (ds : BouquetSpec) (z : BouquetSource ds)
    (hz : z ∈ bouquetBases ds) : bouquetSourceMap ds z = bouquetPoint ds := by
  rcases z with _ | ⟨i, x⟩
  · rfl
  · change x = spherePoint (ds.get i).val at hz
    subst x
    exact bouquetPiece_base ds i

private theorem bouquetSourceMap_kernel (ds : BouquetSpec) (z w : BouquetSource ds) :
    bouquetSourceMap ds z = bouquetSourceMap ds w ↔
      (FiniteConeUnionWedge.subsetSetoid (bouquetBases ds)).r z w := by
  constructor
  · intro h
    rcases z with z | ⟨i, x⟩ <;> rcases w with w | ⟨j, y⟩
    · exact Or.inl (congrArg Sum.inl (Subsingleton.elim _ _))
    · apply Or.inr
      refine ⟨True.intro, bouquetPiece_injective ds j ?_⟩
      exact h.symm.trans (bouquetPiece_base ds j).symm
    · apply Or.inr
      refine ⟨bouquetPiece_injective ds i ?_, True.intro⟩
      exact h.trans (bouquetPiece_base ds i).symm
    · by_cases hij : i = j
      · subst j
        exact Or.inl (congrArg Sum.inr (congrArg (Sigma.mk i) (bouquetPiece_injective ds i h)))
      · exact Or.inr (bouquetPiece_intersection ds i j hij x y h)
  · rintro (rfl | ⟨hz, hw⟩)
    · rfl
    · exact (bouquetSourceMap_base ds z hz).trans (bouquetSourceMap_base ds w hw).symm

private theorem bouquetSourceMap_surjective (ds : BouquetSpec) :
    Function.Surjective (bouquetSourceMap ds) := by
  intro y
  obtain ⟨s, hs, hy⟩ := y.property
  rcases (mem_bouquetComplex ds s).mp hs with rfl | ⟨i, hs⟩
  · rw [← FiniteConeCollapse.faceSimplex_eq_convexHull] at hy
    exact ⟨Sum.inl PUnit.unit, Subtype.ext (singleton_coordinates none hy).symm⟩
  · let z : FiniteSimplicialJoin.Space
        ((sphereComplex (ds.get i).val).map (bouquetInclusion ds i)) := ⟨y.val, s, hs, hy⟩
    let x := (coordinateHomeomorph (sphereComplex (ds.get i).val)
      (bouquetInclusion ds i)).symm z
    refine ⟨Sum.inr ⟨i, x⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun w : FiniteSimplicialJoin.Space
      ((sphereComplex (ds.get i).val).map (bouquetInclusion ds i)) => w.val)
      ((coordinateHomeomorph (sphereComplex (ds.get i).val)
        (bouquetInclusion ds i)).apply_symm_apply z)

private def bouquetQuotientMap (ds : BouquetSpec) :
    C(CoordinateBouquetQuotient ds, FiniteSimplicialJoin.Space (bouquetComplex ds)) where
  toFun := Quotient.lift (bouquetSourceMap ds) (fun z w h =>
    (bouquetSourceMap_kernel ds z w).mpr h)
  continuous_toFun := (bouquetSourceMap ds).continuous.quotient_lift _

/-- The full quotient kernel, including all repeated sphere bases and the empty bouquet. -/
def bouquetQuotientHomeomorph (ds : BouquetSpec) :
    CoordinateBouquetQuotient ds ≃ₜ FiniteSimplicialJoin.Space (bouquetComplex ds) := by
  letI (i : Fin ds.length) : CompactSpace
      (FiniteSimplicialJoin.Space (sphereComplex (ds.get i).val)) :=
    FiniteSimplicialJoin.realizationCompactSpace _
  apply Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective (bouquetQuotientMap ds) ?_)
    (bouquetQuotientMap ds).continuous
  constructor
  · intro z w
    induction z using Quotient.inductionOn with
    | h z =>
      induction w using Quotient.inductionOn with
      | h w => exact fun h => Quotient.sound ((bouquetSourceMap_kernel ds z w).mp h)
  · intro y
    obtain ⟨z, hz⟩ := bouquetSourceMap_surjective ds y
    exact ⟨Quotient.mk _ z, hz⟩

private def bouquetPath (ds : BouquetSpec)
    (x : FiniteSimplicialJoin.Space (bouquetComplex ds)) : Path x (bouquetPoint ds) := by
  let z := Classical.choose (bouquetSourceMap_surjective ds x)
  have hz := Classical.choose_spec (bouquetSourceMap_surjective ds x)
  change bouquetSourceMap ds z = x at hz
  rcases z with _ | ⟨i, y⟩
  · exact (Path.refl (bouquetPoint ds)).cast hz.symm rfl
  · exact ((spherePath (ds.get i).val (ds.get i).property y).map
      (bouquetPiece ds i).continuous).cast hz.symm (bouquetPiece_base ds i).symm

private theorem emptyBouquet_point (x : FiniteSimplicialJoin.Space (bouquetComplex [])) :
    x = bouquetPoint [] := by
  obtain ⟨z, hz⟩ := bouquetSourceMap_surjective [] x
  rcases z with _ | ⟨i, _⟩
  · exact hz.symm
  · exact Fin.elim0 i

private def emptyBouquetJoinEquiv {Z : Type*} [TopologicalSpace Z] (z₀ : Z) :
    FiniteSimplicialJoin.OrdinaryJoin
      (FiniteSimplicialJoin.Space (bouquetComplex [])) Z ≃ₕ
      FiniteSimplicialJoin.Space (bouquetComplex []) := by
  letI : Subsingleton (FiniteSimplicialJoin.Space (bouquetComplex [])) :=
    ⟨fun x y => (emptyBouquet_point x).trans (emptyBouquet_point y).symm⟩
  exact {
    toFun := ContinuousMap.const _ (bouquetPoint [])
    invFun := ContinuousMap.const _ (Quotient.mk _ (bouquetPoint [], z₀, (0 : I)))
    left_inv := ⟨(pointJoinContraction (bouquetPoint []) z₀).symm⟩
    right_inv := by
      have he : (ContinuousMap.const _ (bouquetPoint [])).comp
          (ContinuousMap.const _ (Quotient.mk
            (FiniteSimplicialJoin.ordinaryJoinSetoid _ Z) (bouquetPoint [], z₀, (0 : I)))) =
          ContinuousMap.id (FiniteSimplicialJoin.Space (bouquetComplex [])) := by
        apply ContinuousMap.ext
        intro x
        exact Subsingleton.elim _ _
      simpa only [he] using (Homotopic.refl
        (ContinuousMap.id (FiniteSimplicialJoin.Space (bouquetComplex [])))) }

private def sphereFamilyHomeomorph (ds : BouquetSpec) :
    (Σ i : Fin ds.length, FiniteSimplicialJoin.Space (sphereComplex (ds.get i).val)) ≃ₜ
      (Σ i : Fin ds.length, EuclideanSphereJoin.StdSphere (ds.get i).val) where
  toEquiv := Equiv.sigmaCongrRight (fun i => (sphereHomeomorph (ds.get i).val).toEquiv)
  continuous_toFun := continuous_sigma fun i =>
    continuous_sigmaMk.comp (sphereHomeomorph (ds.get i).val).continuous
  continuous_invFun := continuous_sigma fun i =>
    continuous_sigmaMk.comp (sphereHomeomorph (ds.get i).val).symm.continuous

/-- An actual standard-sphere point, chosen by the finite-coordinate sphere identification. -/
def standardSphereBase (d : ℕ) : EuclideanSphereJoin.StdSphere d :=
  sphereHomeomorph d (spherePoint d)

abbrev StandardBouquetSource (ds : BouquetSpec) :=
  PUnit.{1} ⊕ (Σ i : Fin ds.length, EuclideanSphereJoin.StdSphere (ds.get i).val)

private def standardBouquetBases (ds : BouquetSpec) : Set (StandardBouquetSource ds) :=
  {z | Sum.elim (fun _ => True) (fun x => x.2 = standardSphereBase (ds.get x.1).val) z}

/-- The ordinary quotient bouquet of actual Euclidean spheres; an empty list is a point. -/
abbrev StandardBouquet (ds : BouquetSpec) :=
  FiniteConeUnionWedge.Collapse (standardBouquetBases ds)

private def sphereBouquetQuotientHomeomorph (ds : BouquetSpec) :
    CoordinateBouquetQuotient ds ≃ₜ StandardBouquet ds := by
  let h := (Homeomorph.refl PUnit.{1}).sumCongr (sphereFamilyHomeomorph ds)
  apply Homeomorph.Quotient.congr h
  intro z w
  change (z = w ∨ (z ∈ bouquetBases ds ∧ w ∈ bouquetBases ds)) ↔
    (h z = h w ∨ (h z ∈ standardBouquetBases ds ∧ h w ∈ standardBouquetBases ds))
  have hb (z : BouquetSource ds) : h z ∈ standardBouquetBases ds ↔ z ∈ bouquetBases ds := by
    rcases z with _ | ⟨i, x⟩
    · rfl
    · exact (sphereHomeomorph (ds.get i).val).injective.eq_iff
  rw [h.injective.eq_iff, hb, hb]

/-- The concrete sphere bouquet quotient and the finite-coordinate realization coincide topologically. -/
def standardBouquetHomeomorph (ds : BouquetSpec) :
    FiniteSimplicialJoin.Space (bouquetComplex ds) ≃ₜ StandardBouquet ds :=
  (bouquetQuotientHomeomorph ds).symm.trans (sphereBouquetQuotientHomeomorph ds)

/-- Disjoint tagged components. A family of empty lists is a family of distinct points. -/
abbrev NormalVertices (m : ℕ) (b : Fin m → BouquetSpec) := Σ i, BouquetVertices (b i)

def normalComplex (m : ℕ) (b : Fin m → BouquetSpec) :
    PreAbstractSimplicialComplex (NormalVertices m b) :=
  coproductComplex (fun i => bouquetComplex (b i))

private theorem normalVertex_face (m : ℕ) (b : Fin m → BouquetSpec) (i : Fin m) :
    ({⟨i, none⟩} : Finset (NormalVertices m b)) ∈ normalComplex m b := by
  apply (mem_coproductComplex (fun i => bouquetComplex (b i)) _).mpr
  exact ⟨i, {none}, bouquetVertex_face (b i), Finset.image_singleton _ _⟩

def normalPoint (m : ℕ) (b : Fin m → BouquetSpec) (i : Fin m) :
    FiniteSimplicialJoin.Space (normalComplex m b) :=
  FiniteVertexCylinder.vertexPoint _ ⟨i, none⟩ (normalVertex_face m b i)

def normalHomeomorph (m : ℕ) (b : Fin m → BouquetSpec) :
    FiniteSimplicialJoin.Space (normalComplex m b) ≃ₜ
      (Σ i : Fin m, FiniteSimplicialJoin.Space (bouquetComplex (b i))) :=
  (coproductHomeomorph (fun i => bouquetComplex (b i))).symm

def WPlus {V : Type*} [Fintype V] [DecidableEq V]
    (M : PreAbstractSimplicialComplex V) : Prop :=
  ∃ m : ℕ, ∃ _ : 0 < m, ∃ b : Fin m → BouquetSpec,
    Nonempty (FiniteSimplicialJoin.Space M ≃ₕ FiniteSimplicialJoin.Space (normalComplex m b))

private theorem normalPoint_embedding (m : ℕ) (b : Fin m → BouquetSpec) (i : Fin m) :
    (normalHomeomorph m b).symm ⟨i, bouquetPoint (b i)⟩ = normalPoint m b i := by
  apply Subtype.ext
  change coordinateLinear ⟨(@Sigma.mk (Fin m) (fun i => BouquetVertices (b i)) i),
      sigma_mk_injective⟩
    (Pi.single (none : BouquetVertices (b i)) 1) =
      Pi.single (⟨i, none⟩ : NormalVertices m b) 1
  exact coordinateLinear_single _ _

private def normalPath (m : ℕ) (b : Fin m → BouquetSpec)
    (x : FiniteSimplicialJoin.Space (normalComplex m b)) :
    Path x (normalPoint m b ((normalHomeomorph m b) x).1) := by
  let z := normalHomeomorph m b x
  let p := (bouquetPath (b z.1) z.2).map
    ((normalHomeomorph m b).symm.continuous.comp
      (@continuous_sigmaMk (Fin m)
        (fun i => FiniteSimplicialJoin.Space (bouquetComplex (b i)))
        (fun i => inferInstance) z.1))
  exact p.cast ((normalHomeomorph m b).symm_apply_apply x).symm
    (normalPoint_embedding m b z.1).symm

/-- Both actual native cylinder retractions are used; the image component is selected by the map. -/
private theorem based_normalization {V : Type*} [Fintype V] [DecidableEq V]
    (M : PreAbstractSimplicialComplex V) (hM : WPlus M)
    (a : V) (ha : ({a} : Finset V) ∈ M) :
    ∃ m : ℕ, ∃ hm : 0 < m, ∃ b : Fin m → BouquetSpec, ∃ i : Fin m,
      Nonempty (SingletonRetractionBasedInverse.BasedEquivalence
        (FiniteVertexCylinder.vertexPoint M a ha) (normalPoint m b i)) := by
  obtain ⟨m, hm, b, ⟨e⟩⟩ := hM
  let x := FiniteVertexCylinder.vertexPoint M a ha
  let z := e.toFun x
  let i := ((normalHomeomorph m b) z).1
  obtain ⟨E, _, _⟩ := SingletonRetractionBasedInverse.based_inverse x (normalPoint m b i)
    (nativeCylinder M a ha)
    (nativeCylinder (normalComplex m b) ⟨i, none⟩ (normalVertex_face m b i))
    e.toFun e.invFun e.left_inv.some e.right_inv.some (normalPath m b z)
  exact ⟨m, hm, b, i, ⟨E⟩⟩

section ConeCovers

variable {V : Type*} [Fintype V] [DecidableEq V]

private def finiteConeCover (X Y C : PreAbstractSimplicialComplex V)
    (a b : V) (ha : ({a} : Finset V) ∈ X) (hb : ({b} : Finset V) ∈ Y)
    (haC : ({a} : Finset V) ∈ C) (hbC : ({b} : Finset V) ∈ C)
    (hXY : X ⊓ Y ≤ C) :
    FiniteConeUnionWedge.CollapseCover
      (FiniteVertexCylinder.vertexPoint X a ha) (FiniteVertexCylinder.vertexPoint Y b hb)
      {z : FiniteSimplicialJoin.Space (X ⊔ Y) | z.val ∈ FiniteConeCollapse.realization C} where
  left := FiniteConeUnionWedge.realizationInclusion le_sup_left
  right := FiniteConeUnionWedge.realizationInclusion le_sup_right
  left_injective := fun x y h => Subtype.ext
    (congrArg (fun z : FiniteSimplicialJoin.Space (X ⊔ Y) => z.val) h)
  right_injective := fun x y h => Subtype.ext
    (congrArg (fun z : FiniteSimplicialJoin.Space (X ⊔ Y) => z.val) h)
  left_closed := by
    letI := FiniteSimplicialJoin.realizationCompactSpace X
    exact (FiniteConeUnionWedge.realizationInclusion
      (show X ≤ X ⊔ Y from le_sup_left)).continuous.isClosedMap
  right_closed := by
    letI := FiniteSimplicialJoin.realizationCompactSpace Y
    exact (FiniteConeUnionWedge.realizationInclusion
      (show Y ≤ X ⊔ Y from le_sup_right)).continuous.isClosedMap
  covers := by
    intro z
    obtain ⟨s, hs, hz⟩ := z.property
    rcases hs with hs | hs
    · exact ⟨Sum.inl ⟨z.val, s, hs, hz⟩, Subtype.ext rfl⟩
    · exact ⟨Sum.inr ⟨z.val, s, hs, hz⟩, Subtype.ext rfl⟩
  overlap := by
    intro x y h
    have hy : x.val ∈ FiniteConeCollapse.realization Y :=
      (congrArg Subtype.val h).symm ▸ y.property
    obtain ⟨s, hs, hx⟩ := (Set.ext_iff.mp
      (FiniteConeUnionWedge.realization_intersection X Y) x.val).mpr ⟨x.property, hy⟩
    exact ⟨s, hXY hs, hx⟩
  left_base := (FiniteVertexCylinder.vertexPoint C a haC).property
  right_base := (FiniteVertexCylinder.vertexPoint C b hbC).property

private def coneCoverEquiv (X Y C : PreAbstractSimplicialComplex V)
    (a b : V) (ha : ({a} : Finset V) ∈ X) (hb : ({b} : Finset V) ∈ Y)
    (haC : ({a} : Finset V) ∈ C) (hbC : ({b} : Finset V) ∈ C)
    (hC : C ≤ X ⊔ Y) (hXY : X ⊓ Y ≤ C)
    (hcone : ∀ s ∈ C, insert a s ∈ C) :
    let P := finiteConeCover X Y C a b ha hb haC hbC hXY
    FiniteSimplicialJoin.Space (X ⊔ Y) ≃ₕ
      FiniteConeUnionWedge.Wedge
        (Quotient.mk (FiniteConeUnionWedge.subsetSetoid (P.left ⁻¹'
          {z | z.val ∈ FiniteConeCollapse.realization C}))
          (FiniteVertexCylinder.vertexPoint X a ha))
        (Quotient.mk (FiniteConeUnionWedge.subsetSetoid (P.right ⁻¹'
          {z | z.val ∈ FiniteConeCollapse.realization C}))
          (FiniteVertexCylinder.vertexPoint Y b hb)) := by
  let Q : FiniteConeCollapse.ConePair V :=
    ⟨X ⊔ Y, C, hC, a, haC, hcone⟩
  let P := finiteConeCover X Y C a b ha hb haC hbC hXY
  exact Q.collapseEquiv.trans P.quotientWedgeHomeomorph.symm.toHomotopyEquiv

end ConeCovers

section DisjointJoin

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

private theorem join_left_vertex (M : PreAbstractSimplicialComplex V)
    (Z : PreAbstractSimplicialComplex W) (a : V) (ha : ({a} : Finset V) ∈ M) :
    ({Sum.inl a} : Finset (V ⊕ W)) ∈ FiniteSimplicialJoin.simplicialJoin M Z := by
  have hl : ({Sum.inl a} : Finset (V ⊕ W)).toLeft = {a} := by ext v; simp
  have hr : ({Sum.inl a} : Finset (V ⊕ W)).toRight = ∅ := by ext v; simp
  exact ⟨by simp, Or.inr (hl.symm ▸ ha), Or.inl hr⟩

private theorem join_right_vertex (M : PreAbstractSimplicialComplex V)
    (Z : PreAbstractSimplicialComplex W) (b : W) (hb : ({b} : Finset W) ∈ Z) :
    ({Sum.inr b} : Finset (V ⊕ W)) ∈ FiniteSimplicialJoin.simplicialJoin M Z := by
  have hl : ({Sum.inr b} : Finset (V ⊕ W)).toLeft = ∅ := by ext v; simp
  have hr : ({Sum.inr b} : Finset (V ⊕ W)).toRight = {b} := by ext v; simp
  exact ⟨by simp, Or.inl hl, Or.inr (hr.symm ▸ hb)⟩

private theorem join_mono_left {M N : PreAbstractSimplicialComplex V}
    (h : M ≤ N) (Z : PreAbstractSimplicialComplex W) :
    FiniteSimplicialJoin.simplicialJoin M Z ≤ FiniteSimplicialJoin.simplicialJoin N Z := by
  rintro s ⟨hs, hl, hr⟩
  exact ⟨hs, hl.imp id (fun hm => h hm), hr⟩

private theorem vertexComplex_le (M : PreAbstractSimplicialComplex V)
    (a : V) (ha : ({a} : Finset V) ∈ M) : vertexComplex a ≤ M := by
  rintro s rfl
  exact ha

private theorem join_union (M N : PreAbstractSimplicialComplex V)
    (Z : PreAbstractSimplicialComplex W) :
    FiniteSimplicialJoin.simplicialJoin (M ⊔ N) Z =
      FiniteSimplicialJoin.simplicialJoin M Z ⊔ FiniteSimplicialJoin.simplicialJoin N Z := by
  apply SetLike.ext
  intro s
  change (s.Nonempty ∧ (s.toLeft = ∅ ∨ (s.toLeft ∈ M ∨ s.toLeft ∈ N)) ∧
    (s.toRight = ∅ ∨ s.toRight ∈ Z)) ↔
    ((s.Nonempty ∧ (s.toLeft = ∅ ∨ s.toLeft ∈ M) ∧ (s.toRight = ∅ ∨ s.toRight ∈ Z)) ∨
    (s.Nonempty ∧ (s.toLeft = ∅ ∨ s.toLeft ∈ N) ∧ (s.toRight = ∅ ∨ s.toRight ∈ Z)))
  tauto

private theorem disjoint_join_overlap (M N : PreAbstractSimplicialComplex V)
    (Z : PreAbstractSimplicialComplex W) (hMN : M ⊓ N = ⊥) :
    FiniteSimplicialJoin.simplicialJoin M Z ⊓ FiniteSimplicialJoin.simplicialJoin N Z =
      FiniteSimplicialJoin.simplicialJoin ⊥ Z := by
  apply SetLike.ext
  intro s
  have hno : ¬(s.toLeft ∈ M ∧ s.toLeft ∈ N) := by
    intro h
    have hb : s.toLeft ∈ (⊥ : PreAbstractSimplicialComplex V) := hMN ▸ h
    exact hb
  change ((s.Nonempty ∧ (s.toLeft = ∅ ∨ s.toLeft ∈ M) ∧
    (s.toRight = ∅ ∨ s.toRight ∈ Z)) ∧
    (s.Nonempty ∧ (s.toLeft = ∅ ∨ s.toLeft ∈ N) ∧ (s.toRight = ∅ ∨ s.toRight ∈ Z))) ↔
    (s.Nonempty ∧ (s.toLeft = ∅ ∨ False) ∧ (s.toRight = ∅ ∨ s.toRight ∈ Z))
  tauto

private theorem join_vertex_cone (Z : PreAbstractSimplicialComplex W) (a : V) :
    ∀ s ∈ FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z,
      insert (Sum.inl a) s ∈ FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z := by
  rintro s ⟨_, hl, hr⟩
  refine ⟨Finset.insert_nonempty _ _, Or.inr ?_, ?_⟩
  · change (insert (Sum.inl a) s).toLeft = {a}
    rw [Finset.toLeft_insert_inl]
    rcases hl with hl | hl
    · rw [hl]; simp
    · change s.toLeft = {a} at hl
      rw [hl]; simp
  · simpa only [Finset.toRight_insert_inl] using hr

/-- The first actual two-component split collapses `a*Z`, and retains the right base quotient. -/
private def disjointJoinConeSplit (M N : PreAbstractSimplicialComplex V)
    (Z : PreAbstractSimplicialComplex W) (hMN : M ⊓ N = ⊥)
    (a : V) (ha : ({a} : Finset V) ∈ M) (b : W) (hb : ({b} : Finset W) ∈ Z) :
    FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin (M ⊔ N) Z) ≃ₕ
      FiniteConeUnionWedge.Wedge
        (Quotient.mk (FiniteConeUnionWedge.subsetSetoid
          {x : FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin M Z) |
            x.val ∈ FiniteConeCollapse.realization
              (FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z)})
          (FiniteVertexCylinder.vertexPoint _ _ (join_left_vertex M Z a ha)))
        (Quotient.mk (FiniteConeUnionWedge.subsetSetoid
          {y : FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin N Z) |
            y.val ∈ FiniteConeCollapse.realization
              (FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z)})
          (FiniteVertexCylinder.vertexPoint _ _ (join_right_vertex N Z b hb))) := by
  rw [join_union]
  have hCX : FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z ≤
      FiniteSimplicialJoin.simplicialJoin M Z := join_mono_left (vertexComplex_le M a ha) Z
  have hXY : FiniteSimplicialJoin.simplicialJoin M Z ⊓
      FiniteSimplicialJoin.simplicialJoin N Z ≤
      FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z := by
    rw [disjoint_join_overlap M N Z hMN]
    exact join_mono_left bot_le Z
  exact coneCoverEquiv _ _ _ (Sum.inl a) (Sum.inr b)
    (join_left_vertex M Z a ha) (join_right_vertex N Z b hb)
    (join_left_vertex (vertexComplex a) Z a rfl)
    (join_right_vertex (vertexComplex a) Z b hb)
    (hCX.trans le_sup_left) hXY (join_vertex_cone Z a)

end DisjointJoin

#print axioms sphereHomeomorph
#print axioms bouquetQuotientHomeomorph
#print axioms normalHomeomorph
#print axioms based_normalization
#print axioms disjointJoinConeSplit

end D5.S3.Geometry.FiniteComponentClosure
