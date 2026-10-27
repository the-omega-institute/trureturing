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
        by nlinarith [mul_nonneg (sub_nonneg.mpr s.property.2)
          (sub_nonneg.mpr a.property.2),
          mul_nonneg s.property.1 (sub_nonneg.mpr b.property.2)]⟩⟩ : I))
  continuous_toFun := continuous_quotient_mk'.comp (by fun_prop)
  source' := by congr 1; apply Prod.ext rfl; apply Prod.ext rfl; apply Subtype.ext; simp
  target' := by congr 1; apply Prod.ext rfl; apply Prod.ext rfl; apply Subtype.ext; simp

private def joinPath (x₀ : X) (y₀ : Y)
    (z : FiniteSimplicialJoin.OrdinaryJoin X Y) :
    Path z (Quotient.mk _ (x₀, y₀, (0 : I))) := by
  obtain ⟨⟨x, y, t⟩, rfl⟩ := Quotient.exists_rep z
  have h₀ : (Quotient.mk _ (x, y, (0 : I)) : FiniteSimplicialJoin.OrdinaryJoin X Y) =
      Quotient.mk _ (x, y₀, (0 : I)) :=
    Quotient.sound ⟨rfl, Or.inr rfl, Or.inl rfl⟩
  have h₁ : (Quotient.mk _ (x, y₀, (1 : I)) : FiniteSimplicialJoin.OrdinaryJoin X Y) =
      Quotient.mk _ (x₀, y₀, (1 : I)) :=
    Quotient.sound ⟨rfl, Or.inl rfl, Or.inr rfl⟩
  exact ((joinSegment x y t 0).trans ((joinSegment x y₀ 0 1).cast h₀.symm rfl)).trans
    ((joinSegment x₀ y₀ 1 0).cast h₁.symm rfl)

/-- The point factor is a contractible cone, even when the other factor is disconnected. -/
private def pointJoinContraction [Subsingleton X] (x₀ : X) (y₀ : Y) :
    (ContinuousMap.id (FiniteSimplicialJoin.OrdinaryJoin X Y)).Homotopy
      (ContinuousMap.const _ (Quotient.mk _ (x₀, y₀, (0 : I)))) where
  toFun z := Quotient.map' (fun p => (p.1, p.2.1,
    (⟨(1 - (z.1 : ℝ)) * (p.2.2 : ℝ),
      ⟨mul_nonneg (sub_nonneg.mpr z.1.property.2) p.2.2.property.1,
        by nlinarith [mul_nonneg (sub_nonneg.mpr z.1.property.2)
          (sub_nonneg.mpr p.2.2.property.2)]⟩⟩ : I)))
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
      have := y.property
      rw [EuclideanSpace.sphere_zero_eq 1 (by norm_num)] at this
      simpa using this
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

instance sphereVerticesFintype (d : ℕ) : Fintype (SphereVertices d) := by
  induction d with
  | zero => exact inferInstanceAs (Fintype Bool)
  | succ d ih => exact @Sum.instFintype _ _ ih inferInstance

instance sphereVerticesDecidableEq (d : ℕ) : DecidableEq (SphereVertices d) :=
  Classical.decEq _

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
    change ({Sum.inl (sphereVertex d)} : Finset (SphereVertices d ⊕ Bool)).Nonempty ∧ _
    exact ⟨by simp, Or.inr (by simpa using ih), Or.inl (by simp)⟩

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
      funext v
      cases v <;>
        simp [e, FiniteSimplicialJoin.joinHomeomorph, FiniteSimplicialJoin.realizationMap,
          FiniteSimplicialJoin.representative, spherePoint, sphereVertex,
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
  map_add' x y := by ext w; simp [ite_add_ite, Finset.sum_add_distrib]
  map_smul' c x := by ext w; simp [Finset.mul_sum, mul_ite]

private theorem coordinateLinear_at (e : V ↪ W) (x : V → ℝ) (v : V) :
    coordinateLinear e x (e v) = x v := by
  simp [coordinateLinear, e.injective.eq_iff]

private theorem coordinateLinear_single (e : V ↪ W) (v : V) :
    coordinateLinear e (Pi.single v 1) = Pi.single (e v) 1 := by
  ext w
  simp [coordinateLinear, Pi.single_apply, Finset.sum_ite_irrel,
    Finset.sum_ite_eq', eq_comm]

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
    simp only [← Set.image_comp, coordinateLinear_single, Finset.coe_image]
    rfl
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

private def coordinateHomeomorph (M : PreAbstractSimplicialComplex V) (e : V ↪ W) :
    FiniteSimplicialJoin.Space M ≃ₜ FiniteSimplicialJoin.Space (M.map e) where
  toFun x := ⟨coordinateLinear e x.val, by
    rw [realization_map]
    exact ⟨x.val, x.property, rfl⟩⟩
  invFun y := ⟨fun v => y.val (e v), by
    obtain ⟨x, hx, he⟩ := (realization_map M e ▸ y.property)
    have h : (fun v => y.val (e v)) = x := by
      funext v; rw [← he, coordinateLinear_at]
    exact h ▸ hx⟩
  left_inv x := Subtype.ext (funext (coordinateLinear_at e x.val))
  right_inv y := by
    apply Subtype.ext
    obtain ⟨x, _, he⟩ := (realization_map M e ▸ y.property)
    rw [← he]
    congr 1
    exact funext (coordinateLinear_at e x)
  continuous_toFun := Continuous.subtype_mk
    ((coordinateLinear e).continuous_of_finiteDimensional.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (by fun_prop) _

end CoordinateEmbeddings

abbrev BouquetSpec := List {d : ℕ // 0 < d}

/-- One common vertex and the separately tagged nonbase vertices of every sphere. -/
def BouquetVertices (ds : BouquetSpec) :=
  Option (Σ i : Fin ds.length,
    {v : SphereVertices (ds.get i).val // v ≠ sphereVertex (ds.get i).val})

instance bouquetVerticesFintype (ds : BouquetSpec) : Fintype (BouquetVertices ds) := by
  unfold BouquetVertices
  infer_instance

instance bouquetVerticesDecidableEq (ds : BouquetSpec) : DecidableEq (BouquetVertices ds) :=
  Classical.decEq _

private def bouquetInclusion (ds : BouquetSpec) (i : Fin ds.length) :
    SphereVertices (ds.get i).val ↪ BouquetVertices ds where
  toFun v := if h : v = sphereVertex (ds.get i).val then none else some ⟨i, ⟨v, h⟩⟩
  inj' := by
    intro v w h
    dsimp at h
    split_ifs at h with hv hw hw
    · exact hv.trans hw.symm
    · cases h
    · cases h
    · exact congrArg (fun z => z.val) (Sigma.mk.inj_iff.mp (Option.some.inj h)).2

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

/-- Disjoint tagged components. A family of empty lists is a family of distinct points. -/
def NormalVertices (m : ℕ) (b : Fin m → BouquetSpec) := Σ i, BouquetVertices (b i)

instance normalVerticesFintype (m : ℕ) (b : Fin m → BouquetSpec) :
    Fintype (NormalVertices m b) := by unfold NormalVertices; infer_instance

instance normalVerticesDecidableEq (m : ℕ) (b : Fin m → BouquetSpec) :
    DecidableEq (NormalVertices m b) := Classical.decEq _

def normalComplex (m : ℕ) (b : Fin m → BouquetSpec) :
    PreAbstractSimplicialComplex (NormalVertices m b) :=
  ⨆ i, (bouquetComplex (b i)).map (Sigma.mk i)

def normalPoint (m : ℕ) (b : Fin m → BouquetSpec) (i : Fin m) :
    FiniteSimplicialJoin.Space (normalComplex m b) :=
  FiniteVertexCylinder.vertexPoint _ ⟨i, none⟩ (by
    change _ ∈ ⋃ K ∈ Set.range (fun i =>
      (bouquetComplex (b i)).map (Sigma.mk i)), K.faces
    exact Set.mem_iUnion₂.mpr ⟨_, ⟨i, rfl⟩, {none}, bouquetVertex_face (b i), by simp⟩)

def WPlus {V : Type*} [Fintype V] [DecidableEq V]
    (M : PreAbstractSimplicialComplex V) : Prop :=
  ∃ m : ℕ, ∃ _ : 0 < m, ∃ b : Fin m → BouquetSpec,
    Nonempty (FiniteSimplicialJoin.Space M ≃ₕ FiniteSimplicialJoin.Space (normalComplex m b))

#print axioms sphereHomeomorph

end D5.S3.Geometry.FiniteComponentClosure
