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

section ConeBaseSuspension

variable {Z : Type*} [TopologicalSpace Z]

private abbrev TopologicalCone (Z : Type*) [TopologicalSpace Z] :=
  FiniteSimplicialJoin.OrdinaryJoin Unit Z

private def coneHeight : C(TopologicalCone Z, I) where
  toFun := Quotient.lift (fun p => p.2.2) (fun _ _ h => h.1)
  continuous_toFun := (by fun_prop : Continuous
    (fun p : Unit × Z × I => p.2.2)).quotient_lift _

private abbrev ConeBaseQuotient (Z : Type*) [TopologicalSpace Z] :=
  FiniteConeUnionWedge.Collapse {x : TopologicalCone Z | coneHeight x = 1}

private def halfParameter (b : Bool) (t : I) : I :=
  ⟨(1 + (if b then (1 : ℝ) else -1) * (t : ℝ)) / 2, by
    cases b <;> norm_num <;> constructor <;> linarith [t.property.1, t.property.2]⟩

private theorem halfParameter_continuous :
    Continuous (fun z : Bool × I => halfParameter z.1 z.2) := by
  apply Continuous.subtype_mk
  exact (continuous_const.add
    ((continuous_of_discreteTopology (f := fun b : Bool => if b then (1 : ℝ) else -1)).comp
      continuous_fst |>.mul (continuous_subtype_val.comp continuous_snd))).div_const 2

private def coneClass (z : Z) (t : I) : ConeBaseQuotient Z :=
  Quotient.mk _ (Quotient.mk _ ((), z, t))

private theorem coneClass_zero (z w : Z) : coneClass z 0 = coneClass w 0 :=
  congrArg (Quotient.mk _) (Quotient.sound ⟨rfl, Or.inr rfl, Or.inl rfl⟩)

private theorem coneClass_one (z w : Z) : coneClass z 1 = coneClass w 1 :=
  Quotient.sound (Or.inr ⟨rfl, rfl⟩)

private def suspensionToConeBase :
    C(FiniteSimplicialJoin.OrdinaryJoin Z Bool, ConeBaseQuotient Z) where
  toFun := Quotient.lift (fun p => coneClass p.1 (halfParameter p.2.1 p.2.2)) (by
    rintro ⟨z, b, t⟩ ⟨w, c, u⟩ ⟨ht, hz, hb⟩
    dsimp at ht hz hb ⊢
    subst u
    rcases hb with hb | hb
    · subst t
      have h (d : Bool) : halfParameter d 0 = (⟨1 / 2, by norm_num⟩ : I) := by
        apply Subtype.ext; simp [halfParameter]
      rw [h, h]
      rcases hz with hz | rfl
      · norm_num at hz
      · rfl
    · subst c
      rcases hz with hz | rfl
      · subst t
        cases b
        · simpa [halfParameter] using coneClass_zero z w
        · simpa [halfParameter] using coneClass_one z w
      · rfl)
  continuous_toFun := by
    apply Continuous.quotient_lift
    apply continuous_quotient_mk'.comp
    apply continuous_quotient_mk'.comp
    exact continuous_const.prodMk
      (continuous_fst.prodMk (halfParameter_continuous.comp continuous_snd))

private def lowerParameter (t : I) : I :=
  ⟨max 0 (1 - 2 * (t : ℝ)), ⟨le_max_left _ _,
    max_le (by norm_num) (by linarith [t.property.1])⟩⟩

private def upperParameter (t : I) : I :=
  ⟨max 0 (2 * (t : ℝ) - 1), ⟨le_max_left _ _,
    max_le (by norm_num) (by linarith [t.property.2])⟩⟩

private def foldedSuspension : C(Z × I, FiniteSimplicialJoin.OrdinaryJoin Z Bool) where
  toFun p := if (p.2 : ℝ) ≤ 1 / 2 then
    Quotient.mk _ (p.1, false, lowerParameter p.2)
    else Quotient.mk _ (p.1, true, upperParameter p.2)
  continuous_toFun := by
    apply Continuous.if_le
      (continuous_quotient_mk'.comp (continuous_fst.prodMk
        (continuous_const.prodMk (by dsimp [lowerParameter]; fun_prop))))
      (continuous_quotient_mk'.comp (continuous_fst.prodMk
        (continuous_const.prodMk (by dsimp [upperParameter]; fun_prop))))
      (continuous_subtype_val.comp continuous_snd) continuous_const
    intro p hp
    change (p.2 : ℝ) = 1 / 2 at hp
    apply Quotient.sound
    have hl : lowerParameter p.2 = 0 := by apply Subtype.ext; simp [lowerParameter, hp]
    have hu : upperParameter p.2 = 0 := by apply Subtype.ext; simp [upperParameter, hp]
    exact ⟨hl.trans hu.symm, Or.inr rfl, Or.inl hl⟩

private theorem foldedSuspension_zero (z w : Z) :
    foldedSuspension (z, (0 : I)) = foldedSuspension (w, (0 : I)) := by
  change (if _ then _ else _) = (if _ then _ else _)
  norm_num
  apply Quotient.sound
  exact ⟨rfl, Or.inl (Subtype.ext (by norm_num [lowerParameter])), Or.inr rfl⟩

private theorem foldedSuspension_one (z w : Z) :
    foldedSuspension (z, (1 : I)) = foldedSuspension (w, (1 : I)) := by
  change (if _ then _ else _) = (if _ then _ else _)
  norm_num
  apply Quotient.sound
  exact ⟨rfl, Or.inl (Subtype.ext (by norm_num [upperParameter])), Or.inr rfl⟩

private def coneToSuspension : C(TopologicalCone Z, FiniteSimplicialJoin.OrdinaryJoin Z Bool) where
  toFun := Quotient.lift (fun p => foldedSuspension (p.2.1, p.2.2)) (by
    rintro p q ⟨ht, _, hz⟩
    rcases hz with hz | hz
    · simpa only [hz, ← ht] using foldedSuspension_zero p.2.1 q.2.1
    · rw [ht, hz])
  continuous_toFun := (foldedSuspension.continuous.comp
    (continuous_snd.fst.prodMk continuous_snd.snd)).quotient_lift _

private def coneBaseToSuspension :
    C(ConeBaseQuotient Z, FiniteSimplicialJoin.OrdinaryJoin Z Bool) where
  toFun := Quotient.lift coneToSuspension (by
    rintro x y (rfl | ⟨hx, hy⟩)
    · rfl
    · induction x using Quotient.inductionOn with
      | h p =>
        induction y using Quotient.inductionOn with
        | h q =>
          change p.2.2 = 1 at hx
          change q.2.2 = 1 at hy
          change foldedSuspension (p.2.1, p.2.2) = foldedSuspension (q.2.1, q.2.2)
          rw [hx, hy]
          exact foldedSuspension_one _ _)
  continuous_toFun := coneToSuspension.continuous.quotient_lift _

private theorem coneBase_roundtrip (x : ConeBaseQuotient Z) :
    suspensionToConeBase (coneBaseToSuspension x) = x := by
  induction x using Quotient.inductionOn with
  | h x =>
    induction x using Quotient.inductionOn with
    | h p =>
      rcases p with ⟨⟨⟩, z, t⟩
      change suspensionToConeBase (foldedSuspension (z, t)) = coneClass z t
      change suspensionToConeBase (if _ then _ else _) = _
      split_ifs with ht
      · change coneClass z (halfParameter false (lowerParameter t)) = coneClass z t
        have h : halfParameter false (lowerParameter t) = t := by
          apply Subtype.ext
          dsimp [halfParameter, lowerParameter]
          rw [max_eq_right (by linarith)]
          ring
        rw [h]
      · change coneClass z (halfParameter true (upperParameter t)) = coneClass z t
        have h : halfParameter true (upperParameter t) = t := by
          apply Subtype.ext
          dsimp [halfParameter, upperParameter]
          rw [max_eq_right (by linarith)]
          ring
        rw [h]

private theorem suspension_roundtrip (x : FiniteSimplicialJoin.OrdinaryJoin Z Bool) :
    coneBaseToSuspension (suspensionToConeBase x) = x := by
  induction x using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨z, b, t⟩
    change foldedSuspension (z, halfParameter b t) = Quotient.mk _ (z, b, t)
    cases b
    · have ht : (halfParameter false t : ℝ) ≤ 1 / 2 := by
        dsimp [halfParameter]; linarith [t.property.1]
      change (if _ then _ else _) = _
      rw [if_pos ht]
      apply Quotient.sound
      refine ⟨?_, Or.inr rfl, Or.inr rfl⟩
      apply Subtype.ext
      dsimp [lowerParameter, halfParameter]
      have h : 1 - 2 * ((1 + -1 * (t : ℝ)) / 2) = (t : ℝ) := by ring
      rw [h, max_eq_right t.property.1]
    · change (if _ then _ else _) = _
      split_ifs with ht
      · have hz : t = 0 := by
          apply Subtype.ext
          dsimp [halfParameter] at ht
          change (t : ℝ) = 0
          linarith [t.property.1]
        subst t
        apply Quotient.sound
        exact ⟨Subtype.ext (by norm_num [lowerParameter, halfParameter]), Or.inr rfl,
          Or.inl (Subtype.ext (by norm_num [lowerParameter, halfParameter]))⟩
      · apply Quotient.sound
        refine ⟨?_, Or.inr rfl, Or.inr rfl⟩
        apply Subtype.ext
        dsimp [upperParameter, halfParameter]
        have h : 2 * ((1 + 1 * (t : ℝ)) / 2) - 1 = (t : ℝ) := by ring
        rw [h, max_eq_right t.property.1]

/-- Cone/base is the actual unreduced suspension, with both continuous inverse maps. -/
private def coneBaseSuspensionHomeomorph :
    ConeBaseQuotient Z ≃ₜ FiniteSimplicialJoin.OrdinaryJoin Z Bool where
  toFun := coneBaseToSuspension
  invFun := suspensionToConeBase
  left_inv := coneBase_roundtrip
  right_inv := suspension_roundtrip
  continuous_toFun := coneBaseToSuspension.continuous
  continuous_invFun := suspensionToConeBase.continuous

private theorem coneBase_north (x : TopologicalCone Z) (hx : coneHeight x = 1) (z : Z) :
    coneBaseSuspensionHomeomorph (Quotient.mk _ x) =
      Quotient.mk (FiniteSimplicialJoin.ordinaryJoinSetoid Z Bool) (z, true, (1 : I)) := by
  induction x using Quotient.inductionOn with
  | h p =>
    change p.2.2 = 1 at hx
    change foldedSuspension (p.2.1, p.2.2) = _
    rw [hx, foldedSuspension_one p.2.1 z]
    change (if _ then _ else _) = _
    norm_num
    exact congrArg (fun t : I => Quotient.mk
      (FiniteSimplicialJoin.ordinaryJoinSetoid Z Bool) (z, true, t))
      (Subtype.ext (by norm_num [upperParameter]))

end ConeBaseSuspension

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

section VertexGluing

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

private abbrev GluedVertices (a : V) (b : W) := FiniteConeUnionWedge.Wedge a b

private instance (a : V) (b : W) : Fintype (GluedVertices a b) := Fintype.ofFinite _
private instance (a : V) (b : W) : DecidableEq (GluedVertices a b) := Classical.decEq _

private def glueLeft (a : V) (b : W) : V ↪ GluedVertices a b where
  toFun v := Quotient.mk _ (Sum.inl v)
  inj' := by
    intro v w h
    have h := Quotient.exact h
    change (Sum.inl v = Sum.inl w ∨
      ((Sum.inl v = Sum.inl a ∨ Sum.inl v = Sum.inr b) ∧
      (Sum.inl w = Sum.inl a ∨ Sum.inl w = Sum.inr b))) at h
    simp only [Sum.inl.injEq, Sum.inl_ne_inr, or_false] at h
    exact h.elim id (fun h => h.1.trans h.2.symm)

private def glueRight (a : V) (b : W) : W ↪ GluedVertices a b where
  toFun w := Quotient.mk _ (Sum.inr w)
  inj' := by
    intro v w h
    have h := Quotient.exact h
    change (Sum.inr v = Sum.inr w ∨
      ((Sum.inr v = Sum.inl a ∨ Sum.inr v = Sum.inr b) ∧
      (Sum.inr w = Sum.inl a ∨ Sum.inr w = Sum.inr b))) at h
    simp only [Sum.inr.injEq, Sum.inr_ne_inl, false_or] at h
    exact h.elim id (fun h => h.1.trans h.2.symm)

private theorem glue_cross (a : V) (b : W) (v : V) (w : W) :
    glueLeft a b v = glueRight a b w ↔ v = a ∧ w = b := by
  change Quotient.mk _ (Sum.inl v) = Quotient.mk _ (Sum.inr w) ↔ _
  rw [Quotient.eq]
  change (Sum.inl v = Sum.inr w ∨
    ((Sum.inl v = Sum.inl a ∨ Sum.inl v = Sum.inr b) ∧
    (Sum.inr w = Sum.inl a ∨ Sum.inr w = Sum.inr b))) ↔ _
  simp

private def vertexGluing (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    PreAbstractSimplicialComplex (GluedVertices a b) :=
  K.map (glueLeft a b) ⊔ L.map (glueRight a b)

private def gluedLeft (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    C(FiniteSimplicialJoin.Space K, FiniteSimplicialJoin.Space (vertexGluing K L a b)) :=
  (FiniteConeUnionWedge.realizationInclusion le_sup_left).comp
    ⟨coordinateHomeomorph K (glueLeft a b), (coordinateHomeomorph K (glueLeft a b)).continuous⟩

private def gluedRight (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    C(FiniteSimplicialJoin.Space L, FiniteSimplicialJoin.Space (vertexGluing K L a b)) :=
  (FiniteConeUnionWedge.realizationInclusion le_sup_right).comp
    ⟨coordinateHomeomorph L (glueRight a b), (coordinateHomeomorph L (glueRight a b)).continuous⟩

private theorem gluedLeft_injective (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    Function.Injective (gluedLeft K L a b) := by
  intro x y h
  apply (coordinateHomeomorph K (glueLeft a b)).injective
  exact Subtype.ext (congrArg (fun z : FiniteSimplicialJoin.Space
    (vertexGluing K L a b) => z.val) h)

private theorem gluedRight_injective (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    Function.Injective (gluedRight K L a b) := by
  intro x y h
  apply (coordinateHomeomorph L (glueRight a b)).injective
  exact Subtype.ext (congrArg (fun z : FiniteSimplicialJoin.Space
    (vertexGluing K L a b) => z.val) h)

private theorem glued_bases (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W)
    (ha : ({a} : Finset V) ∈ K) (hb : ({b} : Finset W) ∈ L) :
    gluedLeft K L a b (FiniteVertexCylinder.vertexPoint K a ha) =
      gluedRight K L a b (FiniteVertexCylinder.vertexPoint L b hb) := by
  apply Subtype.ext
  change coordinateLinear (glueLeft a b) (Pi.single a 1) =
    coordinateLinear (glueRight a b) (Pi.single b 1)
  rw [coordinateLinear_single, coordinateLinear_single, (glue_cross a b a b).mpr ⟨rfl, rfl⟩]

private theorem glued_intersection (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W)
    (ha : ({a} : Finset V) ∈ K) (hb : ({b} : Finset W) ∈ L)
    (x : FiniteSimplicialJoin.Space K) (y : FiniteSimplicialJoin.Space L)
    (h : gluedLeft K L a b x = gluedRight K L a b y) :
    x = FiniteVertexCylinder.vertexPoint K a ha ∧
      y = FiniteVertexCylinder.vertexPoint L b hb := by
  have hx : x = FiniteVertexCylinder.vertexPoint K a ha := by
    apply coordinates_eq_vertex x a ha
    intro v hv
    have he := congrArg (fun z : FiniteSimplicialJoin.Space (vertexGluing K L a b) =>
      z.val (glueLeft a b v)) h
    have hz : coordinateLinear (glueRight a b) y.val (glueLeft a b v) = 0 := by
      apply Finset.sum_eq_zero
      intro w _
      have hn : glueRight a b w ≠ glueLeft a b v :=
        fun hh => hv ((glue_cross a b v w).mp hh.symm).1
      simp [hn]
    change coordinateLinear (glueLeft a b) x.val (glueLeft a b v) =
      coordinateLinear (glueRight a b) y.val (glueLeft a b v) at he
    rwa [coordinateLinear_at, hz] at he
  refine ⟨hx, gluedRight_injective K L a b ?_⟩
  rw [← h, hx, glued_bases K L a b ha hb]

private def gluingSum (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    C(FiniteSimplicialJoin.Space K ⊕ FiniteSimplicialJoin.Space L,
      FiniteSimplicialJoin.Space (vertexGluing K L a b)) :=
  ⟨Sum.elim (gluedLeft K L a b) (gluedRight K L a b),
    (gluedLeft K L a b).continuous.sumElim (gluedRight K L a b).continuous⟩

private theorem gluingSum_surjective (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    Function.Surjective (gluingSum K L a b) := by
  intro z
  obtain ⟨s, hs, hz⟩ := z.property
  rcases hs with hs | hs
  · let w : FiniteSimplicialJoin.Space (K.map (glueLeft a b)) := ⟨z.val, s, hs, hz⟩
    refine ⟨Sum.inl ((coordinateHomeomorph K (glueLeft a b)).symm w), ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : FiniteSimplicialJoin.Space (K.map (glueLeft a b)) => z.val)
      ((coordinateHomeomorph K (glueLeft a b)).apply_symm_apply w)
  · let w : FiniteSimplicialJoin.Space (L.map (glueRight a b)) := ⟨z.val, s, hs, hz⟩
    refine ⟨Sum.inr ((coordinateHomeomorph L (glueRight a b)).symm w), ?_⟩
    apply Subtype.ext
    exact congrArg (fun z : FiniteSimplicialJoin.Space (L.map (glueRight a b)) => z.val)
      ((coordinateHomeomorph L (glueRight a b)).apply_symm_apply w)

private theorem gluingSum_kernel (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W)
    (ha : ({a} : Finset V) ∈ K) (hb : ({b} : Finset W) ∈ L)
    (x y : FiniteSimplicialJoin.Space K ⊕ FiniteSimplicialJoin.Space L) :
    (FiniteConeUnionWedge.subsetSetoid (FiniteConeUnionWedge.wedgePoints
      (FiniteVertexCylinder.vertexPoint K a ha) (FiniteVertexCylinder.vertexPoint L b hb))).r
      x y ↔ gluingSum K L a b x = gluingSum K L a b y := by
  constructor
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · have h (z) (hz : z ∈ FiniteConeUnionWedge.wedgePoints
          (FiniteVertexCylinder.vertexPoint K a ha) (FiniteVertexCylinder.vertexPoint L b hb)) :
          gluingSum K L a b z = gluedLeft K L a b (FiniteVertexCylinder.vertexPoint K a ha) := by
        rcases hz with rfl | rfl
        · rfl
        · exact (glued_bases K L a b ha hb).symm
      exact (h x hx).trans (h y hy).symm
  · intro h
    rcases x with x | x <;> rcases y with y | y
    · exact Or.inl (congrArg Sum.inl (gluedLeft_injective K L a b h))
    · obtain ⟨rfl, rfl⟩ := glued_intersection K L a b ha hb x y h
      exact Or.inr ⟨Or.inl rfl, Or.inr rfl⟩
    · obtain ⟨rfl, rfl⟩ := glued_intersection K L a b ha hb y x h.symm
      exact Or.inr ⟨Or.inr rfl, Or.inl rfl⟩
    · exact Or.inl (congrArg Sum.inr (gluedRight_injective K L a b h))

/-- The quotient wedge is homeomorphic to the actual finite coordinate vertex gluing. -/
private def vertexGluingHomeomorph (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W)
    (ha : ({a} : Finset V) ∈ K) (hb : ({b} : Finset W) ∈ L) :
    FiniteConeUnionWedge.Wedge (FiniteVertexCylinder.vertexPoint K a ha)
      (FiniteVertexCylinder.vertexPoint L b hb) ≃ₜ
      FiniteSimplicialJoin.Space (vertexGluing K L a b) := by
  letI := FiniteSimplicialJoin.realizationCompactSpace K
  letI := FiniteSimplicialJoin.realizationCompactSpace L
  have hq : IsQuotientMap (gluingSum K L a b) :=
    (gluingSum K L a b).continuous.isClosedMap.isQuotientMap
      (gluingSum K L a b).continuous (gluingSum_surjective K L a b)
  exact (Homeomorph.Quotient.congrRight (gluingSum_kernel K L a b ha hb)).trans
    (Topology.IsQuotientMap.homeomorph (f := gluingSum K L a b) hq)

/- Concrete carrier for selected-component gluing. -/
private abbrev SelectedGluedVertices (a : V) (b : W) :=
  FiniteConeUnionWedge.Wedge a b

private def selectedVertexGluing (K : PreAbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    PreAbstractSimplicialComplex (SelectedGluedVertices a b) :=
  vertexGluing K L a b

end VertexGluing

section ConeCovers

private def wedgeSubsingletonHomeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Subsingleton Y] (a : X) (b : Y) :
    FiniteConeUnionWedge.Wedge a b ≃ₜ X := by
  let f : X ⊕ Y → X := Sum.elim id (fun _ => a)
  have hc : Continuous f := continuous_id.sumElim continuous_const
  have hq : IsQuotientMap f := IsQuotientMap.of_inverse continuous_inl hc (fun _ => rfl)
  refine (Homeomorph.Quotient.congrRight (r' := Setoid.ker f) ?_).trans
    (Topology.IsQuotientMap.homeomorph (f := ⟨f, hc⟩) hq)
  intro z w
  change (z = w ∨
    ((z = Sum.inl a ∨ z = Sum.inr b) ∧ (w = Sum.inl a ∨ w = Sum.inr b))) ↔ f z = f w
  rcases z with x | y <;> rcases w with x' | y'
  · simp [f]
    intro hx hx'
    exact hx.trans hx'.symm
  · have hy : y' = b := Subsingleton.elim _ _
    simp [f, hy]
  · have hy : y = b := Subsingleton.elim _ _
    simp [f, hy, eq_comm]
  · have hy : y = y' := Subsingleton.elim _ _
    simp [f, hy]

private def wedgeHomeomorph {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (a : X) (b : Y) (e : X ≃ₜ X') (d : Y ≃ₜ Y') :
    FiniteConeUnionWedge.Wedge a b ≃ₜ FiniteConeUnionWedge.Wedge (e a) (d b) := by
  apply Homeomorph.Quotient.congr (e.sumCongr d)
  intro x y
  have h (w : X ⊕ Y) :
      (e.sumCongr d) w ∈ FiniteConeUnionWedge.wedgePoints (e a) (d b) ↔
        w ∈ FiniteConeUnionWedge.wedgePoints a b := by
    cases w <;> simp [FiniteConeUnionWedge.wedgePoints, Homeomorph.sumCongr,
      e.injective.eq_iff, d.injective.eq_iff]
  change (x = y ∨ (_ ∧ _)) ↔ (_ = _ ∨ (_ ∧ _))
  rw [(e.sumCongr d).injective.eq_iff, h x, h y]

private def coverCollapseRightHomeomorph {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {a : X} {b : Y} {C : Set Z}
    (P : FiniteConeUnionWedge.CollapseCover a b C)
    (hY : ∀ y, P.right y ∈ C) :
    FiniteConeUnionWedge.Collapse C ≃ₜ
      FiniteConeUnionWedge.Collapse (P.left ⁻¹' C) := by
  letI : Subsingleton (FiniteConeUnionWedge.Collapse (P.right ⁻¹' C)) :=
    ⟨fun x y => Quotient.inductionOn₂ x y
      (fun x y => Quotient.sound (Or.inr ⟨hY x, hY y⟩))⟩
  exact P.quotientWedgeHomeomorph.symm.trans
    (wedgeSubsingletonHomeomorph (Quotient.mk _ a) (Quotient.mk _ b))

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

/-- Collapsing a whole closed summand leaves the other summand modulo their actual intersection.
No contractibility of either summand or of the intersection is used. -/
private def unionCollapseRightHomeomorph (X Y : PreAbstractSimplicialComplex V)
    (a : V) (haX : ({a} : Finset V) ∈ X) (haY : ({a} : Finset V) ∈ Y) :
    FiniteConeUnionWedge.Collapse
      {z : FiniteSimplicialJoin.Space (X ⊔ Y) |
        z.val ∈ FiniteConeCollapse.realization Y} ≃ₜ
      FiniteConeUnionWedge.Collapse
        {x : FiniteSimplicialJoin.Space X |
          x.val ∈ FiniteConeCollapse.realization Y} :=
  coverCollapseRightHomeomorph
    (finiteConeCover X Y Y a a haX haY haY haY inf_le_right)
    (fun y => y.property)

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

private theorem vertexSpace_eq (a : V) (x : FiniteSimplicialJoin.Space (vertexComplex a)) :
    x.val = Pi.single a 1 := by
  obtain ⟨s, hs, hx⟩ := x.property
  change s = {a} at hs
  rw [hs, ← FiniteConeCollapse.faceSimplex_eq_convexHull] at hx
  exact singleton_coordinates a hx

private def vertexSpaceHomeomorph (a : V) :
    FiniteSimplicialJoin.Space (vertexComplex a) ≃ₜ Unit where
  toFun _ := ()
  invFun _ := FiniteVertexCylinder.vertexPoint (vertexComplex a) a rfl
  left_inv x := Subtype.ext (vertexSpace_eq a x).symm
  right_inv _ := rfl
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

private def nativeConeHomeomorph (Z : PreAbstractSimplicialComplex W)
    (a : V) (z : FiniteSimplicialJoin.Space Z) :
    FiniteSimplicialJoin.Space
      (FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z) ≃ₜ
      TopologicalCone (FiniteSimplicialJoin.Space Z) :=
  (FiniteSimplicialJoin.joinHomeomorph (vertexComplex a) Z
    ⟨FiniteVertexCylinder.vertexPoint _ a rfl⟩ ⟨z⟩).symm.trans
    (joinHomeomorph (vertexSpaceHomeomorph a) (Homeomorph.refl _))

private theorem join_base_mem (Z : PreAbstractSimplicialComplex W)
    (z : FiniteSimplicialJoin.Space Z) :
    (Sum.elim (fun _ : V => (0 : ℝ)) z.val) ∈
      FiniteConeCollapse.realization
        (FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z) := by
  obtain ⟨s, hs, hz⟩ := z.property
  rw [← FiniteConeCollapse.faceSimplex_eq_convexHull] at hz
  refine ⟨(∅ : Finset V).disjSum s, ?_, ?_⟩
  · refine ⟨?_, Or.inl Finset.toLeft_disjSum,
      Or.inr (by simpa only [Finset.toRight_disjSum] using hs)⟩
    obtain ⟨w, hw⟩ := (Z.isRelLowerSet_faces hs).1
    exact ⟨Sum.inr w, by simpa using hw⟩
  · rw [← FiniteConeCollapse.faceSimplex_eq_convexHull]
    refine ⟨?_, ?_, ?_⟩
    · intro v; cases v with
      | inl v => exact le_refl 0
      | inr w => exact hz.1 w
    · simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Finset.sum_const_zero, zero_add] using hz.2.1
    · intro v hv
      cases v with
      | inl v => rfl
      | inr w => exact hz.2.2 w (by simpa using hv)

private theorem nativeCone_base (Z : PreAbstractSimplicialComplex W)
    (a : V) (z : FiniteSimplicialJoin.Space Z)
    (x : FiniteSimplicialJoin.Space
      (FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z)) :
    x.val ∈ FiniteConeCollapse.realization
      (FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z) ↔
      coneHeight (nativeConeHomeomorph Z a z x) = 1 := by
  let e := FiniteSimplicialJoin.joinHomeomorph (vertexComplex a) Z
    ⟨FiniteVertexCylinder.vertexPoint _ a rfl⟩ ⟨z⟩
  obtain ⟨p, rfl⟩ := e.surjective x
  induction p using Quotient.inductionOn with
  | h p =>
    have hr : coneHeight (nativeConeHomeomorph Z a z (e (Quotient.mk _ p))) = p.2.2 := by
      change coneHeight ((joinHomeomorph (vertexSpaceHomeomorph a) (Homeomorph.refl _))
        (e.symm (e (Quotient.mk _ p)))) = _
      rw [e.symm_apply_apply]
      rfl
    rw [hr]
    change FiniteSimplicialJoin.representative (vertexComplex a) Z p ∈ _ ↔ _
    constructor
    · rintro ⟨s, hs, hx⟩
      rw [← FiniteConeCollapse.faceSimplex_eq_convexHull] at hx
      have hl : s.toLeft = ∅ := hs.2.1.resolve_right (fun h => h)
      have hn : Sum.inl a ∉ s := by
        simpa only [Finset.mem_toLeft] using
          (show a ∉ s.toLeft by rw [hl]; simp)
      have hcoord := hx.2.2 (Sum.inl a) hn
      have hpa : p.1.val a = 1 := by rw [vertexSpace_eq a p.1]; simp
      change (1 - (p.2.2 : ℝ)) * p.1.val a = 0 at hcoord
      apply Subtype.ext
      change (p.2.2 : ℝ) = 1
      rw [hpa] at hcoord
      linarith
    · intro ht
      have he : FiniteSimplicialJoin.representative (vertexComplex a) Z p =
          Sum.elim (fun _ : V => (0 : ℝ)) p.2.1.val := by
        ext v; cases v <;> simp [FiniteSimplicialJoin.representative, ht]
      rw [he]
      exact join_base_mem Z p.2.1

private def nativeConeBaseHomeomorph (Z : PreAbstractSimplicialComplex W)
    (a : V) (z : FiniteSimplicialJoin.Space Z) :
    FiniteConeUnionWedge.Collapse
      {x : FiniteSimplicialJoin.Space
        (FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z) |
        x.val ∈ FiniteConeCollapse.realization
          (FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z)} ≃ₜ
      FiniteSimplicialJoin.OrdinaryJoin (FiniteSimplicialJoin.Space Z) Bool :=
  (Homeomorph.Quotient.congr (nativeConeHomeomorph Z a z) (by
    intro x y
    change (x = y ∨ (_ ∧ _)) ↔ (_ = _ ∨ (_ ∧ _))
    simp only [Set.mem_setOf_eq]
    rw [(nativeConeHomeomorph Z a z).injective.eq_iff,
      nativeCone_base Z a z x, nativeCone_base Z a z y])).trans
    coneBaseSuspensionHomeomorph

private theorem realization_pullback_intersection
    (X Y D : PreAbstractSimplicialComplex (V ⊕ W)) (h : X ⊓ Y = D) :
    {x : FiniteSimplicialJoin.Space X | x.val ∈ FiniteConeCollapse.realization Y} =
      {x : FiniteSimplicialJoin.Space X | x.val ∈ FiniteConeCollapse.realization D} := by
  ext x
  rw [← h, FiniteConeUnionWedge.realization_intersection]
  exact ⟨fun hy => ⟨x.property, hy⟩, fun hxy => hxy.2⟩

/-- The auxiliary cone quotient is the other join with precisely its base collapsed. -/
private def auxiliaryConeQuotientHomeomorph
    (N : PreAbstractSimplicialComplex V) (Z : PreAbstractSimplicialComplex W)
    (d : V) (hNd : N ⊓ vertexComplex d = ⊥)
    (b : W) (hb : ({b} : Finset W) ∈ Z) :
    FiniteConeUnionWedge.Collapse
      {z : FiniteSimplicialJoin.Space
          (FiniteSimplicialJoin.simplicialJoin N Z ⊔
            FiniteSimplicialJoin.simplicialJoin (vertexComplex d) Z) |
        z.val ∈ FiniteConeCollapse.realization
          (FiniteSimplicialJoin.simplicialJoin (vertexComplex d) Z)} ≃ₜ
      FiniteConeUnionWedge.Collapse
        {y : FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin N Z) |
          y.val ∈ FiniteConeCollapse.realization
            (FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z)} := by
  refine (unionCollapseRightHomeomorph _ _ (Sum.inr b)
    (join_right_vertex N Z b hb)
    (join_right_vertex (vertexComplex d) Z b hb)).trans ?_
  apply Homeomorph.Quotient.congrRight
  have h := realization_pullback_intersection _ _ _ (disjoint_join_overlap N _ Z hNd)
  intro x y
  rw [h]

/-- The auxiliary space is collapsed along either of two actual cones.
The remaining cone modulo its base is identified by its actual suspension homeomorphism. -/
private def auxiliaryBaseSplit (N : PreAbstractSimplicialComplex V)
    (Z : PreAbstractSimplicialComplex W)
    (d : V) (hNd : N ⊓ vertexComplex d = ⊥)
    (v : V) (hv : ({v} : Finset V) ∈ N)
    (b : W) (hb : ({b} : Finset W) ∈ Z) :
    Σ y : FiniteSimplicialJoin.OrdinaryJoin (FiniteSimplicialJoin.Space Z) Bool,
      FiniteConeUnionWedge.Collapse
        {x : FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin N Z) |
          x.val ∈ FiniteConeCollapse.realization
            (FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z)} ≃ₕ
        FiniteConeUnionWedge.Wedge
          (Quotient.mk (FiniteConeUnionWedge.subsetSetoid
            {x : FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin N Z) |
              x.val ∈ FiniteConeCollapse.realization
                (FiniteSimplicialJoin.simplicialJoin (vertexComplex v) Z)})
            (FiniteVertexCylinder.vertexPoint _ _ (join_left_vertex N Z v hv))) y := by
  let X := FiniteSimplicialJoin.simplicialJoin N Z
  let D := FiniteSimplicialJoin.simplicialJoin (vertexComplex d) Z
  let C := FiniteSimplicialJoin.simplicialJoin (vertexComplex v) Z
  let B := FiniteSimplicialJoin.simplicialJoin (⊥ : PreAbstractSimplicialComplex V) Z
  have hCX : C ≤ X := join_mono_left (vertexComplex_le N v hv) Z
  have hXD : X ⊓ D ≤ C := by
    rw [disjoint_join_overlap N (vertexComplex d) Z hNd]
    exact join_mono_left bot_le Z
  have hdv : vertexComplex d ⊓ vertexComplex v = ⊥ := by
    apply le_antisymm _ bot_le
    intro s hs
    have h : s ∈ N ⊓ vertexComplex d :=
      ⟨vertexComplex_le N v hv hs.2, hs.1⟩
    exact hNd ▸ h
  have hDC : D ⊓ C = B := disjoint_join_overlap _ _ Z hdv
  let Q : FiniteConeCollapse.ConePair (V ⊕ W) :=
    ⟨X ⊔ D, D, le_sup_right, Sum.inl d,
      join_left_vertex (vertexComplex d) Z d rfl, join_vertex_cone Z d⟩
  let A := auxiliaryConeQuotientHomeomorph N Z d hNd b hb
  let E : FiniteConeUnionWedge.Collapse
      {x : FiniteSimplicialJoin.Space D | x.val ∈ FiniteConeCollapse.realization C} ≃ₜ
      FiniteSimplicialJoin.OrdinaryJoin (FiniteSimplicialJoin.Space Z) Bool :=
    (Homeomorph.Quotient.congrRight (by
      intro x y
      have h := realization_pullback_intersection D C B hDC
      change (x = y ∨ (_ ∧ _)) ↔ (x = y ∨ (_ ∧ _))
      rw [h])).trans
      (nativeConeBaseHomeomorph Z d (FiniteVertexCylinder.vertexPoint Z b hb))
  let xa := FiniteVertexCylinder.vertexPoint X (Sum.inl v) (join_left_vertex N Z v hv)
  let yb := FiniteVertexCylinder.vertexPoint D (Sum.inr b)
    (join_right_vertex (vertexComplex d) Z b hb)
  let e := coneCoverEquiv X D C (Sum.inl v) (Sum.inr b)
    (join_left_vertex N Z v hv) (join_right_vertex (vertexComplex d) Z b hb)
    (join_left_vertex (vertexComplex v) Z v rfl)
    (join_right_vertex (vertexComplex v) Z b hb)
    (hCX.trans le_sup_left) hXD (join_vertex_cone Z v)
  refine ⟨E (Quotient.mk _ yb), ?_⟩
  exact (A.symm.toHomotopyEquiv.trans Q.collapseEquiv.symm).trans
    (e.trans (wedgeHomeomorph (Quotient.mk _ xa) (Quotient.mk _ yb)
      (Homeomorph.refl _) E).toHomotopyEquiv)

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

private theorem join_intersection (M N : PreAbstractSimplicialComplex V)
    (Z : PreAbstractSimplicialComplex W) :
    FiniteSimplicialJoin.simplicialJoin M Z ⊓ FiniteSimplicialJoin.simplicialJoin N Z =
      FiniteSimplicialJoin.simplicialJoin (M ⊓ N) Z := by
  apply SetLike.ext
  intro s
  change ((s.Nonempty ∧ (s.toLeft = ∅ ∨ s.toLeft ∈ M) ∧
    (s.toRight = ∅ ∨ s.toRight ∈ Z)) ∧
    (s.Nonempty ∧ (s.toLeft = ∅ ∨ s.toLeft ∈ N) ∧
    (s.toRight = ∅ ∨ s.toRight ∈ Z))) ↔
    (s.Nonempty ∧ (s.toLeft = ∅ ∨ (s.toLeft ∈ M ∧ s.toLeft ∈ N)) ∧
    (s.toRight = ∅ ∨ s.toRight ∈ Z))
  tauto

/-- Distribution over two finite pieces uses their common actual cone in the join. -/
private def vertexUnionJoinEquiv (M N : PreAbstractSimplicialComplex V)
    (Z : PreAbstractSimplicialComplex W) (a : V)
    (hMN : M ⊓ N = vertexComplex a) :
    let haM := (show ({a} : Finset V) ∈ M from
      (show ({a} : Finset V) ∈ M ⊓ N from by rw [hMN]; rfl).1)
    let haN := (show ({a} : Finset V) ∈ N from
      (show ({a} : Finset V) ∈ M ⊓ N from by rw [hMN]; rfl).2)
    FiniteSimplicialJoin.Space (FiniteSimplicialJoin.simplicialJoin (M ⊔ N) Z) ≃ₕ
      FiniteConeUnionWedge.Wedge
        (FiniteVertexCylinder.vertexPoint _ _ (join_left_vertex M Z a haM))
        (FiniteVertexCylinder.vertexPoint _ _ (join_left_vertex N Z a haN)) := by
  rw [join_union]
  let P : FiniteConeUnionWedge.ConeUnion (V ⊕ W) :=
    { left := FiniteSimplicialJoin.simplicialJoin M Z
      right := FiniteSimplicialJoin.simplicialJoin N Z
      cone := FiniteSimplicialJoin.simplicialJoin (vertexComplex a) Z
      intersection := by rw [join_intersection, hMN]
      apex := Sum.inl a
      apex_face := join_left_vertex (vertexComplex a) Z a rfl
      cone_face := join_vertex_cone Z a }
  exact P.homotopyEquiv

end DisjointJoin

section BouquetConcatenation

private def collapseSumHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (C : Set X) (D : Set Y) (a : X) (b : Y) (ha : a ∈ C) (hb : b ∈ D) :
    FiniteConeUnionWedge.Wedge
      (Quotient.mk (FiniteConeUnionWedge.subsetSetoid C) a)
      (Quotient.mk (FiniteConeUnionWedge.subsetSetoid D) b) ≃ₜ
      FiniteConeUnionWedge.Collapse {z : X ⊕ Y | Sum.elim (· ∈ C) (· ∈ D) z} := by
  let P : FiniteConeUnionWedge.CollapseCover a b
      {z : X ⊕ Y | Sum.elim (· ∈ C) (· ∈ D) z} := {
    left := ⟨Sum.inl, continuous_inl⟩
    right := ⟨Sum.inr, continuous_inr⟩
    left_injective := Sum.inl_injective
    right_injective := Sum.inr_injective
    left_closed := isClosedMap_inl
    right_closed := isClosedMap_inr
    covers := by rintro (x | y); exact ⟨Sum.inl x, rfl⟩; exact ⟨Sum.inr y, rfl⟩
    overlap := by intro x y h; cases h
    left_base := ha
    right_base := hb }
  exact P.quotientWedgeHomeomorph

private def anchorCollapseHomeomorph {A Z : Type*} [TopologicalSpace A] [TopologicalSpace Z]
    (a : A) (B : Set Z) :
    FiniteConeUnionWedge.Collapse {z : A ⊕ Z | Sum.elim (fun _ => True) (· ∈ B) z} ≃ₜ
      FiniteConeUnionWedge.Collapse
        {z : PUnit.{1} ⊕ Z | Sum.elim (fun _ => True) (· ∈ B) z} := by
  let f : A ⊕ Z → PUnit.{1} ⊕ Z := Sum.map (fun _ => PUnit.unit) id
  let g : PUnit.{1} ⊕ Z → A ⊕ Z := Sum.map (fun _ => a) id
  have hf : ∀ z w, (FiniteConeUnionWedge.subsetSetoid
        {z : A ⊕ Z | Sum.elim (fun _ => True) (· ∈ B) z}).r z w →
      (FiniteConeUnionWedge.subsetSetoid
        {z : PUnit.{1} ⊕ Z | Sum.elim (fun _ => True) (· ∈ B) z}).r (f z) (f w) := by
    rintro z w (rfl | ⟨hz, hw⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨by cases z <;> exact hz, by cases w <;> exact hw⟩
  have hg : ∀ z w, (FiniteConeUnionWedge.subsetSetoid
        {z : PUnit.{1} ⊕ Z | Sum.elim (fun _ => True) (· ∈ B) z}).r z w →
      (FiniteConeUnionWedge.subsetSetoid
        {z : A ⊕ Z | Sum.elim (fun _ => True) (· ∈ B) z}).r (g z) (g w) := by
    rintro z w (rfl | ⟨hz, hw⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨by cases z <;> exact hz, by cases w <;> exact hw⟩
  exact {
    toFun := Quotient.map' f hf
    invFun := Quotient.map' g hg
    left_inv := by
      intro z; induction z using Quotient.inductionOn with
      | h z =>
        apply Quotient.sound
        cases z
        · exact Or.inr ⟨True.intro, True.intro⟩
        · exact Or.inl rfl
    right_inv := by
      intro z; induction z using Quotient.inductionOn with
      | h z =>
        apply Quotient.sound
        cases z with
        | inl x => exact Or.inl (congrArg Sum.inl (Subsingleton.elim _ _))
        | inr x => exact Or.inl rfl
    continuous_toFun := (continuous_const.sumMap continuous_id).quotient_map' hf
    continuous_invFun := (continuous_const.sumMap continuous_id).quotient_map' hg }

private def sphereCast {d e : ℕ} (h : d = e) :
    FiniteSimplicialJoin.Space (sphereComplex d) ≃ₜ
      FiniteSimplicialJoin.Space (sphereComplex e) := by
  subst e
  exact Homeomorph.refl _

private theorem sphereCast_point {d e : ℕ} (h : d = e) :
    sphereCast h (spherePoint d) = spherePoint e := by
  subst e
  rfl

private abbrev SphereFamily (ds : BouquetSpec) :=
  Σ i : Fin ds.length, FiniteSimplicialJoin.Space (sphereComplex (ds.get i).val)

private def appendIndex (ds es : BouquetSpec) :
    Fin ds.length ⊕ Fin es.length ≃ Fin (ds ++ es).length :=
  finSumFinEquiv.trans (finCongr (by simp))

private def appendDimension (ds es : BouquetSpec) : Fin ds.length ⊕ Fin es.length → ℕ :=
  Sum.elim (fun i => (ds.get i).val) (fun i => (es.get i).val)

private theorem appendDimension_eq (ds es : BouquetSpec) (i : Fin ds.length ⊕ Fin es.length) :
    appendDimension ds es i = ((ds ++ es).get (appendIndex ds es i)).val := by
  cases i with
  | inl i =>
    change ds[i.val].val = (ds ++ es)[i.val].val
    rw [List.getElem_append_left i.isLt]
  | inr i =>
    change es[i.val].val = (ds ++ es)[ds.length + i.val].val
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simp

private def appendFamilyEquiv (ds es : BouquetSpec) :
    SphereFamily ds ⊕ SphereFamily es ≃ SphereFamily (ds ++ es) :=
  (Equiv.sumSigmaDistrib (fun i =>
    FiniteSimplicialJoin.Space (sphereComplex (appendDimension ds es i)))).symm.trans
    (Equiv.sigmaCongr (appendIndex ds es) (fun i =>
      (sphereCast (appendDimension_eq ds es i)).toEquiv))

private def appendFamilyHomeomorph (ds es : BouquetSpec) :
    SphereFamily ds ⊕ SphereFamily es ≃ₜ SphereFamily (ds ++ es) := by
  letI (i : Fin ds.length) : CompactSpace
      (FiniteSimplicialJoin.Space (sphereComplex (ds.get i).val)) :=
    FiniteSimplicialJoin.realizationCompactSpace _
  letI (i : Fin es.length) : CompactSpace
      (FiniteSimplicialJoin.Space (sphereComplex (es.get i).val)) :=
    FiniteSimplicialJoin.realizationCompactSpace _
  apply Continuous.homeoOfEquivCompactToT2 (f := appendFamilyEquiv ds es)
  have hl : Continuous (fun z : SphereFamily ds => appendFamilyEquiv ds es (Sum.inl z)) := by
    apply continuous_sigma
    intro i
    exact (@continuous_sigmaMk _ (fun k : Fin (ds ++ es).length =>
      FiniteSimplicialJoin.Space (sphereComplex ((ds ++ es).get k).val)) _
        (appendIndex ds es (Sum.inl i))).comp
      (sphereCast (appendDimension_eq ds es (Sum.inl i))).continuous
  have hr : Continuous (fun z : SphereFamily es => appendFamilyEquiv ds es (Sum.inr z)) := by
    apply continuous_sigma
    intro i
    exact (@continuous_sigmaMk _ (fun k : Fin (ds ++ es).length =>
      FiniteSimplicialJoin.Space (sphereComplex ((ds ++ es).get k).val)) _
        (appendIndex ds es (Sum.inr i))).comp
      (sphereCast (appendDimension_eq ds es (Sum.inr i))).continuous
  convert Continuous.sumElim hl hr using 1
  funext z
  cases z <;> rfl

private theorem appendFamily_base (ds es : BouquetSpec) (z : SphereFamily ds ⊕ SphereFamily es) :
    (appendFamilyHomeomorph ds es z).2 =
      spherePoint ((ds ++ es).get (appendFamilyHomeomorph ds es z).1).val ↔
    Sum.elim (fun x : SphereFamily ds => x.2 = spherePoint (ds.get x.1).val)
      (fun x : SphereFamily es => x.2 = spherePoint (es.get x.1).val) z := by
  have hc {d e : ℕ} (h : d = e) (x : FiniteSimplicialJoin.Space (sphereComplex d)) :
      sphereCast h x = spherePoint e ↔ x = spherePoint d := by
    subst e
    rfl
  rcases z with ⟨i, x⟩ | ⟨i, x⟩
  · convert hc (appendDimension_eq ds es (Sum.inl i)) x using 1 <;> rfl
  · convert hc (appendDimension_eq ds es (Sum.inr i)) x using 1 <;> rfl

private def bouquetSourceShuffle (ds es : BouquetSpec) :
    BouquetSource ds ⊕ BouquetSource es ≃ₜ
      (PUnit.{1} ⊕ PUnit.{1}) ⊕ SphereFamily (ds ++ es) :=
  (Homeomorph.sumSumSumComm PUnit.{1} (SphereFamily ds) PUnit.{1} (SphereFamily es)).trans
    ((Homeomorph.refl _).sumCongr (appendFamilyHomeomorph ds es))

private def bouquetAppendHomeomorph (ds es : BouquetSpec) :
    FiniteConeUnionWedge.Wedge (bouquetPoint ds) (bouquetPoint es) ≃ₜ
      FiniteSimplicialJoin.Space (bouquetComplex (ds ++ es)) := by
  let qd : CoordinateBouquetQuotient ds := Quotient.mk _ (Sum.inl PUnit.unit)
  let qe : CoordinateBouquetQuotient es := Quotient.mk _ (Sum.inl PUnit.unit)
  let hd := bouquetQuotientHomeomorph ds
  let he := bouquetQuotientHomeomorph es
  let first : FiniteConeUnionWedge.Wedge (bouquetPoint ds) (bouquetPoint es) ≃ₜ
      FiniteConeUnionWedge.Wedge qd qe :=
    (wedgeHomeomorph qd qe hd he).symm
  let h := bouquetSourceShuffle ds es
  let B : Set (SphereFamily (ds ++ es)) :=
    {z | z.2 = spherePoint ((ds ++ es).get z.1).val}
  let middle : FiniteConeUnionWedge.Collapse
      {z : BouquetSource ds ⊕ BouquetSource es |
        Sum.elim (· ∈ bouquetBases ds) (· ∈ bouquetBases es) z} ≃ₜ
      FiniteConeUnionWedge.Collapse
        {z : (PUnit.{1} ⊕ PUnit.{1}) ⊕ SphereFamily (ds ++ es) |
          Sum.elim (fun _ => True) (· ∈ B) z} := by
    apply Homeomorph.Quotient.congr h
    intro z w
    have hb (z : BouquetSource ds ⊕ BouquetSource es) :
        Sum.elim (fun _ => True) (· ∈ B) (h z) ↔
        Sum.elim (· ∈ bouquetBases ds) (· ∈ bouquetBases es) z := by
      rcases z with (u | x) | (v | y)
      · rfl
      · exact appendFamily_base ds es (Sum.inl x)
      · rfl
      · exact appendFamily_base ds es (Sum.inr y)
    change (z = w ∨ (_ ∧ _)) ↔ (h z = h w ∨ (_ ∧ _))
    simp only [Set.mem_setOf_eq]
    rw [h.injective.eq_iff, hb, hb]
  exact first.trans
    ((collapseSumHomeomorph (bouquetBases ds) (bouquetBases es)
      (Sum.inl PUnit.unit) (Sum.inl PUnit.unit) True.intro True.intro).trans
      (middle.trans ((anchorCollapseHomeomorph (Sum.inl PUnit.unit) B).trans
        (bouquetQuotientHomeomorph (ds ++ es)))))

/- The connected selected-component carrier is now consumed by the actual
  vertex-gluing quotient and the actual bouquet concatenation quotient. -/
private def connectedVertexGluingHomeomorph (ds es : BouquetSpec) :
    FiniteSimplicialJoin.Space
        (selectedVertexGluing (bouquetComplex ds) (bouquetComplex es) none none) ≃ₜ
      FiniteSimplicialJoin.Space (bouquetComplex (ds ++ es)) := by
  exact (vertexGluingHomeomorph (bouquetComplex ds) (bouquetComplex es)
      none none (bouquetVertex_face ds) (bouquetVertex_face es)).symm.trans
    (bouquetAppendHomeomorph ds es)

/- The first consumed selected-component step.  The two native based packets
  choose the actual normal-form components containing the supplied vertices;
  basedWedgeEquivalence then performs the quotient wedge replacement on the
  live carrier.  The normal spaces remain finite coproduct realizations, so
  every unselected component (including point components) stays present. -/
private def selectedComponentWedgeBased {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (hK : WPlus K) (hL : WPlus L)
    (a : V) (ha : ({a} : Finset V) ∈ K)
    (b : W) (hb : ({b} : Finset W) ∈ L) :
    ∃ m : ℕ, ∃ hm : 0 < m, ∃ p : Fin m → BouquetSpec, ∃ i : Fin m,
      ∃ n : ℕ, ∃ hn : 0 < n, ∃ q : Fin n → BouquetSpec, ∃ j : Fin n,
      Nonempty (SingletonRetractionBasedInverse.BasedEquivalence
        (Quotient.mk (FiniteConeUnionWedge.subsetSetoid (FiniteConeUnionWedge.wedgePoints
          (FiniteVertexCylinder.vertexPoint K a ha)
          (FiniteVertexCylinder.vertexPoint L b hb)))
          (Sum.inl (FiniteVertexCylinder.vertexPoint K a ha)))
        (Quotient.mk (FiniteConeUnionWedge.subsetSetoid (FiniteConeUnionWedge.wedgePoints
          (normalPoint m p i) (normalPoint n q j))) (Sum.inl (normalPoint m p i)))) := by
  obtain ⟨m, hm, p, i, ⟨E⟩⟩ := based_normalization K hK a ha
  obtain ⟨n, hn, q, j, ⟨F⟩⟩ := based_normalization L hL b hb
  exact ⟨m, hm, p, i, n, hn, q, j,
    ⟨FiniteConeUnionWedge.basedWedgeEquivalence E F⟩⟩

private def selectedComponentWedgeCarrier {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (hK : WPlus K) (hL : WPlus L)
    (a : V) (ha : ({a} : Finset V) ∈ K)
    (b : W) (hb : ({b} : Finset W) ∈ L) :
    ∃ m : ℕ, ∃ hm : 0 < m, ∃ p : Fin m → BouquetSpec, ∃ i : Fin m,
      ∃ n : ℕ, ∃ hn : 0 < n, ∃ q : Fin n → BouquetSpec, ∃ j : Fin n,
      Nonempty (SingletonRetractionBasedInverse.BasedEquivalence
        (Quotient.mk (FiniteConeUnionWedge.subsetSetoid (FiniteConeUnionWedge.wedgePoints
          (FiniteVertexCylinder.vertexPoint K a ha)
          (FiniteVertexCylinder.vertexPoint L b hb)))
          (Sum.inl (FiniteVertexCylinder.vertexPoint K a ha)))
        (Quotient.mk (FiniteConeUnionWedge.subsetSetoid (FiniteConeUnionWedge.wedgePoints
          (normalPoint m p i) (normalPoint n q j))) (Sum.inl (normalPoint m p i)))) ∧
      Nonempty (FiniteConeUnionWedge.Wedge
          (normalPoint m p i) (normalPoint n q j) ≃ₜ
        FiniteSimplicialJoin.Space
          (selectedVertexGluing (normalComplex m p) (normalComplex n q)
            ⟨i, none⟩ ⟨j, none⟩)) := by
  obtain ⟨m, hm, p, i, n, hn, q, j, hE⟩ :=
    selectedComponentWedgeBased K L hK hL a ha b hb
  have hi : ({⟨i, none⟩} : Finset (NormalVertices m p)) ∈ normalComplex m p :=
    normalVertex_face m p i
  have hj : ({⟨j, none⟩} : Finset (NormalVertices n q)) ∈ normalComplex n q :=
    normalVertex_face n q j
  refine ⟨m, hm, p, i, n, hn, q, j, hE, ?_⟩
  exact ⟨by
    convert vertexGluingHomeomorph (normalComplex m p) (normalComplex n q)
      ⟨i, none⟩ ⟨j, none⟩ hi hj using 1 <;> rfl⟩

private def sigmaSplitHomeomorph {A : Type*} [DecidableEq A]
    (X : A → Type*) [∀ i, TopologicalSpace (X i)] (a : A) :
    (Σ i, X i) ≃ₜ X a ⊕ (Σ i : {i : A // i ≠ a}, X i.val) where
  toFun z := if h : z.1 = a then Sum.inl (h ▸ z.2) else Sum.inr ⟨⟨z.1, h⟩, z.2⟩
  invFun := Sum.elim (Sigma.mk a) (fun z => ⟨z.1.val, z.2⟩)
  left_inv := by
    rintro ⟨i, x⟩
    by_cases h : i = a
    · subst i; simp
    · simp [h]
  right_inv := by
    rintro (x | ⟨⟨i, hi⟩, x⟩)
    · simp
    · simp [hi]
  continuous_toFun := by
    apply continuous_sigma
    intro i
    by_cases h : i = a
    · subst i; simpa using (continuous_inl : Continuous (Sum.inl : X a → _))
    · have hc : Continuous (fun x : X i =>
          (⟨⟨i, h⟩, x⟩ : Σ k : {i : A // i ≠ a}, X k.val)) :=
          @continuous_sigmaMk {i : A // i ≠ a} (fun k => X k.val) _ ⟨i, h⟩
      simp only [dif_neg h]
      exact continuous_inr.comp hc
  continuous_invFun := continuous_sigmaMk.sumElim (continuous_sigma fun _ => continuous_sigmaMk)

private def collapseLeftHomeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (C : Set X) :
    FiniteConeUnionWedge.Collapse
      {z : X ⊕ Y | Sum.elim (· ∈ C) (fun _ => False) z} ≃ₜ
      FiniteConeUnionWedge.Collapse C ⊕ Y := by
  let f : X ⊕ Y → FiniteConeUnionWedge.Collapse C ⊕ Y := Sum.map (Quotient.mk _) id
  have hf : ∀ z w, (FiniteConeUnionWedge.subsetSetoid
      {z : X ⊕ Y | Sum.elim (· ∈ C) (fun _ => False) z}).r z w → f z = f w := by
    rintro z w (rfl | ⟨hz, hw⟩)
    · rfl
    · rcases z with x | y <;> rcases w with x' | y'
      · exact congrArg Sum.inl (Quotient.sound (Or.inr ⟨hz, hw⟩))
      · exact hw.elim
      · exact hz.elim
      · exact hz.elim
  let g : C(FiniteConeUnionWedge.Collapse C,
      FiniteConeUnionWedge.Collapse
        {z : X ⊕ Y | Sum.elim (· ∈ C) (fun _ => False) z}) :=
    ⟨Quotient.lift (fun x => Quotient.mk _ (Sum.inl x)) (by
      rintro x y (rfl | ⟨hx, hy⟩)
      · rfl
      · exact Quotient.sound (Or.inr ⟨hx, hy⟩)),
      (continuous_quotient_mk'.comp continuous_inl).quotient_lift _⟩
  exact {
    toFun := Quotient.lift f hf
    invFun := Sum.elim g (fun y => Quotient.mk _ (Sum.inr y))
    left_inv := by
      intro z
      induction z using Quotient.inductionOn with
      | h z => cases z <;> rfl
    right_inv := by
      rintro (x | y)
      · induction x using Quotient.inductionOn with | h x => rfl
      · rfl
    continuous_toFun := (continuous_quotient_mk'.sumMap continuous_id).quotient_lift _
    continuous_invFun := g.continuous.sumElim (continuous_quotient_mk'.comp continuous_inr) }

private def wedgeExtrasHomeomorph {X Y U V : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace U] [TopologicalSpace V]
    (a : X) (b : Y) :
    FiniteConeUnionWedge.Wedge (Sum.inl a : X ⊕ U) (Sum.inl b : Y ⊕ V) ≃ₜ
      FiniteConeUnionWedge.Wedge a b ⊕ (U ⊕ V) := by
  let h := Homeomorph.sumSumSumComm X U Y V
  refine (Homeomorph.Quotient.congr h ?_).trans
    (collapseLeftHomeomorph (Y := U ⊕ V) (FiniteConeUnionWedge.wedgePoints a b))
  intro z w
  have hb (z : (X ⊕ U) ⊕ (Y ⊕ V)) :
      Sum.elim (· ∈ FiniteConeUnionWedge.wedgePoints a b) (fun _ => False) (h z) ↔
        z ∈ FiniteConeUnionWedge.wedgePoints (Sum.inl a) (Sum.inl b) := by
    rcases z with (x | u) | (y | v) <;>
      simp [h, Homeomorph.sumSumSumComm, FiniteConeUnionWedge.wedgePoints]
  change (z = w ∨ (_ ∧ _)) ↔ (h z = h w ∨ (_ ∧ _))
  simp only [Set.mem_setOf_eq]
  rw [h.injective.eq_iff, hb, hb]

private abbrev MergedIndex {m n : ℕ} (i : Fin m) (j : Fin n) :=
  Unit ⊕ ({k : Fin m // k ≠ i} ⊕ {l : Fin n // l ≠ j})

private def mergedSpec {m n : ℕ} (p : Fin m → BouquetSpec) (q : Fin n → BouquetSpec)
    (i : Fin m) (j : Fin n) : MergedIndex i j → BouquetSpec :=
  Sum.elim (fun _ => p i ++ q j) (Sum.elim (fun k => p k.val) (fun l => q l.val))

private theorem mergedIndex_card {m n : ℕ} (i : Fin m) (j : Fin n) :
    Fintype.card (MergedIndex i j) = m + n - 1 := by
  have hm := i.isLt
  have hn := j.isLt
  have hmi : Fintype.card {k : Fin m // k ≠ i} = m - 1 := by
    simpa using Fintype.card_subtype_compl (fun k : Fin m => k = i)
  have hnj : Fintype.card {l : Fin n // l ≠ j} = n - 1 := by
    simpa using Fintype.card_subtype_compl (fun l : Fin n => l = j)
  simp only [MergedIndex, Fintype.card_sum, Fintype.card_unit, hmi, hnj]
  omega

private def mergedEnumeration {m n : ℕ} (i : Fin m) (j : Fin n) :
    MergedIndex i j ≃ Fin (m + n - 1) :=
  (Fintype.equivFin _).trans (finCongr (mergedIndex_card i j))

/-- Selected bouquets concatenate; every other component retains its full sphere list. -/
def selectedWedgeSpec {m n : ℕ} (p : Fin m → BouquetSpec) (q : Fin n → BouquetSpec)
    (i : Fin m) (j : Fin n) : Fin (m + n - 1) → BouquetSpec :=
  fun k => mergedSpec p q i j ((mergedEnumeration i j).symm k)

private def mergedSumHomeomorph {m n : ℕ} (p : Fin m → BouquetSpec) (q : Fin n → BouquetSpec)
    (i : Fin m) (j : Fin n) :
    (FiniteSimplicialJoin.Space (bouquetComplex (p i ++ q j)) ⊕
      ((Σ k : {k : Fin m // k ≠ i}, FiniteSimplicialJoin.Space (bouquetComplex (p k.val))) ⊕
       (Σ l : {l : Fin n // l ≠ j}, FiniteSimplicialJoin.Space (bouquetComplex (q l.val))))) ≃ₜ
    (Σ k : MergedIndex i j, FiniteSimplicialJoin.Space (bouquetComplex (mergedSpec p q i j k))) where
  toFun := Sum.elim (fun x => ⟨Sum.inl (), x⟩)
    (Sum.elim (fun x => ⟨Sum.inr (Sum.inl x.1), x.2⟩)
      (fun y => ⟨Sum.inr (Sum.inr y.1), y.2⟩))
  invFun z := match z with
    | ⟨Sum.inl _, x⟩ => Sum.inl x
    | ⟨Sum.inr (Sum.inl k), x⟩ => Sum.inr (Sum.inl ⟨k, x⟩)
    | ⟨Sum.inr (Sum.inr l), x⟩ => Sum.inr (Sum.inr ⟨l, x⟩)
  left_inv := by rintro (x | (⟨k, x⟩ | ⟨l, x⟩)) <;> rfl
  right_inv := by rintro ⟨(_ | (k | l)), x⟩ <;> rfl
  continuous_toFun := by
    apply Continuous.sumElim
    · exact @continuous_sigmaMk (MergedIndex i j) (fun k =>
        FiniteSimplicialJoin.Space (bouquetComplex (mergedSpec p q i j k))) _ (Sum.inl ())
    · apply Continuous.sumElim
      · apply continuous_sigma
        intro k
        exact @continuous_sigmaMk (MergedIndex i j) (fun k =>
          FiniteSimplicialJoin.Space (bouquetComplex (mergedSpec p q i j k))) _
            (Sum.inr (Sum.inl k))
      · apply continuous_sigma
        intro l
        exact @continuous_sigmaMk (MergedIndex i j) (fun k =>
          FiniteSimplicialJoin.Space (bouquetComplex (mergedSpec p q i j k))) _
            (Sum.inr (Sum.inr l))
  continuous_invFun := by
    apply continuous_sigma
    rintro (_ | (k | l))
    · exact continuous_inl
    · exact continuous_inr.comp (continuous_inl.comp continuous_sigmaMk)
    · exact continuous_inr.comp (continuous_inr.comp continuous_sigmaMk)

private def bouquetListCast {ds es : BouquetSpec} (h : ds = es) :
    FiniteSimplicialJoin.Space (bouquetComplex ds) ≃ₜ
      FiniteSimplicialJoin.Space (bouquetComplex es) := by
  subst es
  exact Homeomorph.refl _

private def mergedReindexHomeomorph {m n : ℕ}
    (p : Fin m → BouquetSpec) (q : Fin n → BouquetSpec) (i : Fin m) (j : Fin n) :
    (Σ k : MergedIndex i j, FiniteSimplicialJoin.Space (bouquetComplex (mergedSpec p q i j k))) ≃ₜ
      (Σ k : Fin (m + n - 1), FiniteSimplicialJoin.Space
        (bouquetComplex (selectedWedgeSpec p q i j k))) := by
  let e := mergedEnumeration i j
  let h (k : MergedIndex i j) := bouquetListCast
    (congrArg (mergedSpec p q i j) (e.symm_apply_apply k).symm)
  letI (k : MergedIndex i j) : CompactSpace
      (FiniteSimplicialJoin.Space (bouquetComplex (mergedSpec p q i j k))) :=
    FiniteSimplicialJoin.realizationCompactSpace _
  apply Continuous.homeoOfEquivCompactToT2
    (f := Equiv.sigmaCongr e (fun k => (h k).toEquiv))
  apply continuous_sigma
  intro k
  exact (@continuous_sigmaMk _ (fun l : Fin (m + n - 1) =>
    FiniteSimplicialJoin.Space (bouquetComplex (selectedWedgeSpec p q i j l))) _ (e k)).comp
      (h k).continuous

private def normalWedgeHomeomorph {m n : ℕ}
    (p : Fin m → BouquetSpec) (q : Fin n → BouquetSpec) (i : Fin m) (j : Fin n) :
    FiniteConeUnionWedge.Wedge (normalPoint m p i) (normalPoint n q j) ≃ₜ
      FiniteSimplicialJoin.Space (normalComplex (m + n - 1) (selectedWedgeSpec p q i j)) := by
  let hp := (normalHomeomorph m p).trans
    (sigmaSplitHomeomorph (fun k => FiniteSimplicialJoin.Space (bouquetComplex (p k))) i)
  let hq := (normalHomeomorph n q).trans
    (sigmaSplitHomeomorph (fun l => FiniteSimplicialJoin.Space (bouquetComplex (q l))) j)
  have hpi : hp (normalPoint m p i) = Sum.inl (bouquetPoint (p i)) := by
    rw [← normalPoint_embedding m p i]
    simp [hp, sigmaSplitHomeomorph]
  have hqj : hq (normalPoint n q j) = Sum.inl (bouquetPoint (q j)) := by
    rw [← normalPoint_embedding n q j]
    simp [hq, sigmaSplitHomeomorph]
  let first := wedgeHomeomorph (normalPoint m p i) (normalPoint n q j) hp hq
  rw [hpi, hqj] at first
  exact first.trans ((wedgeExtrasHomeomorph (bouquetPoint (p i)) (bouquetPoint (q j))).trans
    (((bouquetAppendHomeomorph (p i) (q j)).sumCongr (Homeomorph.refl _)).trans
      ((mergedSumHomeomorph p q i j).trans ((mergedReindexHomeomorph p q i j).trans
        (normalHomeomorph (m + n - 1) (selectedWedgeSpec p q i j)).symm))))

/-- The finite vertex set formed by identifying exactly the two selected vertices. -/
abbrev VertexWedgeVertices {V W : Type*} (a : V) (b : W) :=
  FiniteConeUnionWedge.Wedge a b

instance vertexWedgeVerticesFintype {V W : Type*} [Fintype V] [Fintype W] (a : V) (b : W) :
    Fintype (VertexWedgeVertices a b) := Fintype.ofFinite _

instance vertexWedgeVerticesDecidableEq {V W : Type*} (a : V) (b : W) :
    DecidableEq (VertexWedgeVertices a b) := Classical.decEq _

/-- The actual simplicial vertex wedge, rather than a homotopy-type surrogate. -/
def vertexWedgeComplex {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W) (a : V) (b : W) :
    PreAbstractSimplicialComplex (VertexWedgeVertices a b) := vertexGluing K L a b

private theorem vertexWedge_vertex {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (a : V) (b : W) (ha : ({a} : Finset V) ∈ K) :
    ({Quotient.mk _ (Sum.inl a)} : Finset (VertexWedgeVertices a b)) ∈
      vertexWedgeComplex K L a b := by
  apply Or.inl
  refine ⟨{a}, ha, ?_⟩
  change Finset.image (glueLeft a b) {a} = _
  rw [Finset.image_singleton]
  rfl

/-- The common actual vertex in the native finite wedge realization. -/
def vertexWedgePoint {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (a : V) (b : W) (ha : ({a} : Finset V) ∈ K) :
    FiniteSimplicialJoin.Space (vertexWedgeComplex K L a b) :=
  FiniteVertexCylinder.vertexPoint _ _ (vertexWedge_vertex K L a b ha)

/-- Complete selected-component closure data, including both relative inverse homotopies. -/
structure SelectedVertexWedgeClosure {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (a : V) (ha : ({a} : Finset V) ∈ K) (b : W) (hb : ({b} : Finset W) ∈ L) where
  leftCount : ℕ
  leftPositive : 0 < leftCount
  leftSpec : Fin leftCount → BouquetSpec
  leftSelected : Fin leftCount
  rightCount : ℕ
  rightPositive : 0 < rightCount
  rightSpec : Fin rightCount → BouquetSpec
  rightSelected : Fin rightCount
  leftNormalization : SingletonRetractionBasedInverse.BasedEquivalence
    (FiniteVertexCylinder.vertexPoint K a ha) (normalPoint leftCount leftSpec leftSelected)
  rightNormalization : SingletonRetractionBasedInverse.BasedEquivalence
    (FiniteVertexCylinder.vertexPoint L b hb) (normalPoint rightCount rightSpec rightSelected)
  normalization : SingletonRetractionBasedInverse.BasedEquivalence
    (Quotient.mk (FiniteConeUnionWedge.subsetSetoid (FiniteConeUnionWedge.wedgePoints
      (FiniteVertexCylinder.vertexPoint K a ha) (FiniteVertexCylinder.vertexPoint L b hb)))
      (Sum.inl (FiniteVertexCylinder.vertexPoint K a ha)))
    (Quotient.mk (FiniteConeUnionWedge.subsetSetoid (FiniteConeUnionWedge.wedgePoints
      (normalPoint leftCount leftSpec leftSelected) (normalPoint rightCount rightSpec rightSelected)))
      (Sum.inl (normalPoint leftCount leftSpec leftSelected)))
  outputComponent : Fin (leftCount + rightCount - 1)
  equivalence : SingletonRetractionBasedInverse.BasedEquivalence
    (vertexWedgePoint K L a b ha)
    (normalPoint (leftCount + rightCount - 1)
      (selectedWedgeSpec leftSpec rightSpec leftSelected rightSelected) outputComponent)

  wplus : WPlus (vertexWedgeComplex K L a b)

/-- WPlus is closed under an actual wedge at any two existing vertices, preserving point components. -/
def selectedVertexWedgeClosure {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (K : PreAbstractSimplicialComplex V) (L : PreAbstractSimplicialComplex W)
    (hK : WPlus K) (hL : WPlus L)
    (a : V) (ha : ({a} : Finset V) ∈ K) (b : W) (hb : ({b} : Finset W) ∈ L) :
    SelectedVertexWedgeClosure K L a ha b hb := by
  have h : Nonempty (SelectedVertexWedgeClosure K L a ha b hb) := by
    obtain ⟨m, hm, p, i, ⟨EL⟩⟩ := based_normalization K hK a ha
    obtain ⟨n, hn, q, j, ⟨ER⟩⟩ := based_normalization L hL b hb
    let E := FiniteConeUnionWedge.basedWedgeEquivalence EL ER
    let eW : FiniteConeUnionWedge.Wedge (FiniteVertexCylinder.vertexPoint K a ha)
        (FiniteVertexCylinder.vertexPoint L b hb) ≃ₕ
        FiniteConeUnionWedge.Wedge (normalPoint m p i) (normalPoint n q j) := {
      toFun := E.forward
      invFun := E.backward
      left_inv := ⟨E.left.toHomotopy⟩
      right_inv := ⟨E.right.toHomotopy⟩ }
    let e := ((vertexGluingHomeomorph K L a b ha hb).symm.toHomotopyEquiv.trans eW).trans
      (normalWedgeHomeomorph p q i j).toHomotopyEquiv
    let x := vertexWedgePoint K L a b ha
    let k := (normalHomeomorph (m + n - 1) (selectedWedgeSpec p q i j) (e.toFun x)).1
    obtain ⟨F, _, _⟩ := SingletonRetractionBasedInverse.based_inverse x
      (normalPoint (m + n - 1) (selectedWedgeSpec p q i j) k)
      (nativeCylinder (vertexWedgeComplex K L a b) _ (vertexWedge_vertex K L a b ha))
      (nativeCylinder (normalComplex (m + n - 1) (selectedWedgeSpec p q i j)) ⟨k, none⟩
        (normalVertex_face _ _ k)) e.toFun e.invFun e.left_inv.some e.right_inv.some
      (normalPath _ _ (e.toFun x))
    refine ⟨⟨m, hm, p, i, n, hn, q, j, EL, ER, E, k, F, ?_⟩⟩
    exact ⟨m + n - 1, by omega, selectedWedgeSpec p q i j, ⟨e⟩⟩
  exact Classical.choice h

end BouquetConcatenation

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

private theorem nativeConeRebasedCollapse_forward {V : Type*} [Fintype V] [DecidableEq V]
    (P : FiniteConeCollapse.ConePair V) (z : V) (hz : ({z} : Finset V) ∈ P.cone) :
    (nativeConeRebasedCollapse P z hz).forward = P.quotientMap := rfl

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
    simpa only [List.flatMap_cons] using
      basedTrans pre (basedTrans F (basedTrans
        (FiniteConeUnionWedge.basedWedgeEquivalence P.normalization
          (ih (List.pairwise_cons.mp hd).2))
        (basedBouquetAppend P.spec
          (ps.flatMap (fun R : NormalizedVertexJoinPiece Z a => R.spec)))))

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
    simp only [ps, List.flatMap_def, List.map_ofFn, bouquetJoinPieces]
  exact e.toHomotopyEquiv.trans ((basedOrdinary F).trans (bouquetListCast hs).toHomotopyEquiv)

end BouquetJoinAssembly

#print axioms bouquetFamilyJoinNormalization
#print axioms vertexFamilyJoinBased
#print axioms spherePairJoinNormalization
#print axioms familyJoinBased
#print axioms basedBouquetAppend
#print axioms vertexUnionJoinBased
#print axioms twoComponentJoinBased
#print axioms nativeConeSuspensionHomeomorph
#print axioms nativeConeSuspension_base
#print axioms auxiliaryBasedQuotientSplit
#print axioms unionConeCollapseBased
#print axioms nativeConeRebasedCollapse
#print axioms selectedVertexWedgeClosure
#print axioms normalWedgeHomeomorph
#print axioms sphereHomeomorph
#print axioms bouquetQuotientHomeomorph
#print axioms normalHomeomorph
#print axioms based_normalization
#print axioms disjointJoinConeSplit
#print axioms coneBaseSuspensionHomeomorph
#print axioms nativeConeBaseHomeomorph
#print axioms auxiliaryBaseSplit
#print axioms vertexUnionJoinEquiv
#print axioms vertexGluingHomeomorph
#print axioms connectedVertexGluingHomeomorph
#print axioms selectedComponentWedgeBased
#print axioms selectedComponentWedgeCarrier

end D5.S3.Geometry.FiniteComponentClosure
