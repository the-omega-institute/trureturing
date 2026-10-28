/- GID: D5/S3/Geometry/FiniteComponentClosure/Transport
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteComponentClosure/Transport
   mirror-E: none(waiver:finite-component-closure)
   anchors: [mathlib/module/Mathlib.Topology.Homeomorph.Quotient]
   utility: none
   digest: Actual join transport, suspension quotients, sphere models, and finite coordinate coproducts. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.EuclideanSphereJoin
import D5.S3.Geometry.FiniteVertexCylinder
import D5.S3.Geometry.FiniteConeUnionWedge
import D5.S3.Geometry.SingletonRetractionBasedInverse
import Mathlib.Topology.Homeomorph.Quotient

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

end D5.S3.Geometry.FiniteComponentClosure
