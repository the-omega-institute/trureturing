/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/RationalTimeAction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/RationalTimeAction
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Infinite isotypic multiplicity supplies a coherent equivariant rational-time action. -/

import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteOrbitRootCriterion
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Encodable
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Commute.Basic

/-! Coherent rational-time actions from infinite isotypic multiplicity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.RationalTimeAction

open PrimitiveLiftRootCriterion PrimeOrbitRootCriterion FiniteOrbitRootCriterion
open TwoOrbitSquareRootCriterion (transport_deck)
universe u v w

private abbrev Phase := {r : ℚ // 0 ≤ r ∧ r < 1}

private instance : Nonempty Phase := ⟨⟨0, le_rfl, zero_lt_one⟩⟩

private def suspensionMap {Y : Type v} (U : Equiv.Perm Y) (q : ℚ)
    (x : Phase × Y) : Phase × Y :=
  (⟨Int.fract (x.1.val + q), Int.fract_nonneg _, Int.fract_lt_one _⟩,
   (U ^ Int.floor (x.1.val + q)) x.2)

private theorem floor_carry (a b : ℚ) :
    Int.floor (Int.fract a + b) + Int.floor a = Int.floor (a + b) := by
  rw [← Int.floor_add_intCast]
  congr 1
  rw [add_right_comm, Int.fract_add_floor]

private def suspensionEnd {Y : Type v} (U : Equiv.Perm Y) :
    Multiplicative ℚ →* Function.End (Phase × Y) where
  toFun q := suspensionMap U q.toAdd
  map_one' := by
    funext x
    apply Prod.ext
    · apply Subtype.ext
      change Int.fract (x.1.val + 0) = x.1.val
      simpa only [add_zero] using (Int.fract_eq_self.mpr x.1.property)
    · change (U ^ Int.floor (x.1.val + 0)) x.2 = x.2
      rw [add_zero, Int.floor_eq_zero_iff.mpr x.1.property, zpow_zero]
      rfl
  map_mul' p q := by
    funext x
    apply Prod.ext
    · apply Subtype.ext
      change Int.fract (x.1.val + (p.toAdd + q.toAdd)) =
        Int.fract (Int.fract (x.1.val + q.toAdd) + p.toAdd)
      rw [Int.fract_fract_add]
      congr 1
      ac_rfl
    · change (U ^ Int.floor (x.1.val + (p.toAdd + q.toAdd))) x.2 =
        (U ^ Int.floor (Int.fract (x.1.val + q.toAdd) + p.toAdd))
          ((U ^ Int.floor (x.1.val + q.toAdd)) x.2)
      rw [← Equiv.Perm.mul_apply, ← zpow_add, floor_carry]
      congr 2
      ac_rfl

private def suspension {Y : Type v} (U : Equiv.Perm Y) :
    Multiplicative ℚ →* Equiv.Perm (Phase × Y) :=
  (suspensionEnd U).toHomPerm

private theorem suspension_one {Y : Type v} (U : Equiv.Perm Y) (x : Phase × Y) :
    suspension U (Multiplicative.ofAdd (1 : ℚ)) x = (x.1, U x.2) := by
  apply Prod.ext
  · apply Subtype.ext
    change Int.fract (x.1.val + 1) = x.1.val
    rw [Int.fract_add_one, Int.fract_eq_self.mpr x.1.property]
  · change (U ^ Int.floor (x.1.val + 1)) x.2 = U x.2
    rw [Int.floor_add_one, Int.floor_eq_zero_iff.mpr x.1.property, zero_add, zpow_one]

private theorem zpow_commute {Y : Type v} (U : Equiv.Perm Y) (D : Y → Y)
    (h : Function.Commute U D) (z : ℤ) : Function.Commute (U ^ z) D := by
  have hi : Function.Commute (U⁻¹ : Equiv.Perm Y) D := by
    intro x
    apply U.injective
    simpa using (h (U.symm x)).symm
  cases z with
  | ofNat n =>
    change Function.Commute (⇑(U ^ n)) D
    rw [Equiv.Perm.coe_pow]
    exact h.iterate_left n
  | negSucc n =>
    change Function.Commute (⇑((U ^ (n + 1))⁻¹)) D
    rw [← inv_pow, Equiv.Perm.coe_pow]
    exact hi.iterate_left (n + 1)

private theorem suspension_deck {Y : Type v} (U : Equiv.Perm Y) (D : Y → Y)
    (h : Function.Commute U D) (q : ℚ) (x : Phase × Y) :
    suspension U (Multiplicative.ofAdd q) (x.1, D x.2) =
      ((suspension U (Multiplicative.ofAdd q) x).1,
       D (suspension U (Multiplicative.ofAdd q) x).2) := by
  apply Prod.ext
  · rfl
  change (U ^ Int.floor (x.1.val + q)) (D x.2) =
    D ((U ^ Int.floor (x.1.val + q)) x.2)
  exact zpow_commute U D h _ x.2

private def timePerm {H : Type u} [Group H] {Y : Type v}
    (B : ReturnAtlas H Y) : Equiv.Perm Y :=
  Equiv.ofBijective B.time ⟨B.time_injective, by
    intro y
    obtain ⟨t,z,rfl⟩ := B.covers y
    refine ⟨B.point (t-1) z, ?_⟩
    rw [B.time_point]
    congr 1 <;> omega⟩

/-- Infinite multiplicity of every actual isotypic class permits one coherent
rational action, with the specified joint time as its time-one map. -/
theorem exists_rational_time_action {H : Type u} [Group H]
    {ι : Type w} {X : ι → Type v} (A : ∀ i, ReturnAtlas H (X i))
    (hinf : ∀ i, Infinite {j // Isotypic A i j}) :
    ∃ ρ : Multiplicative ℚ →* Equiv.Perm (Σ i, X i),
      (∀ q a x, ρ q (jointDeck A a x) = jointDeck A a (ρ q x)) ∧
      (ρ (Multiplicative.ofAdd (1 : ℚ)) : (Σ i, X i) → Σ i, X i) = jointTime A := by
  classical
  let s := atlasSetoid A
  let Q := Quotient s
  let r : Q → ι := Quotient.out
  let fiber (c : Q) := {i : ι // Quotient.mk s i = c}
  have eclass (c : Q) : fiber c ≃ {j // Isotypic A (r c) j} :=
    Equiv.subtypeEquivRight (fun j => by
      change Quotient.mk s j = c ↔ s.r (r c) j
      constructor
      · intro hj
        exact s.symm (Quotient.exact (hj.trans (Quotient.out_eq c).symm))
      · intro hj
        exact (Quotient.sound (s.symm hj)).trans (Quotient.out_eq c))
  let ec (c : Q) : fiber c ≃ Phase × fiber c := by
    letI : Infinite {j // Isotypic A (r c) j} := hinf (r c)
    letI : Infinite (fiber c) := Infinite.of_injective (eclass c).symm (eclass c).symm.injective
    exact (infinite_block_equiv (C := fiber c) (P := Phase)).trans
      (Equiv.prodComm (fiber c) Phase)
  let e : ι ≃ Σ c : Q, fiber c := (Equiv.sigmaFiberEquiv (Quotient.mk s)).symm
  have hi (i : ι) : Isotypic A i (r (e i).1) := by
    change s.r i (r (e i).1)
    exact Quotient.exact (Quotient.out_eq (e i).1).symm
  choose b hb using fun i => (hi i).2
  let g (i : ι) := chartGauge (A i) (A (r (e i).1)) (hi i).1 (b i)
  let Y (c : Q) := fiber c × X (r c)
  let M := Σ c : Q, Phase × Y c
  let E : (Σ i, X i) ≃ M :=
    (Equiv.sigmaCongr e g).trans
      ((Equiv.sigmaAssoc (fun c (_ : fiber c) => X (r c))).trans
        (Equiv.sigmaCongrRight (fun c =>
          (Equiv.sigmaEquivProd (fiber c) (X (r c))).trans
            ((Equiv.prodCongr (ec c) (Equiv.refl (X (r c)))).trans
              (Equiv.prodAssoc Phase (fiber c) (X (r c)))))))
  let pack (i : ι) (y : X (r (e i).1)) : M :=
    ⟨(e i).1, (ec (e i).1 (e i).2).1, (ec (e i).1 (e i).2).2, y⟩
  let U (c : Q) : Equiv.Perm (Y c) :=
    Equiv.prodCongr (Equiv.refl (fiber c)) (timePerm (A (r c)))
  let T : M → M := fun x => ⟨x.1, x.2.1, U x.1 x.2.2⟩
  let D (a : H) : M → M := fun x =>
    ⟨x.1, x.2.1, x.2.2.1, (A (r x.1)).deck a x.2.2.2⟩
  have et : Function.Semiconj E (jointTime A) T := by
    rintro ⟨i,x⟩
    change pack i (g i ((A i).time x)) = pack i ((A (r (e i).1)).time (g i x))
    exact congrArg (pack i)
      (chartGauge_time (A i) (A (r (e i).1)) (hi i).1 (b i) (hb i) x)
  have ed : ∀ a x, E (jointDeck A a x) = D a (E x) := by
    rintro a ⟨i,x⟩
    change pack i (g i ((A i).deck a x)) =
      pack i ((A (r (e i).1)).deck a (g i x))
    exact congrArg (pack i)
      (transport_deck (A i) (A (r (e i).1)) (hi i).1 (b i) (hb i) a x)
  let G : Multiplicative ℚ →* Equiv.Perm M :=
    { toFun := fun q => Equiv.Perm.sigmaCongrRight (fun c => suspension (U c) q)
      map_one' := by
        apply Equiv.ext
        rintro ⟨c,y⟩
        change (⟨c, suspension (U c) 1 y⟩ : M) = ⟨c,y⟩
        rw [map_one]
        rfl
      map_mul' := by
        intro q p
        apply Equiv.ext
        rintro ⟨c,y⟩
        change (⟨c, suspension (U c) (q*p) y⟩ : M) =
          ⟨c, suspension (U c) q (suspension (U c) p y)⟩
        rw [map_mul]
        rfl }
  have gt : (G (Multiplicative.ofAdd (1 : ℚ)) : M → M) = T := by
    funext ⟨c,p,y⟩
    change (⟨c, suspension (U c) (Multiplicative.ofAdd (1 : ℚ)) (p,y)⟩ : M) = _
    rw [suspension_one]
  have gd : ∀ q a x, G q (D a x) = D a (G q x) := by
    rintro q a ⟨c,p,j,x⟩
    let d : Y c → Y c := fun y => ⟨y.1, (A (r c)).deck a y.2⟩
    have hd : Function.Commute (U c) d := by
      rintro ⟨j,x⟩
      obtain ⟨t,z,rfl⟩ := (A (r c)).covers x
      change (j, (A (r c)).time ((A (r c)).deck a ((A (r c)).point t z))) =
        (j, (A (r c)).deck a ((A (r c)).time ((A (r c)).point t z)))
      rw [(A (r c)).deck_point, (A (r c)).time_point,
        (A (r c)).time_point, (A (r c)).deck_point]
    exact congrArg (Sigma.mk c) (suspension_deck (U c) d hd q.toAdd (p,(j,x)))
  let ρ := E.symm.permCongrHom.toMonoidHom.comp G
  have er (q : Multiplicative ℚ) (x : Σ i, X i) : E (ρ q x) = G q (E x) :=
    E.apply_symm_apply _
  refine ⟨ρ, ?_, ?_⟩
  · intro q a x
    apply E.injective
    rw [er, ed, gd, ed, er]
  · funext x
    apply E.injective
    rw [er, gt, et]

end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.RationalTimeAction
