/- GID: D5/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PrimitiveLifts/PrimitiveLiftRootCriterion
   mirror-E: none(waiver:symbolic-structural-theorems)
   anchors: []
   utility: none
   digest: Actual primitive lifts have a centralizer normal form and an exact signed return equation for equivariant time roots. -/

import D5.S3.ConceptDynamics.Coding.OrderedGroupChainHistories
import D5.S3.ConceptDynamics.Coding.TwistedPeriodicHistories
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Tactic.Group

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.ConceptDynamics.Coding.PrimitiveLifts.PrimitiveLiftRootCriterion

universe u v

/-- A complete signed return chart. Its equality law records the holonomy,
rather than merely the periods of the underlying permutation. -/
structure ReturnAtlas (H : Type u) [Group H] (X : Type v) where
  period : ℕ
  positive : 0 < period
  holonomy : H
  point : ℤ → H → X
  covers : ∀ x, ∃ t z, point t z = x
  relation : ∀ t s z w, point t z = point s w ↔
    ∃ m : ℤ, t = s + (period : ℤ) * m ∧ z * holonomy ^ m = w
  time : X → X
  time_point : ∀ t z, time (point t z) = point (t + 1) z
  deck : H → X → X
  deck_point : ∀ a t z, deck a (point t z) = point t (a * z)

namespace ReturnAtlas
variable {H : Type u} [Group H] {X : Type v} (A : ReturnAtlas H X)

private theorem same_time (t : ℤ) {z w : H} : A.point t z = A.point t w ↔ z = w := by
  rw [A.relation]
  constructor
  · rintro ⟨m, hm, hz⟩
    have hd : (A.period : ℤ) ≠ 0 := by exact_mod_cast A.positive.ne'
    have : m = 0 := by rcases mul_eq_zero.mp (show (A.period : ℤ)*m = 0 by omega) with h | h; exact (hd h).elim; exact h
    simpa [this] using hz
  · intro h; exact ⟨0, by omega, by simpa using h⟩

private theorem reduce (t : ℤ) (z : H) :
    A.point t z = A.point (t % A.period) (z * A.holonomy ^ (t / A.period)) := by
  apply (A.relation _ _ _ _).2
  exact ⟨t / A.period, by have := Int.ediv_mul_add_emod t (A.period:ℤ); nlinarith, rfl⟩

/-- Finite phases and an unrestricted group coordinate parametrize the entire carrier. -/
def coordinates : Fin A.period × H ≃ X :=
  Equiv.ofBijective (fun q => A.point q.1.val q.2) (by
    constructor
    · rintro ⟨q,z⟩ ⟨r,w⟩ h
      obtain ⟨m, hm, hz⟩ := (A.relation _ _ _ _).1 h
      change (q.val:ℤ) = (r.val:ℤ) + (A.period:ℤ)*m at hm
      have hd : (0:ℤ) < A.period := by exact_mod_cast A.positive
      have hq : (q.val:ℤ) < A.period := by exact_mod_cast q.isLt
      have hr : (r.val:ℤ) < A.period := by exact_mod_cast r.isLt
      have hq0 : (0:ℤ) ≤ q.val := Int.natCast_nonneg _
      have hr0 : (0:ℤ) ≤ r.val := Int.natCast_nonneg _
      have hm0 : m = 0 := by
        by_contra hn
        rcases lt_or_gt_of_ne hn with hn | hn
        · have : m ≤ -1 := by omega
          nlinarith
        · have : 1 ≤ m := by omega
          nlinarith
      have hqr : q = r := Fin.ext (by simp only [hm0,mul_zero,add_zero] at hm; exact_mod_cast hm)
      have hzw : z = w := by simpa [hm0] using hz
      exact Prod.ext hqr hzw
    · intro x
      obtain ⟨t,z,rfl⟩ := A.covers x
      have hd : (0 : ℤ) < A.period := by exact_mod_cast A.positive
      let r : Fin A.period := ⟨(t % A.period).toNat, by
        have := Int.emod_lt_of_pos t hd
        have := Int.emod_nonneg t (ne_of_gt hd)
        omega⟩
      refine ⟨(r,z * A.holonomy ^ (t / A.period)), ?_⟩
      have hr : (r.val : ℤ) = t % A.period := by
        dsimp [r]
        exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hd))
      change A.point (r.val : ℤ) _ = _
      rw [hr]
      exact (A.reduce t z).symm)

theorem time_injective : Function.Injective A.time := by
  intro x y h
  obtain ⟨t,z,rfl⟩ := A.covers x
  obtain ⟨s,w,rfl⟩ := A.covers y
  rw [A.time_point, A.time_point, A.relation] at h
  obtain ⟨m, hm, hz⟩ := h
  exact (A.relation _ _ _ _).2 ⟨m, by omega, hz⟩

/-- Group equivariance refers to the specified left deck action. -/
def Equivariant (f : X → X) : Prop := ∀ a x, f (A.deck a x) = A.deck a (f x)

private theorem propagate (f : X → X) (hf : A.Equivariant f)
    (ht : Function.Commute f A.time) {s : ℤ} {b : H}
    (h0 : f (A.point 0 1) = A.point s b) :
    ∀ t z, f (A.point t z) = A.point (t + s) (z * b) := by
  have hz : ∀ z, f (A.point 0 z) = A.point s (z*b) := by
    intro z
    simpa only [mul_one, zero_add, A.deck_point] using
      (hf z (A.point 0 1)).trans (congrArg (A.deck z) h0)
  have hp : ∀ n : ℕ, ∀ z, f (A.point (n : ℤ) z) = A.point ((n : ℤ)+s) (z*b) := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih =>
      intro z
      rw [show ((n+1 : ℕ) : ℤ) = (n:ℤ)+1 by omega, ← A.time_point,
        ht, ih, A.time_point]
      congr 1 <;> omega
  have hn : ∀ n : ℕ, ∀ z, f (A.point (-(n : ℤ)) z) = A.point (-(n:ℤ)+s) (z*b) := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih =>
      intro z
      apply A.time_injective
      rw [← ht, A.time_point, A.time_point]
      have h : -((n+1 : ℕ):ℤ)+1 = -(n:ℤ) := by omega
      rw [h, ih]
      congr 1 <;> omega
  intro t
  cases t with
  | ofNat n => exact hp n
  | negSucc n =>
    have hi : Int.negSucc n = -((n+1:ℕ):ℤ) := by omega
    rw [hi]
    exact hn (n+1)

/-- Reverse classification, including the noncommutative seam constraint. -/
theorem normal_form (f : X → X) (hf : A.Equivariant f)
    (ht : Function.Commute f A.time) :
    ∃! q : Fin A.period × H,
      Commute q.2 A.holonomy ∧
      ∀ t z, f (A.point t z) = A.point (t + q.1.val) (z*q.2) := by
  let q := A.coordinates.symm (f (A.point 0 1))
  have hq : f (A.point 0 1) = A.point q.1.val q.2 := (A.coordinates.apply_symm_apply _).symm
  have law := A.propagate f hf ht hq
  have seam : A.point (A.period : ℤ) 1 = A.point 0 A.holonomy :=
    (A.relation _ _ _ _).2 ⟨1, by omega, by simp⟩
  have out := congrArg f seam
  rw [law, law] at out
  have ret : A.point ((A.period:ℤ)+q.1.val) q.2 = A.point q.1.val (q.2*A.holonomy) :=
    (A.relation _ _ _ _).2 ⟨1, by omega, by simp⟩
  simp only [one_mul, zero_add] at out
  rw [ret] at out
  have hc : Commute q.2 A.holonomy := (A.same_time _).1 out
  refine ⟨q, ⟨hc,law⟩, ?_⟩
  intro r hr
  apply A.coordinates.injective
  change A.point r.1.val r.2 = A.point q.1.val q.2
  simpa using (hr.2 0 1).symm.trans hq

/-- The normal map, constructed on the same carrier by its complete coordinates. -/
def normalMap (s : ℤ) (b : H) : X → X := fun x =>
  let q := A.coordinates.symm x
  A.point ((q.1.val : ℤ)+s) (q.2*b)

private theorem normalMap_point (s : ℤ) (b : H) (hb : Commute b A.holonomy)
    (t : ℤ) (z : H) :
    A.normalMap s b (A.point t z) = A.point (t+s) (z*b) := by
  let q := A.coordinates.symm (A.point t z)
  have he : A.point t z = A.point q.1.val q.2 := (A.coordinates.apply_symm_apply _).symm
  obtain ⟨m,hm,hz⟩ := (A.relation _ _ _ _).1 he
  change A.point ((q.1.val:ℤ)+s) (q.2*b) = A.point (t+s) (z*b)
  symm
  apply (A.relation _ _ _ _).2
  refine ⟨m, by omega, ?_⟩
  rw [← hz]
  have hc := (hb.zpow_right m).eq
  calc
    (z*b)*A.holonomy^m = z*(b*A.holonomy^m) := mul_assoc _ _ _
    _ = z*(A.holonomy^m*b) := congrArg (z*·) hc
    _ = z*A.holonomy^m*b := (mul_assoc _ _ _).symm

private theorem normalMap_equivariant (s : ℤ) (b : H) (hb : Commute b A.holonomy) :
    A.Equivariant (A.normalMap s b) := by
  intro a x
  obtain ⟨t,z,rfl⟩ := A.covers x
  rw [A.deck_point, A.normalMap_point s b hb, A.normalMap_point s b hb, A.deck_point, mul_assoc]

private theorem normalMap_iterate (s : ℤ) (b : H) (hb : Commute b A.holonomy)
    (k : ℕ) (t : ℤ) (z : H) :
    (A.normalMap s b)^[k] (A.point t z) = A.point (t + k*s) (z*b^k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, A.normalMap_point s b hb, pow_succ]
    congr 1
    · push_cast; ring
    · exact mul_assoc _ _ _

/-- Every lawful normal map is an actual permutation of the carrier. -/
def normalEquiv (s : ℤ) (b : H) (hb : Commute b A.holonomy) : Equiv.Perm X where
  toFun := A.normalMap s b
  invFun := A.normalMap (-s) b⁻¹
  left_inv x := by
    obtain ⟨t,z,rfl⟩ := A.covers x
    rw [A.normalMap_point s b hb, A.normalMap_point (-s) b⁻¹ hb.inv_left]
    simp
  right_inv x := by
    obtain ⟨t,z,rfl⟩ := A.covers x
    rw [A.normalMap_point (-s) b⁻¹ hb.inv_left, A.normalMap_point s b hb]
    simp

/-- A root need only be deck equivariant: commuting with time follows from its power.
The return exponent is an integer and can be negative. -/
theorem root_criterion (k : ℕ) :
    (∃ f : X → X, A.Equivariant f ∧ f^[k] = A.time) ↔
    ∃ s : Fin A.period, ∃ m : ℤ, ∃ b : H, Commute b A.holonomy ∧
      (k:ℤ)*(s.val:ℤ) = 1 + (A.period:ℤ)*m ∧ b^k*A.holonomy^m = 1 := by
  constructor
  · rintro ⟨f,hf,hroot⟩
    have ht : Function.Commute f A.time := by
      rw [← hroot]
      exact Function.Commute.self_iterate f k
    obtain ⟨q,⟨hb,law⟩,_⟩ := A.normal_form f hf ht
    have iter : ∀ j : ℕ, ∀ t z, f^[j] (A.point t z) =
        A.point (t + (j:ℤ)*q.1.val) (z*q.2^j) := by
      intro j
      induction j with
      | zero => intros; simp
      | succ j ih =>
        intro t z
        rw [Function.iterate_succ_apply', ih, law, pow_succ]
        congr 1
        · push_cast; ring
        · exact mul_assoc _ _ _
    have out := congrFun hroot (A.point 0 1)
    rw [iter, A.time_point] at out
    simp only [zero_add, one_mul] at out
    obtain ⟨m,hm,hz⟩ := (A.relation _ _ _ _).1 out
    exact ⟨q.1,m,q.2,hb,hm,hz⟩
  · rintro ⟨s,m,b,hb,hm,hz⟩
    refine ⟨A.normalEquiv s.val b hb, A.normalMap_equivariant s.val b hb, ?_⟩
    funext x
    obtain ⟨t,z,rfl⟩ := A.covers x
    change (A.normalMap s.val b)^[k] (A.point t z) = A.time (A.point t z)
    rw [A.normalMap_iterate s.val b hb, A.time_point]
    apply (A.relation _ _ _ _).2
    exact ⟨m, by omega, by simpa [mul_assoc] using congrArg (z*·) hz⟩

end ReturnAtlas

open EssentialWordRealization FiniteWindowTableCriterion FixedBlockRigidity
open FixedBlockRigidity.BlockCoordinates OrderedGroupChainHistories
open CountedGroupOverlap (GroupMat Path Edge)

section Actual
variable {H : Type u} [Group H] {n : ℕ} (C : GroupMat H n n)
  (p : Path C) (d : ℕ) (hd : 0 < d)
  (hmin : Function.minimalPeriod (CountedGroupOverlap.shift C) p = d)

/-- The ordered label of the actual zero-phase primitive loop. -/
def orbitHolonomy : H := totalLabel (historyWindow (baseGraph C) p 0 d)

private theorem holonomy_coordinate :
    orbitHolonomy C p d = anchoredCoordinate p 1 (d : ℤ) := by
  have pref : ∀ r : ℕ, r ≤ d →
      prefixLabel (historyWindow (baseGraph C) p 0 d) r = (positiveLabels p r).prod := by
    intro r
    induction r with
    | zero => intro _; simp [prefixLabel, positiveLabels]
    | succ r ih =>
      intro hr
      rw [prefixLabel, dif_pos (show r < d by omega), ih (by omega)]
      simp [positiveLabels, List.prod_append, historyWindow]
  simpa [orbitHolonomy, totalLabel, anchoredCoordinate] using pref d le_rfl

private def origin : History (expandedGraph C) := anchoredHistory p 1

include hmin in
private theorem origin_return :
    (shift (expandedGraph C))^[d] (origin C p) =
      groupHistory C (orbitHolonomy C p d) (origin C p) := by
  apply (anchoredEquiv C).injective
  rw [shift_iterate_translate]
  apply Prod.ext
  · change (⟨fun i => p.val (i+(d:ℤ)), _⟩ : Path C) = p
    have hp := Function.isPeriodicPt_minimalPeriod (CountedGroupOverlap.shift C) p
    rw [hmin] at hp
    change (shift (baseGraph C))^[d] p = p at hp
    rw [shift_iterate_translate] at hp
    exact hp
  · change anchoredCoordinate p 1 ((0:ℤ)+(d:ℤ)) =
      orbitHolonomy C p d * anchoredCoordinate p 1 0
    simp only [zero_add, anchored_zero, mul_one]
    exact (holonomy_coordinate C p d).symm

private def rawPoint (t : ℤ) (z : H) : History (expandedGraph C) :=
  groupHistory C z (translate (expandedGraph C) t (origin C p))

include hmin in
private theorem raw_return (t m : ℤ) (z : H) :
    rawPoint C p (t+(d:ℤ)*m) z = rawPoint C p t (z*orbitHolonomy C p d^m) := by
  apply Subtype.ext
  funext i
  have h := TwistedPeriodicHistories.signed_recovery C (orbitHolonomy C p d)
    (⟨origin C p, origin_return C p d hmin⟩ :
      TwistedPeriodicHistories.TwistedPeriod C (orbitHolonomy C p d) d) m (i+t)
  change (origin C p).val (i+t + m*(d:ℤ)) = _ at h
  change (((origin C p).val (i+(t+(d:ℤ)*m))).1,
      z*((origin C p).val (i+(t+(d:ℤ)*m))).2) =
      (((origin C p).val (i+t)).1,
        (z*orbitHolonomy C p d^m)*((origin C p).val (i+t)).2)
  have hi : i+(t+(d:ℤ)*m) = i+t+m*(d:ℤ) := by ring
  rw [hi,h]
  simp only [mul_assoc]


private theorem raw_forget (t : ℤ) (z : H) :
    forgetHistory (rawPoint C p t z) = translate (baseGraph C) t p := rfl

include hmin in
private theorem raw_reduced (t : ℤ) (z : H) :
    rawPoint C p t z = rawPoint C p (t % d) (z*orbitHolonomy C p d^(t/(d:ℤ))) := by
  have h := raw_return C p d hmin (t % d) (t/(d:ℤ)) z
  have hi : t % (d:ℤ) + (d:ℤ)*(t/(d:ℤ)) = t := by
    have := Int.ediv_mul_add_emod t (d:ℤ)
    nlinarith
  rw [hi] at h
  exact h

include hmin in
private theorem raw_injective {q r : Fin d} {z w : H}
    (h : rawPoint C p q.val z = rawPoint C p r.val w) : q = r ∧ z = w := by
  have hb := congrArg forgetHistory h
  rw [raw_forget,raw_forget] at hb
  have hiter : (CountedGroupOverlap.shift C)^[q.val] p =
      (CountedGroupOverlap.shift C)^[r.val] p := by
    change (shift (baseGraph C))^[q.val] p = (shift (baseGraph C))^[r.val] p
    rw [shift_iterate_translate,shift_iterate_translate]
    exact hb
  have hqr : q = r := Fin.ext
    ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
      (by simpa [hmin] using q.isLt) (by simpa [hmin] using r.isLt)).1 hiter)
  subst r
  have hw := congrArg (fun x : History (expandedGraph C) => (x.val (-(q.val:ℤ))).2) h
  have hz : z = w := by
    simpa [rawPoint, translate, origin, anchoredHistory, groupHistory] using hw
  exact ⟨rfl,hz⟩

/-- All actual lifts of the specified primitive base orbit; no lift is selected away. -/
def LiftOrbit := {x : History (expandedGraph C) //
  ∃ q : Fin d, forgetHistory x = (CountedGroupOverlap.shift C)^[q.val] p}

include hd hmin in
private theorem raw_mem (t : ℤ) (z : H) :
    ∃ q : Fin d, forgetHistory (rawPoint C p t z) =
      (CountedGroupOverlap.shift C)^[q.val] p := by
  have hd' : (0:ℤ) < d := by exact_mod_cast hd
  let q : Fin d := ⟨(t%(d:ℤ)).toNat, by
    have := Int.emod_nonneg t (ne_of_gt hd')
    have := Int.emod_lt_of_pos t hd'
    omega⟩
  refine ⟨q, ?_⟩
  rw [raw_reduced C p d hmin,raw_forget]
  have hq : (q.val:ℤ) = t%(d:ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hd'))
  rw [← hq]
  exact (shift_iterate_translate (baseGraph C) q.val p).symm

private def actualPoint (t : ℤ) (z : H) : LiftOrbit C p d :=
  ⟨rawPoint C p t z, raw_mem C p d hd hmin t z⟩

private theorem raw_covers (x : LiftOrbit C p d) :
    ∃ t z, rawPoint C p t z = x.val := by
  obtain ⟨q,hq⟩ := x.property
  let y := translate (expandedGraph C) (-(q.val:ℤ)) x.val
  have hy : forgetHistory y = p := by
    change forgetHistory x.val = (shift (baseGraph C))^[q.val] p at hq
    rw [shift_iterate_translate] at hq
    change translate (baseGraph C) (-(q.val:ℤ)) (forgetHistory x.val) = p
    rw [hq]
    apply Subtype.ext
    funext i
    simp [translate]
  let z := (y.val 0).2
  have he : y = anchoredHistory p z := by
    apply (anchoredEquiv C).injective
    apply Prod.ext hy
    simp [anchoredEquiv,anchoredHistory,z]
  refine ⟨q.val,z,?_⟩
  have hanchor : anchoredHistory p z = groupHistory C z (origin C p) := by
    apply (anchoredEquiv C).injective
    apply Prod.ext
    · rfl
    · simp [anchoredEquiv, groupHistory, origin, anchoredHistory]
  rw [hanchor] at he
  have ht := congrArg (translate (expandedGraph C) (q.val:ℤ)) he
  apply Subtype.ext
  funext i
  have ht' := congrArg (fun a : History (expandedGraph C) => a.val i) ht
  simpa [y, translate, rawPoint, groupHistory] using ht'.symm

include hd hmin in
private theorem raw_relation (t s : ℤ) (z w : H) :
    rawPoint C p t z = rawPoint C p s w ↔
      ∃ m : ℤ, t = s+(d:ℤ)*m ∧ z*orbitHolonomy C p d^m = w := by
  constructor
  · intro h
    have hd' : (0:ℤ) < d := by exact_mod_cast hd
    let q : Fin d := ⟨(t%(d:ℤ)).toNat, by
      have := Int.emod_nonneg t (ne_of_gt hd'); have := Int.emod_lt_of_pos t hd'; omega⟩
    let r : Fin d := ⟨(s%(d:ℤ)).toNat, by
      have := Int.emod_nonneg s (ne_of_gt hd'); have := Int.emod_lt_of_pos s hd'; omega⟩
    have hq : (q.val:ℤ) = t%(d:ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hd'))
    have hr : (r.val:ℤ) = s%(d:ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hd'))
    rw [raw_reduced C p d hmin t z, raw_reduced C p d hmin s w, ← hq, ← hr] at h
    obtain ⟨hqr,hzw⟩ := raw_injective C p d hmin h
    have hrem : t%(d:ℤ) = s%(d:ℤ) := hq.symm.trans ((congrArg (fun a : Fin d => (a.val:ℤ)) hqr).trans hr)
    refine ⟨t/(d:ℤ)-s/(d:ℤ), ?_, ?_⟩
    · have ht := Int.ediv_mul_add_emod t (d:ℤ)
      have hs := Int.ediv_mul_add_emod s (d:ℤ)
      rw [hrem] at ht
      nlinarith
    · rw [zpow_sub]
      calc
        z * (orbitHolonomy C p d ^ (t/(d:ℤ)) * (orbitHolonomy C p d ^ (s/(d:ℤ)))⁻¹) =
            (z * orbitHolonomy C p d ^ (t/(d:ℤ))) * (orbitHolonomy C p d ^ (s/(d:ℤ)))⁻¹ := (mul_assoc _ _ _).symm
        _ = (w * orbitHolonomy C p d ^ (s/(d:ℤ))) * (orbitHolonomy C p d ^ (s/(d:ℤ)))⁻¹ := by rw [hzw]
        _ = w := mul_inv_cancel_right _ _
  · rintro ⟨m,rfl,hw⟩
    rw [raw_return C p d hmin,hw]

private theorem raw_time (t : ℤ) (z : H) :
    shift (expandedGraph C) (rawPoint C p t z) = rawPoint C p (t+1) z := by
  apply Subtype.ext
  funext i
  simp [rawPoint,shift,translate,groupHistory,add_assoc,add_comm,add_left_comm]

/-- The complete actual-history chart, with right holonomy and left deck action. -/
def actualAtlas : ReturnAtlas H (LiftOrbit C p d) where
  period := d
  positive := hd
  holonomy := orbitHolonomy C p d
  point := actualPoint C p d hd hmin
  covers x := by
    obtain ⟨t,z,h⟩ := raw_covers C p d x
    exact ⟨t,z,Subtype.ext h⟩
  relation t s z w := by
    constructor
    · intro h
      exact (raw_relation C p d hd hmin t s z w).1 (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((raw_relation C p d hd hmin t s z w).2 h)
  time x := by
    refine ⟨shift (expandedGraph C) x.val, ?_⟩
    obtain ⟨t,z,h⟩ := raw_covers C p d x
    rw [← h,raw_time]
    exact raw_mem C p d hd hmin (t+1) z
  time_point t z := by
    apply Subtype.ext
    exact raw_time C p t z
  deck a x := ⟨groupHistory C a x.val, by
    obtain ⟨q,hq⟩ := x.property
    exact ⟨q,hq⟩⟩
  deck_point a t z := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simp [actualPoint,rawPoint,groupHistory,mul_assoc]

end Actual
end D5.S3.ConceptDynamics.Coding.PrimitiveLifts.PrimitiveLiftRootCriterion
