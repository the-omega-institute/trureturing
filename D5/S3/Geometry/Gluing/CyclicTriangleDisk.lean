/- GID: D5/S3/Geometry/Gluing/CyclicTriangleDisk
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/CyclicTriangleDisk
   mirror-E: none(waiver:explicit-cyclic-triangle-topology)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Complex.CircleMap]
   utility: none
   digest: Cyclic triangle seams carry an explicit radial disk homeomorphism. -/

import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Data.Real.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Logic.Relation
import Mathlib.Order.SuccPred.Relation
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S3.Geometry.Gluing.CyclicTriangleDisk

open scoped Fin.NatCast
open scoped Topology

noncomputable section

abbrev Triangle := {p : ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}
abbrev Point (n : ℕ) := Fin n × Triangle

def swap (p : Triangle) : Triangle :=
  ⟨(p.val.2, p.val.1), p.property.2.1, p.property.1,
    by simpa only [add_comm] using p.property.2.2⟩

def radius {n : ℕ} (x : Point n) : ℝ := x.2.val.1 + x.2.val.2

def apex {n : ℕ} (i : Fin n) : Point n :=
  (i, ⟨(0, 0), by norm_num⟩)

/-- The source seam is exactly `(i,t,0) ~ (i+1,0,t)`. -/
def seam {n : ℕ} [NeZero n] (x y : Point n) : Prop :=
  x.2.val.2 = 0 ∧ y = (x.1 + 1, swap x.2)

abbrev Related {n : ℕ} [NeZero n] : Point n → Point n → Prop :=
  Relation.EqvGen seam

/-- `none` denotes the common apex; positive representatives have second coordinate positive. -/
def normal {n : ℕ} [NeZero n] (x : Point n) : Option (Point n) := by
  classical
  exact if radius x = 0 then none else
    if x.2.val.2 = 0 then some (x.1 + 1, swap x.2) else some x

private theorem coordinates_zero {n : ℕ} (x : Point n) (h : radius x = 0) :
    x.2.val.1 = 0 ∧ x.2.val.2 = 0 := by
  have ha := x.2.property.1
  have hb := x.2.property.2.1
  change x.2.val.1 + x.2.val.2 = 0 at h
  constructor <;> linarith

private theorem normal_none {n : ℕ} [NeZero n] (x : Point n) :
    normal x = none ↔ radius x = 0 := by
  classical
  by_cases hr : radius x = 0
  · simp only [normal, hr, if_pos]
  · by_cases hb : x.2.val.2 = 0 <;> simp [normal, hr, hb]

private theorem seam_normal {n : ℕ} [NeZero n] {x y : Point n}
    (h : seam x y) : normal x = normal y := by
  classical
  obtain ⟨hb, rfl⟩ := h
  by_cases ha : x.2.val.1 = 0 <;>
    simp [normal, radius, swap, hb, ha]

private theorem related_to_normal {n : ℕ} [NeZero n] {x z : Point n}
    (h : normal x = some z) : Related x z := by
  classical
  by_cases hr : radius x = 0
  · simp only [normal, hr, if_pos] at h
    cases h
  · by_cases hb : x.2.val.2 = 0
    · simp only [normal, hr, if_false, hb, if_pos, Option.some.injEq] at h
      subst z
      exact Relation.EqvGen.rel _ _ ⟨hb, rfl⟩
    · simp only [normal, hr, if_false, hb, Option.some.injEq] at h
      subst z
      exact Relation.EqvGen.refl _

private theorem eq_apex {n : ℕ} (x : Point n) (h : radius x = 0) :
    x = apex x.1 := by
  have hz := coordinates_zero x h
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact Prod.ext hz.1 hz.2

private theorem zero_to_apex_nat {n : ℕ} [NeZero n] (k : ℕ) :
    Related (apex (0 : Fin n)) (apex (k : Fin n)) := by
  let A : ℕ → Point n := fun j => apex (j : Fin n)
  let r : ℕ → ℕ → Prop := fun j l => seam (A j) (A l)
  have hs (j : ℕ) : r j (Order.succ j) := by
    refine ⟨rfl,?_⟩
    apply Prod.ext
    · change ((j + 1 : ℕ) : Fin n) = (j : Fin n) + 1
      simp only [Nat.cast_add,Nat.cast_one]
    · rfl
  have hpath : Relation.ReflTransGen r 0 k :=
    reflTransGen_of_succ_of_le r (fun j _ => hs j) (Nat.zero_le k)
  exact Relation.EqvGen.reflTransGen_le_eqvGen seam _ _
    (Relation.ReflTransGen.lift A (fun _ _ h => h) _ _ hpath)

private theorem zero_to_apex {n : ℕ} [NeZero n] (i : Fin n) :
    Related (apex (0 : Fin n)) (apex i) := by
  simpa only [Fin.cast_val_eq_self] using zero_to_apex_nat (n := n) i.val

/-- The actual seam-generated equivalence has precisely the displayed normal forms. -/
theorem related_iff_normal_eq {n : ℕ} [NeZero n] (x y : Point n) :
    Related x y ↔ normal x = normal y := by
  classical
  constructor
  · intro h
    induction h with
    | rel x y hs => exact seam_normal hs
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz
  · intro h
    cases hx : normal x with
    | none =>
      have hy : normal y = none := h.symm.trans hx
      have hxr := (normal_none x).mp hx
      have hyr := (normal_none y).mp hy
      rw [eq_apex x hxr, eq_apex y hyr]
      exact Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (zero_to_apex x.1)) (zero_to_apex y.1)
    | some z =>
      have hy : normal y = some z := h.symm.trans hx
      exact Relation.EqvGen.trans _ _ _ (related_to_normal hx)
        (Relation.EqvGen.symm _ _ (related_to_normal hy))

def angle {n : ℕ} [NeZero n] (x : Point n) : ℝ :=
  (2 * Real.pi / (n : ℝ)) * ((x.1.val : ℝ) + x.2.val.1 / radius x)

/-- The prescribed radius-preserving map, with an explicit value at the apex. -/
def radial {n : ℕ} [NeZero n] (x : Point n) : ℂ := by
  classical
  exact if radius x = 0 then 0 else circleMap 0 (radius x) (angle x)

private theorem radius_nonneg {n : ℕ} (x : Point n) : 0 ≤ radius x :=
  add_nonneg x.2.property.1 x.2.property.2.1

/-- The radial image norm is the sum of the triangle coordinates. -/
theorem radial_norm {n : ℕ} [NeZero n] (x : Point n) :
    ‖radial x‖ = radius x := by
  classical
  by_cases hr : radius x = 0
  · simp [radial, hr]
  · simp only [radial, if_neg hr, norm_circleMap_zero, abs_of_nonneg (radius_nonneg x)]

private theorem next_value {n : ℕ} [NeZero n] (i : Fin n) :
    (i + 1).val = i.val + 1 ∨ ((i + 1).val = 0 ∧ i.val + 1 = n) := by
  have hval : (i + 1).val = (i.val + 1) % n := by
    simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  by_cases hi : i.val + 1 < n
  · exact Or.inl (hval.trans (Nat.mod_eq_of_lt hi))
  · have heq : i.val + 1 = n := by omega
    exact Or.inr ⟨by simp only [hval, heq, Nat.mod_self], heq⟩

private theorem seam_radial {n : ℕ} [NeZero n] {x y : Point n}
    (h : seam x y) : radial x = radial y := by
  classical
  obtain ⟨hb, rfl⟩ := h
  by_cases ha : x.2.val.1 = 0
  · simp [radial, radius, swap, hb, ha]
  · rcases next_value x.1 with hnext | ⟨hnext, hlast⟩
    · simp [radial, angle, radius, swap, hb, ha, hnext, Nat.cast_add, Nat.cast_one]
    · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
      have hi : (x.1.val : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hlast
      have ht : (2 * Real.pi / (n : ℝ)) * ((x.1.val : ℝ) + 1) =
          2 * Real.pi := by
        rw [hi]
        exact div_mul_cancel₀ _ hn
      simpa [radial, angle, radius, swap, hb, ha, hnext, ht] using
        (periodic_circleMap (0 : ℂ) x.2.val.1 0)

private theorem radial_eq_of_related {n : ℕ} [NeZero n] {x y : Point n}
    (h : Related x y) : radial x = radial y := by
  induction h with
  | rel x y hs => exact seam_radial hs
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

private theorem normal_positive {n : ℕ} [NeZero n] {x u : Point n}
    (h : normal x = some u) : 0 < u.2.val.2 := by
  classical
  by_cases hr : radius x = 0
  · simp only [normal, hr, if_pos] at h
    cases h
  · by_cases hb : x.2.val.2 = 0
    · simp only [normal, hr, if_false, hb, if_pos, Option.some.injEq] at h
      subst u
      change 0 < x.2.val.1
      have ha := x.2.property.1
      change x.2.val.1 + x.2.val.2 ≠ 0 at hr
      rw [hb, add_zero] at hr
      exact lt_of_le_of_ne ha hr.symm
    · simp only [normal, hr, if_false, hb, Option.some.injEq] at h
      subst u
      exact lt_of_le_of_ne x.2.property.2.1 (Ne.symm hb)

private theorem positive_angle_bounds {n : ℕ} [NeZero n] (x : Point n)
    (hb : 0 < x.2.val.2) :
    0 < radius x ∧ 0 ≤ x.2.val.1 / radius x ∧ x.2.val.1 / radius x < 1 ∧
      angle x ∈ Set.Ico 0 (2 * Real.pi) := by
  have ha := x.2.property.1
  have hr : 0 < radius x := by
    dsimp only [radius]
    linarith
  have hfrac0 : 0 ≤ x.2.val.1 / radius x := div_nonneg ha hr.le
  have hfrac1 : x.2.val.1 / radius x < 1 := (div_lt_one hr).mpr (by
    dsimp only [radius]
    linarith)
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  have hc : 0 < 2 * Real.pi / (n : ℝ) := div_pos (by positivity) hn
  have hk : (x.1.val : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt x.1.isLt)
  have hcoord : (x.1.val : ℝ) + x.2.val.1 / radius x < (n : ℝ) := by
    linarith
  refine ⟨hr, hfrac0, hfrac1, ?_, ?_⟩
  · exact mul_nonneg hc.le (add_nonneg (Nat.cast_nonneg _) hfrac0)
  · change (2 * Real.pi / (n : ℝ)) *
        ((x.1.val : ℝ) + x.2.val.1 / radius x) < 2 * Real.pi
    calc
      _ < (2 * Real.pi / (n : ℝ)) * (n : ℝ) := mul_lt_mul_of_pos_left hcoord hc
      _ = 2 * Real.pi := div_mul_cancel₀ _ hn.ne'

private theorem radial_injective_on_positive_normals {n : ℕ} [NeZero n]
    {x y : Point n} (hx : 0 < x.2.val.2) (hy : 0 < y.2.val.2)
    (h : radial x = radial y) : x = y := by
  classical
  obtain ⟨hrx, hfx0, hfx1, hax⟩ := positive_angle_bounds x hx
  obtain ⟨hry, hfy0, hfy1, hay⟩ := positive_angle_bounds y hy
  have hr : radius x = radius y := by
    simpa only [radial_norm] using congrArg (fun z : ℂ => ‖z‖) h
  have hcircle : circleMap (0 : ℂ) (radius x) (angle x) =
      circleMap (0 : ℂ) (radius x) (angle y) := by
    simpa only [radial, if_neg hrx.ne', if_neg hry.ne', ← hr] using h
  have hangle : angle x = angle y :=
    (injOn_circleMap_of_abs_sub_le' (c := (0 : ℂ)) (R := radius x)
      (a := 0) (b := 2 * Real.pi) hrx.ne' (by simp)) hax hay hcircle
  have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  have hc : 2 * Real.pi / (n : ℝ) ≠ 0 :=
    (div_pos (by positivity) hn).ne'
  have hcoord : (x.1.val : ℝ) + x.2.val.1 / radius x =
      (y.1.val : ℝ) + y.2.val.1 / radius y := mul_left_cancel₀ hc hangle
  have hij : x.1.val = y.1.val := by
    rcases lt_trichotomy x.1.val y.1.val with hlt | heq | hgt
    · have hle : (x.1.val : ℝ) + 1 ≤ (y.1.val : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hlt)
      exfalso
      linarith
    · exact heq
    · have hle : (y.1.val : ℝ) + 1 ≤ (x.1.val : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hgt)
      exfalso
      linarith
  have hf : x.2.val.1 / radius x = y.2.val.1 / radius y := by
    rw [hij] at hcoord
    exact add_left_cancel hcoord
  rw [← hr] at hf
  have ha : x.2.val.1 = y.2.val.1 := by
    simpa [hrx.ne'] using congrArg (fun t : ℝ => t * radius x) hf
  have hb : x.2.val.2 = y.2.val.2 := by
    dsimp only [radius] at hr
    linarith
  exact Prod.ext (Fin.ext hij) (Subtype.ext (Prod.ext ha hb))

/-- The radial map's fibers are exactly the original generated seam classes. -/
theorem radial_eq_iff_related {n : ℕ} [NeZero n] (x y : Point n) :
    radial x = radial y ↔ Related x y := by
  classical
  constructor
  · intro h
    have hr : radius x = radius y := by
      simpa only [radial_norm] using congrArg (fun z : ℂ => ‖z‖) h
    apply (related_iff_normal_eq x y).mpr
    by_cases hx0 : radius x = 0
    · have hy0 : radius y = 0 := hr.symm.trans hx0
      rw [(normal_none x).mpr hx0, (normal_none y).mpr hy0]
    · have hy0 : radius y ≠ 0 := by rwa [← hr]
      cases hnx : normal x with
      | none => exact False.elim (hx0 ((normal_none x).mp hnx))
      | some u =>
        cases hny : normal y with
        | none => exact False.elim (hy0 ((normal_none y).mp hny))
        | some v =>
          have hxu := radial_eq_of_related (related_to_normal hnx)
          have hyv := radial_eq_of_related (related_to_normal hny)
          have huv : u = v := radial_injective_on_positive_normals
            (normal_positive hnx) (normal_positive hny) (hxu.symm.trans (h.trans hyv))
          simp only [huv]
  · exact radial_eq_of_related

private theorem continuous_radius {n : ℕ} : Continuous (@radius n) := by
  unfold radius
  fun_prop

private theorem continuous_radial {n : ℕ} [NeZero n] : Continuous (@radial n _) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : radius x = 0
  · have hzero : radial x = 0 := by simp [radial, hx]
    rw [ContinuousAt, hzero, tendsto_zero_iff_norm_tendsto_zero]
    simpa only [radial_norm, hx] using (@continuous_radius n).tendsto x
  · have ha : ContinuousAt (fun y : Point n => angle y) x := by
      have hi : Continuous (fun y : Point n => (y.1.val : ℝ)) :=
        (continuous_of_discreteTopology : Continuous (fun i : Fin n => (i.val : ℝ))).comp
          continuous_fst
      have hfirst : Continuous (fun y : Point n => y.2.val.1) := by fun_prop
      exact continuousAt_const.mul
        (hi.continuousAt.add (hfirst.continuousAt.div continuous_radius.continuousAt hx))
    have hexp : ContinuousAt
        (fun y : Point n => circleMap 0 (radius y) (angle y)) x := by
      unfold circleMap
      exact continuousAt_const.add
        ((Complex.continuous_ofReal.continuousAt.comp continuous_radius.continuousAt).mul
          ((Complex.continuous_ofReal.continuousAt.comp ha).mul continuousAt_const).cexp)
    apply hexp.congr_of_eventuallyEq
    filter_upwards [(continuous_radius.continuousAt.ne_iff_eventually_ne
      continuousAt_const).mp hx] with y hy
    simp only [radial, if_neg hy]

private theorem compact_triangle : IsCompact
    {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} := by
  have hclosed : IsClosed {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  apply (isCompact_Icc.prod isCompact_Icc :
    IsCompact ((Set.Icc (0 : ℝ) 1) ×ˢ (Set.Icc (0 : ℝ) 1))).of_isClosed_subset hclosed
  rintro p ⟨ha, hb, hab⟩
  exact ⟨⟨ha, by linarith⟩, ⟨hb, by linarith⟩⟩

private instance : CompactSpace Triangle := isCompact_iff_compactSpace.mp compact_triangle

abbrev Disk := {z : ℂ // ‖z‖ ≤ 1}

def diskRadial {n : ℕ} [NeZero n] (x : Point n) : Disk :=
  ⟨radial x, by rw [radial_norm]; exact x.2.property.2.2⟩

theorem positive_circle_angle {z : ℂ} :
    ∃ θ ∈ Set.Ico (0 : ℝ) (2 * Real.pi), circleMap 0 ‖z‖ θ = z := by
  have hz : z ∈ Metric.sphere (0 : ℂ) |‖z‖| := by simp
  rw [← image_circleMap_Ioc (0 : ℂ) ‖z‖] at hz
  obtain ⟨θ, hθ, heq⟩ := hz
  by_cases ht : θ = 2 * Real.pi
  · refine ⟨0, ⟨le_rfl, Real.two_pi_pos⟩, ?_⟩
    have hp := periodic_circleMap (0 : ℂ) ‖z‖ 0
    simp only [zero_add] at hp
    exact hp.symm.trans (ht ▸ heq)
  · exact ⟨θ, ⟨hθ.1.le, lt_of_le_of_ne hθ.2 ht⟩, heq⟩

private theorem diskRadial_surjective {n : ℕ} [NeZero n] :
    Function.Surjective (@diskRadial n _) := by
  classical
  intro z
  by_cases hz : z.val = 0
  · refine ⟨apex (0 : Fin n), Subtype.ext ?_⟩
    simp [diskRadial, radial, radius, apex, hz]
  · have hr : 0 < ‖z.val‖ := norm_pos_iff.mpr hz
    have hn : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
    have hp : 0 < 2 * Real.pi := Real.two_pi_pos
    obtain ⟨θ, hθ, hcircle⟩ := positive_circle_angle (z := z.val)
    let t : ℝ := (n : ℝ) * θ / (2 * Real.pi)
    have ht0 : 0 ≤ t := div_nonneg (mul_nonneg hn.le hθ.1) hp.le
    have htn : t < (n : ℝ) := by
      apply (div_lt_iff₀ hp).mpr
      exact mul_lt_mul_of_pos_left hθ.2 hn
    let i : Fin n := ⟨Nat.floor t, (Nat.floor_lt ht0).mpr htn⟩
    let f : ℝ := t - (i.val : ℝ)
    have hf0 : 0 ≤ f := sub_nonneg.mpr (Nat.floor_le ht0)
    have hf1 : f < 1 := by
      have hh := Nat.lt_floor_add_one t
      dsimp [f, i]
      linarith
    let p : Triangle := ⟨(‖z.val‖ * f, ‖z.val‖ * (1 - f)),
      mul_nonneg hr.le hf0, mul_nonneg hr.le (by linarith), by
        nlinarith [z.property]⟩
    let x : Point n := (i, p)
    have hrad : radius x = ‖z.val‖ := by dsimp [radius, x, p]; ring
    have hangle : angle x = θ := by
      dsimp only [angle]
      rw [hrad]
      change (2 * Real.pi / (n : ℝ)) *
        ((i.val : ℝ) + (‖z.val‖ * f) / ‖z.val‖) = θ
      rw [mul_div_cancel_left₀ f hr.ne']
      dsimp only [f, t]
      field_simp [hn.ne', hp.ne']; ring
    have hrad0 : radius x ≠ 0 := by rw [hrad]; exact hr.ne'
    refine ⟨x, Subtype.ext ?_⟩
    change radial x = z.val
    rw [radial, if_neg hrad0, hrad, hangle]
    exact hcircle

def seamSetoid (n : ℕ) [NeZero n] : Setoid (Point n) := Relation.EqvGen.setoid seam

abbrev Fan (n : ℕ) [NeZero n] := Quotient (seamSetoid n)

def quotientRadial {n : ℕ} [NeZero n] : Fan n → Disk :=
  Quotient.lift diskRadial (fun _ _ h => Subtype.ext (radial_eq_of_related h))

/-- The quotient topology comes solely from the actual cyclic seams. -/
theorem quotientRadial_isHomeomorph {n : ℕ} [NeZero n] :
    IsHomeomorph (@quotientRadial n _) := by
  apply isHomeomorph_iff_continuous_bijective.mpr
  constructor
  · exact (continuous_radial.subtype_mk _).quotient_lift _
  · constructor
    · unfold quotientRadial
      apply (Setoid.lift_injective_iff_ker_eq_of_le _).2
      ext x y
      change diskRadial x = diskRadial y ↔ Related x y
      rw [Subtype.ext_iff]
      exact radial_eq_iff_related x y
    · intro z
      obtain ⟨x, hx⟩ := diskRadial_surjective (n := n) z
      exact ⟨Quotient.mk (seamSetoid n) x, hx⟩

/-- The closed disk coordinate of a seam class is the prescribed radial expression. -/
def homeomorphism {n : ℕ} [NeZero n] : Fan n ≃ₜ Disk :=
  quotientRadial_isHomeomorph.homeomorph quotientRadial

end

end D5.S3.Geometry.Gluing.CyclicTriangleDisk
