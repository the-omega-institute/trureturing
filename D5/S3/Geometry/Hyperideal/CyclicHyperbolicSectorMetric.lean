/- GID: D5/S3/Geometry/Hyperideal/CyclicHyperbolicSectorMetric
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/CyclicHyperbolicSectorMetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Group.AddCircle, mathlib/module/Mathlib.Analysis.Complex.Isometry]
   utility: none
   digest: Original finite chains attain the capped angular metric in numbered actual hyperbolic sectors. -/

import D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
import D5.S3.Geometry.HyperbolicSupportBoundary
import D5.S3.Topology.FiniteOrbitChainMetric
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

import D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorSupport

noncomputable section
open scoped BigOperators Matrix NNReal ENNReal
open Set
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace

namespace D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric

set_option autoImplicit false

def offset {n : ℕ} (alpha : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  ∑ k ∈ Finset.Iio i, alpha k

def totalAngle {n : ℕ} (alpha : Fin (n + 1) → ℝ) : ℝ :=
  ∑ k, alpha k

private def cyclicTag {n : ℕ} (i : Fin (n + 1)) (m : ℕ) : Fin (n + 1) :=
  (finRotate (n + 1))^[m] i

private def cyclicWidth {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, alpha (cyclicTag i k)

private def cyclicWrap {n : ℕ} (i : Fin (n + 1)) : ℕ → ℕ
  | 0 => 0
  | m + 1 => cyclicWrap i m + if cyclicTag i m = Fin.last n then 1 else 0

open Fin.NatCast in
private theorem cyclicTag_add {n : ℕ} (i : Fin (n + 1)) (m : ℕ) :
    cyclicTag i m = i + (m : Fin (n + 1)) := by
  induction m with
  | zero => simp [cyclicTag]
  | succ m ih =>
      simp only [cyclicTag, Function.iterate_succ_apply', finRotate_apply]
      change cyclicTag i m + 1 = _
      rw [ih, Nat.cast_add, Nat.cast_one, add_assoc]

private theorem cyclicTag_difference {n : ℕ} (i j : Fin (n + 1)) :
    cyclicTag i (j - i).val = j := by
  rw [cyclicTag_add]
  simp

private theorem cyclicTag_period {n : ℕ} (i : Fin (n + 1)) :
    cyclicTag i (n + 1) = i := by
  rw [cyclicTag_add, Fin.natCast_self, add_zero]

private theorem cyclic_offset_real {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    offset alpha i + alpha i = offset alpha (finRotate (n + 1) i) +
      (if i = Fin.last n then totalAngle alpha else 0) := by
  classical
  have hsum : offset alpha i + alpha i = ∑ k ∈ Finset.Iic i, alpha k := by
    rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
    exact add_comm _ _
  have hz : offset alpha 0 = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have h : k < (0 : Fin (n + 1)) := Finset.mem_Iio.mp hk
    exact False.elim (not_lt_of_ge (Fin.zero_le k) h)
  by_cases hi : i = Fin.last n
  · subst i
    have ht : Finset.Iic (Fin.last n) = (Finset.univ : Finset (Fin (n + 1))) := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
      exact Fin.le_last k
    rw [if_pos rfl, finRotate_last, hz, zero_add, hsum, ht]
    rfl
  · have hn := coe_finRotate_of_ne_last hi
    have hs : Finset.Iio (finRotate (n + 1) i) = Finset.Iic i := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_def]
      omega
    rw [if_neg hi, add_zero, hsum]
    simp only [offset, hs]

private theorem cyclicWidth_lift {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (m : ℕ) :
    cyclicWidth alpha i m = offset alpha (cyclicTag i m) - offset alpha i +
      (cyclicWrap i m : ℝ) * totalAngle alpha := by
  classical
  induction m with
  | zero => simp [cyclicWidth, cyclicWrap, cyclicTag]
  | succ m ih =>
      have hs := cyclic_offset_real alpha (cyclicTag i m)
      have ht : cyclicTag i (m + 1) = finRotate (n + 1) (cyclicTag i m) := by
        simp only [cyclicTag, Function.iterate_succ_apply']
      rw [cyclicWidth, Finset.sum_range_succ]
      change cyclicWidth alpha i m + alpha (cyclicTag i m) = _
      rw [ih, cyclicWrap, Nat.cast_add, ht]
      split_ifs at hs ⊢ <;> simp only [Nat.cast_one, Nat.cast_zero] <;> linarith

private theorem cyclicWrap_position {n : ℕ} (i : Fin (n + 1)) (m : ℕ) :
    (cyclicTag i m).val + (n + 1) * cyclicWrap i m = i.val + m := by
  classical
  induction m with
  | zero => simp [cyclicTag, cyclicWrap]
  | succ m ih =>
      have ht : cyclicTag i (m + 1) = finRotate (n + 1) (cyclicTag i m) := by
        simp only [cyclicTag, Function.iterate_succ_apply']
      rw [ht, cyclicWrap, coe_finRotate]
      split_ifs with h
      · have hv : (cyclicTag i m).val = n := congrArg Fin.val h
        simp only [Nat.mul_add, Nat.mul_one] at *
        omega
      · simp only [Nat.add_zero] at *
        omega

private theorem cyclicWidth_difference {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) :
    cyclicWidth alpha i (j - i).val = offset alpha j - offset alpha i +
      (if i ≤ j then 0 else totalAngle alpha) := by
  classical
  have hp := cyclicWrap_position i (j - i).val
  rw [cyclicTag_difference] at hp
  have hd := Fin.intCast_val_sub_eq_sub_add_ite j i
  have hn : 0 < n + 1 := Nat.succ_pos n
  have hw : cyclicWrap i (j - i).val = if i ≤ j then 0 else 1 := by
    split_ifs at hd ⊢ with h
    · apply Nat.eq_of_mul_eq_mul_left hn
      omega
    · apply Nat.eq_of_mul_eq_mul_left hn
      omega
  rw [cyclicWidth_lift, cyclicTag_difference, hw]
  split_ifs <;> simp

private theorem cyclicWidth_period {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : cyclicWidth alpha i (n + 1) = totalAngle alpha := by
  have hp := cyclicWrap_position i (n + 1)
  rw [cyclicTag_period] at hp
  have hw : cyclicWrap i (n + 1) = 1 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n)
    simpa only [Nat.mul_one] using Nat.add_left_cancel hp
  rw [cyclicWidth_lift, cyclicTag_period, hw]
  simp

private theorem offset_end_le {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (i : Fin (n + 1)) :
    offset alpha i + alpha i ≤ totalAngle alpha := by
  classical
  have hs : offset alpha i + alpha i = ∑ k ∈ Finset.Iic i, alpha k := by
    rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
    exact add_comm _ _
  rw [hs]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun k _ _ => (ha k).le)

private theorem offset_end_le_offset {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) {i j : Fin (n + 1)} (hij : i < j) :
    offset alpha i + alpha i ≤ offset alpha j := by
  classical
  have hs : offset alpha i + alpha i = ∑ k ∈ Finset.Iic i, alpha k := by
    rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
    exact add_comm _ _
  rw [hs]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    exact Finset.mem_Iio.mpr ((Finset.mem_Iic.mp hk).trans_lt hij)
  · intro k _ _
    exact (ha k).le

private def forwardSteps {n : ℕ} (i j : Fin (n + 1)) (tp tq : ℝ) : ℕ :=
  if i = j ∧ tq < tp then n + 1 else (j - i).val

private def forwardSpan {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) (tp tq : ℝ) : ℝ :=
  cyclicWidth alpha i (forwardSteps i j tp tq) + tq - tp

private theorem forwardSteps_tag {n : ℕ} (i j : Fin (n + 1)) (tp tq : ℝ) :
    cyclicTag i (forwardSteps i j tp tq) = j := by
  classical
  unfold forwardSteps
  split_ifs with h
  · rw [cyclicTag_period, h.1]
  · exact cyclicTag_difference i j

private theorem forwardSpan_nonneg {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (i j : Fin (n + 1)) (tp tq : ℝ)
    (hp : tp ∈ Icc 0 (alpha i)) (hq : tq ∈ Icc 0 (alpha j)) :
    0 ≤ forwardSpan alpha i j tp tq := by
  classical
  unfold forwardSpan forwardSteps
  split_ifs with h
  · rw [cyclicWidth_period]
    have hb : alpha i ≤ totalAngle alpha :=
      (le_add_of_nonneg_left (Finset.sum_nonneg fun k _ => (ha k).le)).trans
        (offset_end_le alpha ha i)
    linarith [hp.2, hq.1]
  · rw [cyclicWidth_difference]
    by_cases hij : i = j
    · subst j
      simp only [le_refl, if_true, sub_self, zero_add]
      have ht : tp ≤ tq := le_of_not_gt (fun hlt => h ⟨rfl, hlt⟩)
      linarith
    · by_cases hle : i ≤ j
      · rw [if_pos hle]
        have he := offset_end_le_offset alpha ha (lt_of_le_of_ne hle hij)
        linarith [hp.2, hq.1]
      · rw [if_neg hle]
        have he := offset_end_le alpha ha i
        have ho : 0 ≤ offset alpha j := Finset.sum_nonneg (fun k _ => (ha k).le)
        linarith [hp.2, hq.1]

private theorem forwardSpan_pair {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) (tp tq : ℝ) :
    (i = j ∧ tp = tq ∧ forwardSpan alpha i j tp tq = 0 ∧
      forwardSpan alpha j i tq tp = 0) ∨
    forwardSpan alpha i j tp tq + forwardSpan alpha j i tq tp = totalAngle alpha := by
  classical
  by_cases hij : i = j
  · subst j
    by_cases ht : tp = tq
    · subst tq
      left
      simp [forwardSpan, forwardSteps, cyclicWidth]
    · right
      rcases lt_or_gt_of_ne ht with hlt | hgt
      · simp only [forwardSpan, forwardSteps, true_and, not_lt_of_ge hlt.le,
          if_false, if_true, hlt, sub_self, Fin.val_zero]
        rw [cyclicWidth_period]
        simp [cyclicWidth]
      · simp only [forwardSpan, forwardSteps, true_and, not_lt_of_ge hgt.le,
          if_false, if_true, hgt, sub_self, Fin.val_zero]
        rw [cyclicWidth_period]
        simp [cyclicWidth]
  · right
    have hji : j ≠ i := Ne.symm hij
    simp only [forwardSpan, forwardSteps, hij, hji, false_and, if_false,
      cyclicWidth_difference]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · rw [if_pos hlt.le, if_neg (not_le.mpr hlt)]
      ring
    · rw [if_neg (not_le.mpr hgt), if_pos hgt.le]
      ring

private theorem forwardSpan_class {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) (tp tq : ℝ) :
    ((forwardSpan alpha i j tp tq : ℝ) : AddCircle (totalAngle alpha)) =
      ((offset alpha j + tq - (offset alpha i + tp) : ℝ) : AddCircle (totalAngle alpha)) := by
  classical
  unfold forwardSpan forwardSteps
  split_ifs with h
  · rw [cyclicWidth_period, h.1]
    simp only [AddCircle.coe_sub, AddCircle.coe_add, AddCircle.coe_period, zero_add]
    abel
  · rw [cyclicWidth_difference]
    split_ifs <;> simp only [AddCircle.coe_sub, AddCircle.coe_add,
      AddCircle.coe_period, AddCircle.coe_zero] <;> abel

private theorem shorterSpan_norm {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (i j : Fin (n + 1)) (tp tq : ℝ)
    (hp : tp ∈ Icc 0 (alpha i)) (hq : tq ∈ Icc 0 (alpha j)) :
    min (forwardSpan alpha i j tp tq) (forwardSpan alpha j i tq tp) =
      ‖((offset alpha j + tq - (offset alpha i + tp) : ℝ) : AddCircle (totalAngle alpha))‖ := by
  classical
  have hA : 0 < totalAngle alpha := Finset.sum_pos (fun k _ => ha k) Finset.univ_nonempty
  have hf := forwardSpan_nonneg alpha ha i j tp tq hp hq
  have hb := forwardSpan_nonneg alpha ha j i tq tp hq hp
  have hclass := forwardSpan_class alpha i j tp tq
  have hback : ((forwardSpan alpha j i tq tp : ℝ) : AddCircle (totalAngle alpha)) =
      -((offset alpha j + tq - (offset alpha i + tp) : ℝ) : AddCircle (totalAngle alpha)) := by
    rw [forwardSpan_class]
    simp only [AddCircle.coe_sub, AddCircle.coe_add]
    abel
  rcases forwardSpan_pair alpha i j tp tq with hzero | hsum
  · rw [hzero.2.2.1, hzero.2.2.2, min_self]
    rw [hzero.2.2.1] at hclass
    simpa only [AddCircle.coe_zero, norm_zero] using congrArg norm hclass
  · by_cases hle : forwardSpan alpha i j tp tq ≤ forwardSpan alpha j i tq tp
    · rw [min_eq_left hle, ← hclass]
      have hhalf : |forwardSpan alpha i j tp tq| ≤ |totalAngle alpha| / 2 := by
        rw [abs_of_nonneg hf, abs_of_pos hA]
        linarith
      rw [(AddCircle.norm_coe_eq_abs_iff (totalAngle alpha) hA.ne').mpr hhalf,
        abs_of_nonneg hf]
    · rw [min_eq_right (le_of_not_ge hle), ← norm_neg
        (((offset alpha j + tq - (offset alpha i + tp) : ℝ) : AddCircle (totalAngle alpha))),
        ← hback]
      have hhalf : |forwardSpan alpha j i tq tp| ≤ |totalAngle alpha| / 2 := by
        rw [abs_of_nonneg hb, abs_of_pos hA]
        linarith
      rw [(AddCircle.norm_coe_eq_abs_iff (totalAngle alpha) hA.ne').mpr hhalf,
        abs_of_nonneg hb]

private theorem cyclic_offset {n : ℕ} (alpha : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    ((offset alpha i + alpha i : ℝ) : AddCircle (totalAngle alpha)) =
      (offset alpha (finRotate (n + 1) i) : AddCircle (totalAngle alpha)) := by
  classical
  have hsum : offset alpha i + alpha i = ∑ k ∈ Finset.Iic i, alpha k := by
    rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self]
    exact add_comm _ _
  rw [hsum]
  by_cases hi : i = Fin.last n
  · subst i
    have htop : Finset.Iic (Fin.last n) = (Finset.univ : Finset (Fin (n + 1))) := by
      ext k
      simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
      exact Fin.le_last k
    rw [finRotate_last, htop]
    change ((totalAngle alpha : ℝ) : AddCircle (totalAngle alpha)) =
      (offset alpha 0 : AddCircle (totalAngle alpha))
    have hzero : offset alpha 0 = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hk' : k < (0 : Fin (n + 1)) := Finset.mem_Iio.mp hk
      exact False.elim (not_lt_of_ge (Fin.zero_le k) hk')
    rw [hzero, AddCircle.coe_zero, AddCircle.coe_period]
  · have hnext := coe_finRotate_of_ne_last hi
    have hsets : Finset.Iio (finRotate (n + 1) i) = Finset.Iic i := by
      ext k
      simp only [Finset.mem_Iio, Finset.mem_Iic, Fin.lt_def, Fin.le_def]
      omega
    simp only [offset, hsets]

def cyclicDatum {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi) :
    D5.S3.Topology.FiniteOrbitChainMetric.Datum (Fin (n + 1)) (Fin (n + 1))
      (fun i => sector (alpha i)) :=
  sectorDatum (finRotate (n + 1)) alpha ha hapi

def comparisonLength {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (p q : Sigma (fun i => sector (alpha i))) : ℝ :=
  dist (cylindricalPoint (radialCoordinate p.2.val) (axialCoordinate p.2.val) 0)
    (cylindricalPoint (radialCoordinate q.2.val) (axialCoordinate q.2.val)
      (min Real.pi ‖((offset alpha q.1 + angularCoordinate q.2.val -
        (offset alpha p.1 + angularCoordinate p.2.val) : ℝ) : AddCircle (totalAngle alpha))‖))

private theorem turn_axis (theta z : ℝ) :
    turn theta (cylindricalPoint 0 z 0) = cylindricalPoint 0 z 0 := by
  apply lift_injective
  rw [turn_lift, cylindrical_lift]
  ext k
  fin_cases k <;> simp [cylinderLift]

private theorem axis_mem_sector (alpha z : ℝ) :
    cylindricalPoint 0 z 0 ∈ sector alpha := by
  simp [sector, cylindrical_lift, cylinderLift]

private def axisPoint (alpha z : ℝ) : sector alpha :=
  ⟨cylindricalPoint 0 z 0, axis_mem_sector alpha z⟩

private theorem axis_walk {I : Type*} (next : I → I) (alpha : I → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (i : I) (m : ℕ) (z : ℝ) :
    (sectorDatum next alpha ha hapi).Chain
      (⟨i, axisPoint (alpha i) z⟩ : Sigma (fun i => sector (alpha i)))
      ⟨next^[m] i, axisPoint (alpha (next^[m] i)) z⟩ 0 := by
  let G := sectorDatum next alpha ha hapi
  induction m with
  | zero => exact (D5.S3.Topology.FiniteOrbitChainMetric.Datum.Chain.nil (G := G))
  | succ m ih =>
      let j := next^[m] i
      let x : G.dom j := ⟨axisPoint (alpha j) z, by
        change Real.cos (alpha j) * lift (cylindricalPoint 0 z 0) 1 -
          Real.sin (alpha j) * lift (cylindricalPoint 0 z 0) 0 = 0
        simp [cylindrical_lift, cylinderLift]⟩
      have hx : (G.iso j x).val = axisPoint (alpha (next j)) z := by
        apply Subtype.ext
        exact turn_axis (-alpha j) z
      have h := D5.S3.Topology.FiniteOrbitChainMetric.Datum.Chain.forward (G := G) j x ih
      rw [hx] at h
      change G.Chain ⟨i, axisPoint (alpha i) z⟩
        ⟨next^[m + 1] i, axisPoint (alpha (next^[m + 1] i)) z⟩ 0
      rw [Function.iterate_succ_apply']
      exact h

private theorem axis_change_tag {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (i j : Fin (n + 1)) (z : ℝ) :
    (cyclicDatum alpha ha hapi).Chain
      (⟨i, axisPoint (alpha i) z⟩ : Sigma (fun i => sector (alpha i)))
      ⟨j, axisPoint (alpha j) z⟩ 0 := by
  have h := axis_walk (finRotate (n + 1)) alpha ha hapi i (j - i).val z
  change (cyclicDatum alpha ha hapi).Chain _
    ⟨cyclicTag i (j - i).val, axisPoint (alpha (cyclicTag i (j - i).val)) z⟩ 0 at h
  rw [cyclicTag_difference] at h
  exact h

private theorem chain_via_axis {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (p q : Sigma (fun i => sector (alpha i))) (z : ℝ) :
    (cyclicDatum alpha ha hapi).Chain p q
      (ENNReal.ofReal (dist p.2.val (cylindricalPoint 0 z 0) +
        dist (cylindricalPoint 0 z 0) q.2.val)) := by
  let G := cyclicDatum alpha ha hapi
  have hfirst : G.Chain p ⟨p.1, axisPoint (alpha p.1) z⟩
      (edist p.2 (axisPoint (alpha p.1) z)) := by
    simpa only [zero_add] using D5.S3.Topology.FiniteOrbitChainMetric.Datum.Chain.move (G := G) (a := p) p.2 (axisPoint (alpha p.1) z) (D5.S3.Topology.FiniteOrbitChainMetric.Datum.Chain.nil (G := G))
  have hmid := G.chain_append hfirst (axis_change_tag alpha ha hapi p.1 q.1 z)
  have h := D5.S3.Topology.FiniteOrbitChainMetric.Datum.Chain.move (G := G) (a := p) (axisPoint (alpha q.1) z) q.2 hmid
  simpa only [add_zero, edist_dist, Subtype.dist_eq, axisPoint,
    ENNReal.ofReal_add dist_nonneg dist_nonneg] using h

private theorem cylindrical_distance_of_cos {rho z theta sigma w phi beta gamma : ℝ}
    (hc : Real.cos (theta - phi) = Real.cos (beta - gamma)) :
    dist (cylindricalPoint rho z theta) (cylindricalPoint sigma w phi) =
      dist (cylindricalPoint rho z beta) (cylindricalPoint sigma w gamma) := by
  apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
  rw [cylindrical_cosh_distance, cylindrical_cosh_distance, hc]

private theorem cylindrical_axis_distance (rho z theta w : ℝ) :
    dist (cylindricalPoint rho z theta) (cylindricalPoint 0 w 0) =
      dist (cylindricalPoint rho z 0) (cylindricalPoint 0 w 0) := by
  apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
  simp only [cylindrical_cosh_distance, Real.cosh_zero, Real.sinh_zero, mul_zero,
    zero_mul, sub_zero]

private theorem opposite_axis_split (rho z sigma w : ℝ) (hr : 0 < rho) (hs : 0 < sigma) :
    ∃ a : ℝ,
      dist (cylindricalPoint rho z 0) (cylindricalPoint 0 a 0) +
        dist (cylindricalPoint 0 a 0) (cylindricalPoint sigma w Real.pi) =
      dist (cylindricalPoint rho z 0) (cylindricalPoint sigma w Real.pi) := by
  let p := cylindricalPoint rho z 0
  let q := cylindricalPoint sigma w Real.pi
  have hp : lift p 0 = Real.sinh rho := by simp [p, cylindrical_lift, cylinderLift]
  have hq : lift q 0 = -Real.sinh sigma := by simp [q, cylindrical_lift, cylinderLift]
  have hpy : lift p 1 = 0 := by simp [p, cylindrical_lift, cylinderLift]
  have hqy : lift q 1 = 0 := by simp [q, cylindrical_lift, cylinderLift]
  have hpq : p ≠ q := by
    intro h
    have hx := congrArg (fun r => lift r 0) h
    rw [hp, hq] at hx
    linarith [Real.sinh_pos_iff.mpr hr, Real.sinh_pos_iff.mpr hs]
  obtain ⟨gamma, hiso, h0, h1, hg, hbetween⟩ := hyperbolic_segment p q hpq
  let t0 : Icc (0 : ℝ) (dist p q) := ⟨0, ⟨le_rfl, dist_nonneg⟩⟩
  let t1 : Icc (0 : ℝ) (dist p q) := ⟨dist p q, ⟨dist_nonneg, le_rfl⟩⟩
  have hc : Continuous (fun t => lift (gamma t) 0) :=
    (continuous_apply 0).comp
      (D5.S3.Geometry.HyperbolicSupportBoundary.lift_continuous.comp hiso.continuous)
  have hx0 : lift (gamma t1) 0 ≤ 0 := by
    rw [h1, hq]
    exact neg_nonpos.mpr (Real.sinh_pos_iff.mpr hs).le
  have hx1 : 0 ≤ lift (gamma t0) 0 := by
    rw [h0, hp]
    exact (Real.sinh_pos_iff.mpr hr).le
  letI : PreconnectedSpace (Icc (0 : ℝ) (dist p q)) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  obtain ⟨t, ht⟩ := intermediate_value_univ t1 t0 hc ⟨hx0, hx1⟩
  have hy : lift (gamma t) 1 = 0 := by
    rw [hg]
    simp [interpolate, hpy, hqy]
  have hv : transverse (gamma t) = 0 := by
    apply Complex.ext <;> simp [transverse, ht, hy]
  have hr0 : radialCoordinate (gamma t) = 0 := by simp [radialCoordinate, hv]
  have he : gamma t = cylindricalPoint 0 (axialCoordinate (gamma t)) 0 := by
    have h := cylindrical_reconstruct (gamma t)
    rw [hr0, cylindrical_axis] at h
    exact h.symm
  refine ⟨axialCoordinate (gamma t), ?_⟩
  have hb : dist p (gamma t) + dist (gamma t) q = dist p q :=
    (show gamma t ∈ {r | dist p r + dist r q = dist p q} from
      hbetween ▸ Set.mem_range_self t)
  rw [← he]
  exact hb

private theorem opposite_attaining_chain {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (p q : Sigma (fun i => sector (alpha i)))
    (hp : 0 < radialCoordinate p.2.val) (hq : 0 < radialCoordinate q.2.val) :
    (cyclicDatum alpha ha hapi).Chain p q
      (ENNReal.ofReal (dist
        (cylindricalPoint (radialCoordinate p.2.val) (axialCoordinate p.2.val) 0)
        (cylindricalPoint (radialCoordinate q.2.val) (axialCoordinate q.2.val) Real.pi))) := by
  obtain ⟨a, hsplit⟩ := opposite_axis_split
    (radialCoordinate p.2.val) (axialCoordinate p.2.val)
    (radialCoordinate q.2.val) (axialCoordinate q.2.val) hp hq
  have h := chain_via_axis alpha ha hapi p q a
  have hd : dist p.2.val (cylindricalPoint 0 a 0) +
      dist (cylindricalPoint 0 a 0) q.2.val =
      dist (cylindricalPoint (radialCoordinate p.2.val) (axialCoordinate p.2.val) 0)
        (cylindricalPoint (radialCoordinate q.2.val) (axialCoordinate q.2.val) Real.pi) := by
    conv_lhs =>
      arg 1
      rw [← cylindrical_reconstruct p.2.val, cylindrical_axis_distance]
    conv_lhs =>
      arg 2
      rw [dist_comm, ← cylindrical_reconstruct q.2.val, cylindrical_axis_distance, dist_comm]
    have hdq : dist (cylindricalPoint 0 a 0)
        (cylindricalPoint (radialCoordinate q.2.val) (axialCoordinate q.2.val) Real.pi) =
        dist (cylindricalPoint 0 a 0)
          (cylindricalPoint (radialCoordinate q.2.val) (axialCoordinate q.2.val) 0) := by
      rw [dist_comm, cylindrical_axis_distance, dist_comm]
    rw [hdq] at hsplit
    exact hsplit
  simpa only [hd] using h

private theorem comparisonLength_symm {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (p q : Sigma (fun i => sector (alpha i))) :
    comparisonLength alpha p q = comparisonLength alpha q p := by
  have hd : ((offset alpha p.1 + angularCoordinate p.2.val -
      (offset alpha q.1 + angularCoordinate q.2.val) : ℝ) : AddCircle (totalAngle alpha)) =
      -((offset alpha q.1 + angularCoordinate q.2.val -
        (offset alpha p.1 + angularCoordinate p.2.val) : ℝ) : AddCircle (totalAngle alpha)) := by
    simp only [AddCircle.coe_sub, AddCircle.coe_add]
    abel
  unfold comparisonLength
  rw [hd, norm_neg]
  apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
  rw [cylindrical_cosh_distance, cylindrical_cosh_distance]
  have hz : Real.cosh (axialCoordinate p.2.val - axialCoordinate q.2.val) =
      Real.cosh (axialCoordinate q.2.val - axialCoordinate p.2.val) := by
    rw [← Real.cosh_neg, neg_sub]
  rw [hz]
  ring

private theorem axis_endpoint_attaining {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (p q : Sigma (fun i => sector (alpha i))) (hp : radialCoordinate p.2.val = 0) :
    (cyclicDatum alpha ha hapi).Chain p q (ENNReal.ofReal (comparisonLength alpha p q)) := by
  have hpaxis : p.2.val = cylindricalPoint 0 (axialCoordinate p.2.val) 0 := by
    have h := cylindrical_reconstruct p.2.val
    rw [hp, cylindrical_axis] at h
    exact h.symm
  have h := chain_via_axis alpha ha hapi p q (axialCoordinate p.2.val)
  have hd : dist p.2.val (cylindricalPoint 0 (axialCoordinate p.2.val) 0) +
      dist (cylindricalPoint 0 (axialCoordinate p.2.val) 0) q.2.val =
      comparisonLength alpha p q := by
    have h0 : dist p.2.val (cylindricalPoint 0 (axialCoordinate p.2.val) 0) = 0 :=
      dist_eq_zero.mpr hpaxis
    rw [h0, zero_add]
    conv_lhs =>
      arg 2
      rw [← cylindrical_reconstruct q.2.val]
    unfold comparisonLength
    rw [hp]
    apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
    rw [cylindrical_cosh_distance, cylindrical_cosh_distance]
    simp only [Real.sinh_zero, zero_mul, sub_zero]
  simpa only [hd] using h

/-- The capped scalar angular separation gives a lower bound for the literal
original cost infimum on numbered actual hyperbolic sectors. -/
private theorem comparison_lower {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (p q : Sigma (fun i => sector (alpha i))) :
    ENNReal.ofReal (comparisonLength alpha p q) ≤ (cyclicDatum alpha ha hapi).distance p q := by
  have h := fold_distance_lower (finRotate (n + 1)) alpha ha hapi (totalAngle alpha)
    (offset alpha p.1 + angularCoordinate p.2.val) (offset alpha) (cyclic_offset alpha) p q
  simpa only [fold, foldedAngle, sub_self, AddCircle.coe_zero, norm_zero,
    min_eq_right Real.pi_pos.le, edist_dist, comparisonLength, cyclicDatum] using h

private theorem short_forward_attaining {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (p q : Sigma (fun i => sector (alpha i)))
    (hp : 0 < radialCoordinate p.2.val) (hq : 0 < radialCoordinate q.2.val)
    (hle : forwardSpan alpha p.1 q.1 (angularCoordinate p.2.val) (angularCoordinate q.2.val) ≤
      forwardSpan alpha q.1 p.1 (angularCoordinate q.2.val) (angularCoordinate p.2.val))
    (hshort : forwardSpan alpha p.1 q.1 (angularCoordinate p.2.val)
      (angularCoordinate q.2.val) < Real.pi) :
    (cyclicDatum alpha ha hapi).Chain p q (ENNReal.ofReal (comparisonLength alpha p q)) := by
  let m := forwardSteps p.1 q.1 (angularCoordinate p.2.val) (angularCoordinate q.2.val)
  have htag := forwardSteps_tag p.1 q.1 (angularCoordinate p.2.val) (angularCoordinate q.2.val)
  have hwp : runWidth (finRotate (n + 1)) alpha p.1 m = cyclicWidth alpha p.1 m := rfl
  have hqangle : angularCoordinate q.2.val ∈
      Icc 0 (alpha ((finRotate (n + 1))^[m] p.1)) := by
    change angularCoordinate q.2.val ∈ Icc 0 (alpha (cyclicTag p.1 m))
    rw [htag]
    exact sector_angle (alpha q.1) (ha q.1) q.2
  have h := short_angle_forward_run (finRotate (n + 1)) alpha ha hapi m p.1
    (radialCoordinate p.2.val) (axialCoordinate p.2.val) (angularCoordinate p.2.val)
    (radialCoordinate q.2.val) (axialCoordinate q.2.val) (angularCoordinate q.2.val)
    hp hq (sector_angle (alpha p.1) (ha p.1) p.2) hqangle
    (by simpa only [hwp, forwardSpan, m] using hshort)
  have hd : dist
      (cylindricalPoint (radialCoordinate p.2.val) (axialCoordinate p.2.val)
        (angularCoordinate p.2.val))
      (cylindricalPoint (radialCoordinate q.2.val) (axialCoordinate q.2.val)
        (runWidth (finRotate (n + 1)) alpha p.1 m + angularCoordinate q.2.val)) =
      comparisonLength alpha p q := by
    have hn := shorterSpan_norm alpha ha p.1 q.1
      (angularCoordinate p.2.val) (angularCoordinate q.2.val)
      (sector_angle (alpha p.1) (ha p.1) p.2) (sector_angle (alpha q.1) (ha q.1) q.2)
    rw [min_eq_left hle] at hn
    unfold comparisonLength
    rw [← hn, min_eq_right hshort.le]
    apply cylindrical_distance_of_cos
    rw [hwp]
    congr 1
    change angularCoordinate p.2.val -
      (cyclicWidth alpha p.1 m + angularCoordinate q.2.val) =
      0 - (cyclicWidth alpha p.1 m + angularCoordinate q.2.val - angularCoordinate p.2.val)
    ring
  rw [hd] at h
  -- Transport the whole tagged endpoint so its membership proof follows the tag.
  have hendpoint {i j : Fin (n + 1)}
      (x : sector (alpha i)) (y : sector (alpha j))
      (hij : i = j) (hxy : x.val = y.val) :
      (⟨i, x⟩ : Sigma (fun k => sector (alpha k))) = ⟨j, y⟩ := by
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext hxy)
  have htarget := hendpoint
    (⟨cylindricalPoint (radialCoordinate q.2.val) (axialCoordinate q.2.val)
        (angularCoordinate q.2.val),
      cylindrical_mem_sector _ _ _ _ hq.le (hapi _) hqangle⟩ :
        sector (alpha ((finRotate (n + 1))^[m] p.1)))
    q.2 htag (cylindrical_reconstruct q.2.val)
  rw [htarget] at h
  have hsource := hendpoint
    (⟨cylindricalPoint (radialCoordinate p.2.val) (axialCoordinate p.2.val)
        (angularCoordinate p.2.val),
      cylindrical_mem_sector _ _ _ _ hp.le (hapi _)
        (sector_angle (alpha p.1) (ha p.1) p.2)⟩ : sector (alpha p.1))
    p.2 rfl (cylindrical_reconstruct p.2.val)
  rw [hsource] at h
  simpa only [Sigma.eta, cyclicDatum] using h

/-- Every pair of actual numbered cyclic-sector representatives has an original
finite chain attaining the capped angular distance, which equals the original
cost infimum. -/
theorem cyclic_sector_metric {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (ha : ∀ i, 0 < alpha i) (hapi : ∀ i, alpha i < Real.pi)
    (p q : Sigma (fun i => sector (alpha i))) :
    (cyclicDatum alpha ha hapi).Chain p q (ENNReal.ofReal (comparisonLength alpha p q)) ∧
      (cyclicDatum alpha ha hapi).distance p q = ENNReal.ofReal (comparisonLength alpha p q) := by
  let G := cyclicDatum alpha ha hapi
  have hattain : G.Chain p q (ENNReal.ofReal (comparisonLength alpha p q)) := by
    have hrp : 0 ≤ radialCoordinate p.2.val :=
      Real.arsinh_nonneg_iff.mpr (norm_nonneg _)
    have hrq : 0 ≤ radialCoordinate q.2.val :=
      Real.arsinh_nonneg_iff.mpr (norm_nonneg _)
    rcases eq_or_lt_of_le hrp with hp | hp
    · exact axis_endpoint_attaining alpha ha hapi p q hp.symm
    rcases eq_or_lt_of_le hrq with hq | hq
    · have h := G.chain_reverse (axis_endpoint_attaining alpha ha hapi q p hq.symm)
      simpa only [comparisonLength_symm alpha q p] using h
    let f := forwardSpan alpha p.1 q.1 (angularCoordinate p.2.val) (angularCoordinate q.2.val)
    let b := forwardSpan alpha q.1 p.1 (angularCoordinate q.2.val) (angularCoordinate p.2.val)
    have hn : min f b = ‖((offset alpha q.1 + angularCoordinate q.2.val -
        (offset alpha p.1 + angularCoordinate p.2.val) : ℝ) : AddCircle (totalAngle alpha))‖ :=
      shorterSpan_norm alpha ha p.1 q.1 (angularCoordinate p.2.val) (angularCoordinate q.2.val)
        (sector_angle (alpha p.1) (ha p.1) p.2) (sector_angle (alpha q.1) (ha q.1) q.2)
    by_cases hcap : Real.pi ≤ min f b
    · have h := opposite_attaining_chain alpha ha hapi p q hp hq
      change G.Chain p q (ENNReal.ofReal (comparisonLength alpha p q))
      simpa only [comparisonLength, min_eq_left (hn ▸ hcap)] using h
    · have hmin : min f b < Real.pi := lt_of_not_ge hcap
      by_cases hle : f ≤ b
      · exact short_forward_attaining alpha ha hapi p q hp hq hle
          (by simpa only [min_eq_left hle] using hmin)
      · have hle' := le_of_not_ge hle
        have h := G.chain_reverse (short_forward_attaining alpha ha hapi q p hq hp hle'
          (by simpa only [min_eq_right hle'] using hmin))
        simpa only [comparisonLength_symm alpha q p] using h
  exact ⟨hattain, le_antisymm
    (iInf₂_le (ENNReal.ofReal (comparisonLength alpha p q)) hattain)
    (comparison_lower alpha ha hapi p q)⟩

end D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric
