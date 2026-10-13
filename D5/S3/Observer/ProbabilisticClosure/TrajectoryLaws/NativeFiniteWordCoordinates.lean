/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFiniteWordCoordinates
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFiniteWordCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Periodic curve parameters and installed finite stopped-word coordinates. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelCommonFlow
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePeriodicWordLaw
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw

/- This instance layer fixes the native alphabet, endpoint interval and control boxes.
   Its arbitrary finite carriers do not generalize those source-specific choices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteCompleteObstruction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BigOperators
open NativeBorelCommonFlow NativeConditionalControl.Tail NativeFullResidual FourthSegmentStoppedLaw
open NativeInstalledFullLaw NativeObserverJointLaw

abbrev CurveParameter := {x : ℝ // x ∈ Set.Icc (239 / 1000 : ℝ) (6 / 25)}

def curveQ : ℝ := 1944 / 390625

def curveG (x : ℝ) : ℝ := curveQ / x ^ 3

def curveU (x : ℝ) : ℝ := 1 - curveG x - x

def curveV (x : ℝ) : ℝ := x / (curveG x + x)

theorem scalar_boxes (t : CurveParameter) :
    1 / 3 ≤ curveU t ∧ curveU t ≤ 2 / 5 ∧
    1 / 3 ≤ curveV t ∧ curveV t ≤ 2 / 5 ∧
    9 / 25 ≤ curveG t ∧ curveG t ≤ 73 / 200 := by
  let x : ℝ := t
  have hlo : (239 / 1000 : ℝ) ≤ x := t.property.1
  have hhi : x ≤ 6 / 25 := t.property.2
  have hx : 0 < x := by linarith
  have h3 : 0 < x ^ 3 := pow_pos hx 3
  have hp3lo : (239 / 1000 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hlo 3
  have hp3hi : x ^ 3 ≤ (6 / 25 : ℝ) ^ 3 := pow_le_pow_left₀ hx.le hhi 3
  have hgl : (9 / 25 : ℝ) ≤ curveG x := by
    apply (le_div_iff₀ h3).mpr
    unfold curveQ
    nlinarith
  have hgu : curveG x ≤ (73 / 200 : ℝ) := by
    apply (div_le_iff₀ h3).mpr
    unfold curveQ
    norm_num at hp3lo
    nlinarith
  have hbr : 0 ≤ (3 / 5 - x) * (x ^ 2 + x * (6 / 25) + (6 / 25) ^ 2) - (6 / 25) ^ 3 := by
    have ha : 0 ≤ (3 / 5 - x) * (x ^ 2 + x * (6 / 25)) :=
      mul_nonneg (by linarith) (add_nonneg (sq_nonneg _) (mul_nonneg hx.le (by norm_num)))
    have hb : 0 ≤ (6 / 25 : ℝ) ^ 2 * (3 / 5 - x - 6 / 25) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith
  have hfac := mul_nonneg (show 0 ≤ (6 / 25 : ℝ) - x by linarith) hbr
  have hpoly : 0 ≤ x ^ 4 - (3 / 5) * x ^ 3 + curveQ := by
    unfold curveQ
    nlinarith [hfac]
  have hug : 3 / 5 - x ≤ curveG x := by
    apply (le_div_iff₀ h3).mpr
    nlinarith [hpoly]
  have hden : 0 < curveG x + x := by linarith
  have hp4hi : x ^ 4 ≤ (6 / 25 : ℝ) ^ 4 := pow_le_pow_left₀ hx.le hhi 4
  have hvg : (3 / 2) * x ≤ curveG x := by
    apply (le_div_iff₀ h3).mpr
    unfold curveQ
    nlinarith [hp4hi]
  have hvl : (1 / 3 : ℝ) ≤ curveV x := by
    unfold curveV
    apply (le_div_iff₀ hden).mpr
    linarith
  have hvu : curveV x ≤ (2 / 5 : ℝ) := by
    unfold curveV
    apply (div_le_iff₀ hden).mpr
    linarith
  change 1 / 3 ≤ curveU x ∧ curveU x ≤ 2 / 5 ∧
    1 / 3 ≤ curveV x ∧ curveV x ≤ 2 / 5 ∧ 9 / 25 ≤ curveG x ∧ curveG x ≤ 73 / 200
  refine ⟨?_, ?_, hvl, hvu, hgl, hgu⟩ <;> unfold curveU <;> linarith

/-- The original parameters, with the same x in all three control labels. -/
def curveParameters (t : CurveParameter) : NativePeriodicWordLaw.Parameters where
  w := 1 / 4
  u _ := curveU t
  v _ := curveV t
  w_pos := by norm_num
  w_lt := by norm_num
  u_box _ := ⟨(scalar_boxes t).1, (scalar_boxes t).2.1⟩
  v_box _ := ⟨(scalar_boxes t).2.2.1, (scalar_boxes t).2.2.2.1⟩


theorem curve_algebra (t : CurveParameter) :
    (1 - curveU t) * curveV t = (t : ℝ) ∧
    (1 - curveU t) * (1 - curveV t) = curveG t := by
  have hd : curveG t + (t : ℝ) ≠ 0 := ne_of_gt (by
    have h := scalar_boxes t; have hx := t.property.1; linarith)
  constructor <;> unfold curveU curveV <;> field_simp <;> ring

theorem curve_coord (t : CurveParameter) (n : ℕ) (b : Letter) :
    NativePeriodicWordLaw.coord (curveParameters t) n b 2 =
      (if b = 0 then curveU t else curveG t) * (t : ℝ)^n := by
  rw [NativePeriodicWordLaw.fixed_coord]
  have hh : NativePeriodicWordLaw.fixedRate (curveParameters t) = (t : ℝ) := by
    exact (curve_algebra t).1
  rw [hh]
  simp only [NativePeriodicWordLaw.coord]
  split_ifs
  · change (t : ℝ)^n * curveU t = curveU t * (t : ℝ)^n
    ring
  · have hg : NativePeriodicWordLaw.g (curveParameters t) 2 = curveG t :=
      (curve_algebra t).2
    rw [hg]; ring

universe u
variable {Z : Type u} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

private def readSymbol (w : Marked Z) : Letter :=
  match w.2 with
  | some (.read b) => b
  | _ => 0

private def cylinder (M : Observer Z) (e : InstalledEmitter M)
    (w : Marked Z) (a : List Letter) : ℝ≥0∞ :=
  markedLaw M e w (rawFrom ⁻¹' prefixCylinder a)

private theorem cylinder_cons (M : Observer Z) (e : InstalledEmitter M)
    (w : Marked Z) (b : Letter) (a : List Letter) :
    cylinder M e w (b::a) = ∑ v : Marked Z,
      markedRow M e w v * (if readSymbol v = b then cylinder M e v a else 0) := by
  rw [cylinder,marked_regenerate M e w]
  simp only [Measure.coe_finsetSum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro v _
  rw [Measure.smul_apply,Measure.map_apply (measurable_prepend w)
    ((measurable_cylinder _).preimage rawFrom_measurable)]
  change _ * markedLaw M e v _ = _
  congr 1
  have he : (prepend w) ⁻¹' (rawFrom ⁻¹' prefixCylinder (b::a)) =ᵐ[markedLaw M e v]
      (if readSymbol v = b then rawFrom ⁻¹' prefixCylinder a else ∅ : Set (ℕ → Marked Z)) := by
    filter_upwards [marked_head M e v] with x hx
    apply propext
    have hprefix : Prefix (rawFrom (prepend w x)) (b::a) ↔
        readSymbol v = b ∧ Prefix (rawFrom x) a := by
      simp [Prefix,readPrefix,List.ofFn_succ,rawFrom,prepend,hx,readSymbol]
      tauto
    change Prefix (rawFrom (prepend w x)) (b::a) ↔ _
    rw [hprefix]
    split_ifs with h
    · change (readSymbol v = b ∧ Prefix (rawFrom x) a) ↔ Prefix (rawFrom x) a
      exact and_iff_right h
    · change (readSymbol v = b ∧ Prefix (rawFrom x) a) ↔ False
      simp [h]
  rw [measure_congr he]
  split_ifs
  · rfl
  · exact measure_empty

def letterStep (M : Observer Z) (e : InstalledEmitter M) (b : Letter) :
    Module.End ℝ (Marked Z → ℝ) where
  toFun f w := ∑ v : Marked Z, (markedRow M e w v).toReal *
    (if readSymbol v = b then f v else 0)
  map_add' f g := by
    funext w
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> ring
  map_smul' r f := by
    funext w
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> ring

def cylinderVector (M : Observer Z) (e : InstalledEmitter M)
    (a : List Letter) : Marked Z → ℝ := fun w => (cylinder M e w a).toReal

private theorem cylinderVector_cons (M : Observer Z) (e : InstalledEmitter M)
    (b : Letter) (a : List Letter) :
    cylinderVector M e (b::a) = letterStep M e b (cylinderVector M e a) := by
  funext w
  rw [cylinderVector,cylinder_cons,ENNReal.toReal_sum (fun v _ => by
    apply ENNReal.mul_ne_top
    · exact PMF.apply_ne_top _ _
    · split_ifs <;> first | exact measure_ne_top (markedLaw M e v) _ | simp)]
  apply Finset.sum_congr rfl
  intro v _
  simp only [ENNReal.toReal_mul]
  split_ifs <;> rfl

theorem cylinderVector_pWord (M : Observer Z) (e : InstalledEmitter M) (n : ℕ) :
    cylinderVector M e (pWord n 1) =
      ((letterStep M e 1 * letterStep M e 0)^n) (cylinderVector M e [1,1]) := by
  induction n with
  | zero => simp [pWord,loopWord,Module.End.one_apply]
  | succ n ih =>
    rw [p_word_succ,cylinderVector_cons,cylinderVector_cons,ih,pow_succ']
    rfl

theorem tail_coordinate (M : Observer Z) (e : InstalledEmitter M) (z : Z) (n : ℕ) :
    (tailLaw M e .p z).real {pAtom n 1} = cylinderVector M e (pWord n 1) (z,none) := by
  unfold Measure.real tailLaw cylinderVector cylinder
  have hm : Measurable (fun x : ℕ → Marked Z => tailValue .p (rawFrom x)) :=
    (((measurable_stopped_read_word .p).subtype_mk).comp rawFrom_measurable)
  rw [Measure.map_apply hm (measurableSet_singleton _)]
  congr 1
  congr 1
  ext x
  change tailValue .p (rawFrom x) = pAtom n 1 ↔ Prefix (rawFrom x) (pWord n 1)
  rw [Subtype.ext_iff]
  change stoppedReadWord .p (rawFrom x) = some (pWord n 1) ↔ _
  rw [stopped_word_fiber]
  exact and_iff_left ⟨1,n,rfl⟩

def initialReadout (ρ : PMF Z) : (Marked Z → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ z : Z, (ρ z).toReal * f (z,none)
  map_add' f g := by simp [mul_add,Finset.sum_add_distrib]
  map_smul' r f := by simp [Finset.mul_sum,mul_left_comm]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelFiniteCompleteObstruction
