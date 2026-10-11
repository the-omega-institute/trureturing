/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CompleteTailWeightedDistortion
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CompleteTailWeightedDistortion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete-event distortion contracts under primed continuation coefficients. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeEmissionClipping

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CompleteTailWeightedDistortion
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BigOperators
open FourthSegmentStoppedLaw ConstantSuspensionSeparator NativePaidHistoryCommonRowRisks
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

private theorem tv_le_events (P Q : Measure RawTail)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (d : ℝ) (hd : 0 ≤ d)
    (h : ∀ E : Set RawTail, |P.real E-Q.real E| ≤ d) :
    (measurableTotalVariation P Q).toReal ≤ d := by
  have ht : measurableTotalVariation P Q ≤ ENNReal.ofReal d := by
    unfold measurableTotalVariation
    apply iSup_le
    intro E
    apply max_le
    · apply (ENNReal.toReal_le_toReal
        (ne_top_of_le_ne_top (measure_ne_top _ _) tsub_le_self) ENNReal.ofReal_ne_top).mp
      by_cases hpq : Q E.val ≤ P E.val
      · rw [ENNReal.toReal_sub_of_le hpq (measure_ne_top _ _),ENNReal.toReal_ofReal hd]
        exact (le_abs_self _).trans (h E.val)
      · rw [tsub_eq_zero_of_le (le_of_not_ge hpq),ENNReal.toReal_ofReal hd]
        exact hd
    · apply (ENNReal.toReal_le_toReal
        (ne_top_of_le_ne_top (measure_ne_top _ _) tsub_le_self) ENNReal.ofReal_ne_top).mp
      by_cases hpq : P E.val ≤ Q E.val
      · rw [ENNReal.toReal_sub_of_le hpq (measure_ne_top _ _),ENNReal.toReal_ofReal hd]
        simpa only [Measure.real,neg_sub] using (neg_le_abs (P.real E-Q.real E)).trans (h E.val)
      · rw [tsub_eq_zero_of_le (le_of_not_ge hpq),ENNReal.toReal_ofReal hd]
        exact hd
  simpa only [ENNReal.toReal_ofReal hd] using ENNReal.toReal_mono ENNReal.ofReal_ne_top ht

private theorem mixture_bounds {Y : Type*} [Fintype Y] (B : Y → ℝ)
    (hB : ∀ y, 0 ≤ B y) (hBs : ∑ y, B y = 1)
    (W : Y → Measure RawTail) (hW : ∀ y, IsProbabilityMeasure (W y)) (E : Set RawTail) :
    0 ≤ ∑ y, B y * (W y).real E ∧ ∑ y, B y * (W y).real E ≤ 1 := by
  haveI (y : Y) : IsProbabilityMeasure (W y) := hW y
  constructor
  · exact Finset.sum_nonneg fun y _ => mul_nonneg (hB y) measureReal_nonneg
  · calc
      _ ≤ ∑ y, B y * 1 := Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (by
          simpa only [probReal_univ] using
            (measureReal_mono (μ := W y) (Set.subset_univ E))) (hB y)
      _ = 1 := by simpa using hBs

private theorem mixture_gap {Y : Type*} [Fintype Y] (B : Y → ℝ)
    (hB : ∀ y, 0 ≤ B y) (W W' : Y → Measure RawTail)
    (hW : ∀ y, IsProbabilityMeasure (W y)) (hW' : ∀ y, IsProbabilityMeasure (W' y))
    (E : Set RawTail) :
    |(∑ y, B y*(W y).real E)-(∑ y, B y*(W' y).real E)| ≤
      ∑ y, B y*(measurableTotalVariation (W y) (W' y)).toReal := by
  haveI (y : Y) : IsProbabilityMeasure (W y) := hW y
  haveI (y : Y) : IsProbabilityMeasure (W' y) := hW' y
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ y, |B y*(W y).real E-B y*(W' y).real E| := abs_sum_le_sum_abs _ _
    _ = ∑ y, B y*|(W y).real E-(W' y).real E| := by
      apply Finset.sum_congr rfl
      intro y _
      rw [← mul_sub,abs_mul,abs_of_nonneg (hB y)]
    _ ≤ _ := Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (event_gap _ _ E (by trivial)) (hB y)

private theorem one_step {Y : Type*} [Fintype Y]
    (P P' : Measure RawTail) [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (t t' : ℝ) (ht' : 0 ≤ t' ∧ t' ≤ 1) (c : RawTail) (f : RawTail → RawTail)
    (B : Y → ℝ) (hB : ∀ y, 0 ≤ B y) (hBs : ∑ y, B y = 1)
    (W W' : Y → Measure RawTail)
    (hW : ∀ y, IsProbabilityMeasure (W y)) (hW' : ∀ y, IsProbabilityMeasure (W' y))
    (hP : ∀ E : Set RawTail, P.real E = t*(if c ∈ E then 1 else 0) +
      (1-t)*∑ y, B y*(W y).real (f ⁻¹' E))
    (hP' : ∀ E : Set RawTail, P'.real E = t'*(if c ∈ E then 1 else 0) +
      (1-t')*∑ y, B y*(W' y).real (f ⁻¹' E)) :
    (measurableTotalVariation P P').toReal ≤ |t-t'| +
      (1-t')*∑ y, B y*(measurableTotalVariation (W y) (W' y)).toReal := by
  have hs : 0 ≤ ∑ y, B y*(measurableTotalVariation (W y) (W' y)).toReal :=
    Finset.sum_nonneg fun y _ => mul_nonneg (hB y) ENNReal.toReal_nonneg
  apply tv_le_events P P' _ (add_nonneg (abs_nonneg _) (mul_nonneg (by linarith) hs))
  intro E
  let K := ∑ y, B y*(W y).real (f ⁻¹' E)
  let K' := ∑ y, B y*(W' y).real (f ⁻¹' E)
  let i : ℝ := if c ∈ E then 1 else 0
  have hK : 0 ≤ K ∧ K ≤ 1 := mixture_bounds B hB hBs W hW _
  have hi : 0 ≤ i ∧ i ≤ 1 := by dsimp [i]; split_ifs <;> norm_num
  have hik : |i-K| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hgap : |K-K'| ≤ ∑ y, B y*(measurableTotalVariation (W y) (W' y)).toReal :=
    mixture_gap B hB W W' hW hW' _
  rw [hP,hP']
  change |t*i+(1-t)*K-(t'*i+(1-t')*K')| ≤ _
  rw [show t*i+(1-t)*K-(t'*i+(1-t')*K') =
    (t-t')*(i-K)+(1-t')*(K-K') by ring]
  calc
    _ ≤ |(t-t')*(i-K)| + |(1-t')*(K-K')| := abs_add_le _ _
    _ = |t-t'| *|i-K|+(1-t')*|K-K'| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by linarith : 0 ≤ 1-t')]
    _ ≤ |t-t'| *1+(1-t')*(∑ y, B y*(measurableTotalVariation (W y) (W' y)).toReal) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hik (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hgap (by linarith))
    _ = _ := by ring

/-- Original zero and unit emissions and original noncompletion need no contraction. -/
theorem stationary_weighted_complete_distortion {X Y : Type*} [Fintype X] [Fintype Y]
    (R : RegularTable X Y) (u : X → ℝ) (v : Y → ℝ)
    (Q : X → Measure RawTail) (W : Y → Measure RawTail)
    (hQ : ∀ x, IsProbabilityMeasure (Q x)) (hW : ∀ y, IsProbabilityMeasure (W y))
    (hq : ∀ x (E : Set RawTail), (Q x).real E =
      u x*(if some [0] ∈ E then 1 else 0) +
        (1-u x)*∑ y, R.B x y*(W y).real ((prefixRaw 1) ⁻¹' E))
    (hw : ∀ y (E : Set RawTail), (W y).real E =
      (1-v y)*(if some [1] ∈ E then 1 else 0) +
        v y*∑ x, R.A y x*(Q x).real ((prefixRaw 0) ⁻¹' E)) :
    let du := ∑ x, R.pi x*|u x-R.u x|
    let dv := ∑ y, R.tau y*|v y-R.v y|
    let DQ := ∑ x, R.pi x*(measurableTotalVariation (Q x) (R.Q x)).toReal
    let DW := ∑ y, R.tau y*(measurableTotalVariation (W y) (R.W y)).toReal
    DQ ≤ du+(2/3)*DW ∧ DW ≤ dv+(2/5)*DQ ∧
      DQ ≤ (15*du+10*dv)/11 ∧ DW ≤ (6*du+15*dv)/11 := by
  haveI (x : X) : IsProbabilityMeasure (Q x) := hQ x
  haveI (y : Y) : IsProbabilityMeasure (W y) := hW y
  haveI (x : X) : IsProbabilityMeasure (R.Q x) := R.Qprob x
  haveI (y : Y) : IsProbabilityMeasure (R.W y) := R.Wprob y
  dsimp only
  let q := fun x => (measurableTotalVariation (Q x) (R.Q x)).toReal
  let w := fun y => (measurableTotalVariation (W y) (R.W y)).toReal
  have hp (x : X) : q x ≤ |u x-R.u x|+(2/3)*∑ y, R.B x y*w y := by
    have h := one_step (Q x) (R.Q x) (u x) (R.u x)
      ⟨by have hb := (R.u_box x).1; linarith,by have hb := (R.u_box x).2; linarith⟩
      (some [0]) (prefixRaw 1) (R.B x) (R.B_nonneg x) (R.B_sum x)
      W R.W hW R.Wprob (hq x) (R.q_generate x)
    apply h.trans
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
      (show 1-R.u x ≤ 2/3 by have hb := (R.u_box x).1; linarith)
      (show 0 ≤ ∑ y, R.B x y*w y from
        Finset.sum_nonneg fun y _ => mul_nonneg (R.B_nonneg x y) ENNReal.toReal_nonneg))
  have hb (y : Y) : w y ≤ |v y-R.v y|+(2/5)*∑ x, R.A y x*q x := by
    have h := one_step (W y) (R.W y) (1-v y) (1-R.v y)
      ⟨by have hb := (R.v_box y).2; linarith,by have hb := (R.v_box y).1; linarith⟩
      (some [1]) (prefixRaw 0) (R.A y) (R.A_nonneg y) (R.A_sum y)
      Q R.Q hQ R.Qprob
      (by intro E; simpa using hw y E) (by intro E; simpa using R.w_generate y E)
    have he : |(1-v y)-(1-R.v y)| = |v y-R.v y| := by
      rw [show (1-v y)-(1-R.v y) = -(v y-R.v y) by ring,abs_neg]
    rw [he] at h
    simp only [sub_sub_cancel] at h
    apply h.trans
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (R.v_box y).2
      (show 0 ≤ ∑ x, R.A y x*q x from
        Finset.sum_nonneg fun x _ => mul_nonneg (R.A_nonneg y x) ENNReal.toReal_nonneg))
  have hpa : (∑ x, R.pi x*q x) ≤
      (∑ x, R.pi x*|u x-R.u x|)+(2/3)*(∑ y, R.tau y*w y) := by
    calc
      _ ≤ ∑ x, R.pi x*(|u x-R.u x|+(2/3)*∑ y, R.B x y*w y) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hp x) (R.pi_nonneg x)
      _ = _ := by
        simp only [mul_add,Finset.sum_add_distrib]
        congr 1
        calc
          _ = (2/3)*∑ x, ∑ y, (R.pi x*R.B x y)*w y := by
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro x _
            apply Finset.sum_congr rfl; intro y _; ring
          _ = _ := by
            rw [Finset.sum_comm]
            simp_rw [← Finset.sum_mul,R.pi_B]
  have hba : (∑ y, R.tau y*w y) ≤
      (∑ y, R.tau y*|v y-R.v y|)+(2/5)*(∑ x, R.pi x*q x) := by
    calc
      _ ≤ ∑ y, R.tau y*(|v y-R.v y|+(2/5)*∑ x, R.A y x*q x) :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hb y) (R.tau_nonneg y)
      _ = _ := by
        simp only [mul_add,Finset.sum_add_distrib]
        congr 1
        calc
          _ = (2/5)*∑ y, ∑ x, (R.tau y*R.A y x)*q x := by
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro y _
            apply Finset.sum_congr rfl; intro x _; ring
          _ = _ := by
            rw [Finset.sum_comm]
            simp_rw [← Finset.sum_mul,R.tau_A]
  exact ⟨hpa,hba,by linarith,by linarith⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CompleteTailWeightedDistortion
