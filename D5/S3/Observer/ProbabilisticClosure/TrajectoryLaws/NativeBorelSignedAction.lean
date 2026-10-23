/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSignedAction
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSignedAction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded signed-real acquired action and a uniform three-return late-coordinate estimate. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelEndpointIdentification
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeBorelCommonFlow NativeBorelEndpointIdentification NativeFullResidual
open NativeConditionalControl.Tail FourthSegmentStoppedLaw
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelSignedAction


def Bounded {X : Type*} [MeasurableSpace X] (f : X → ℝ) : Prop :=
  Measurable f ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M

lemma Bounded.integrable {X : Type*} [MeasurableSpace X] {f : X → ℝ}
    (hf : Bounded f) (μ : Measure X) [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨hm,M,hM,hb⟩ := hf
  exact Integrable.of_bound hm.aestronglyMeasurable M (Eventually.of_forall hb)

lemma bounded_const {X : Type*} [MeasurableSpace X] (a : ℝ) : Bounded (fun _ : X => a) :=
  ⟨measurable_const, ‖a‖, norm_nonneg _, fun _ => le_rfl⟩

lemma Bounded.add {X : Type*} [MeasurableSpace X] {f g : X → ℝ}
    (hf : Bounded f) (hg : Bounded g) : Bounded (fun x => f x + g x) := by
  obtain ⟨mf,M,hM,bf⟩ := hf; obtain ⟨mg,N,hN,bg⟩ := hg
  exact ⟨mf.add mg, M+N, add_nonneg hM hN, fun x => (norm_add_le _ _).trans (add_le_add (bf x) (bg x))⟩

lemma Bounded.neg {X : Type*} [MeasurableSpace X] {f : X → ℝ}
    (hf : Bounded f) : Bounded (fun x => -f x) := by
  obtain ⟨mf,M,hM,bf⟩ := hf
  exact ⟨mf.neg, M,hM,fun x => by simpa using bf x⟩

lemma Bounded.sub {X : Type*} [MeasurableSpace X] {f g : X → ℝ}
    (hf : Bounded f) (hg : Bounded g) : Bounded (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma Bounded.mul_const {X : Type*} [MeasurableSpace X] {f : X → ℝ}
    (hf : Bounded f) (a : ℝ) : Bounded (fun x => a*f x) := by
  obtain ⟨mf,M,hM,bf⟩ := hf
  refine ⟨measurable_const.mul mf, ‖a‖*M, mul_nonneg (norm_nonneg _) hM, ?_⟩
  intro x; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (bf x) (norm_nonneg _)

def action (F : CommonFlow) (f : PDescriptor → ℝ) (Q : PDescriptor) : ℝ :=
  ∫ R, f R ∂F.L Q

def realIterate (F : CommonFlow) (f : PDescriptor → ℝ) : ℕ → PDescriptor → ℝ
  | 0 => f
  | j+1 => action F (realIterate F f j)

lemma row_mass (F : CommonFlow) (Q : PDescriptor) : (F.L Q).real Set.univ ≤ 1 := by
  have h := ENNReal.toReal_mono ENNReal.one_ne_top ((L_le_C F Q Set.univ).trans (by simp))
  simpa [Measure.real] using h

lemma Bounded.action (F : CommonFlow) {f : PDescriptor → ℝ} (hf : Bounded f) :
    Bounded (action F f) := by
  obtain ⟨mf,M,hM,bf⟩ := hf
  refine ⟨mf.stronglyMeasurable.integral_kernel.measurable, M,hM,?_⟩
  intro Q
  exact (norm_integral_le_of_norm_le_const (Eventually.of_forall bf)).trans
    ((mul_le_mul_of_nonneg_left (row_mass F Q) hM).trans_eq (mul_one _))

lemma Bounded.realIterate (F : CommonFlow) {f : PDescriptor → ℝ} (hf : Bounded f) :
    ∀ j, Bounded (realIterate F f j) := by
  intro j; induction j with
  | zero => exact hf
  | succ j ih => exact ih.action F

lemma action_add (F : CommonFlow) {f g : PDescriptor → ℝ}
    (hf : Bounded f) (hg : Bounded g) (Q : PDescriptor) :
    action F (fun R => f R+g R) Q = action F f Q+action F g Q :=
  integral_add (hf.integrable _) (hg.integrable _)

lemma action_sub (F : CommonFlow) {f g : PDescriptor → ℝ}
    (hf : Bounded f) (hg : Bounded g) (Q : PDescriptor) :
    action F (fun R => f R-g R) Q = action F f Q-action F g Q :=
  integral_sub (hf.integrable _) (hg.integrable _)

lemma action_mul (F : CommonFlow) (f : PDescriptor → ℝ) (a : ℝ) (Q : PDescriptor) :
    action F (fun R => a*f R) Q = a*action F f Q := integral_const_mul a f

lemma ae_action (F : CommonFlow) {f g : PDescriptor → ℝ} (h : f =ᵐ[F.nuP] g) :
    action F f =ᵐ[F.nuP] action F g := by
  have hC := Measure.ae_ae_of_ae_comp (κ := F.C) ((common_flow_word_iteration F).1.symm ▸ h)
  filter_upwards [hC] with Q hQ
  exact integral_congr_ae ((L_le_C F Q).absolutelyContinuous.ae_le hQ)

lemma ae_action_mono (F : CommonFlow) {f g : PDescriptor → ℝ}
    (hf : Bounded f) (hg : Bounded g) (h : f ≤ᵐ[F.nuP] g) :
    action F f ≤ᵐ[F.nuP] action F g := by
  have hC := Measure.ae_ae_of_ae_comp (κ := F.C) ((common_flow_word_iteration F).1.symm ▸ h)
  filter_upwards [hC] with Q hQ
  exact integral_mono_ae (hf.integrable _) (hg.integrable _)
    ((L_le_C F Q).absolutelyContinuous.ae_le hQ)

lemma weighted_action (F : CommonFlow) {f : PDescriptor → ℝ} (hf : Bounded f)
    (Q : PDescriptor) :
    action F f Q = (1-u Q).toReal * ∫ W, (v W).toReal * ∫ R, f R ∂F.A W ∂F.B Q := by
  have hd : Measurable (Function.uncurry (fun (Q : PDescriptor) (_ : PDescriptor) => 1-u Q)) :=
    measurable_const.sub (measurable_u.comp measurable_fst)
  unfold action
  rw [CommonFlow.L, Kernel.withDensity_apply _ hd, withDensity_const,
    integral_smul_measure]
  simp only [smul_eq_mul]
  congr 1
  rw [Kernel.integral_comp (hf.integrable _)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun W => by
    change (∫ R, f R ∂F.A.withDensity (fun W _ => v W) W) = _
    have hv : Measurable (Function.uncurry (fun W (_ : PDescriptor) => v W)) := by
      change Measurable (fun p : BDescriptor × PDescriptor => v p.1)
      exact measurable_v.comp measurable_fst
    rw [Kernel.withDensity_apply F.A (f := fun W (_ : PDescriptor) => v W) hv W,
      withDensity_const, integral_smul_measure]
    rfl)

lemma original_A_zero (F : CommonFlow) : ∀ᵐ W ∂F.nuB,
    law W {betaAtom 0 1} = v W * ∫⁻ Q, coordinate 0 1 Q ∂F.A W := by
  exact A_coordinate F 0 1


lemma margin_B (F : CommonFlow) : F.B ∘ₘ F.nuP = F.nuB := by
  rw [← F.marginB₁, ← Measure.snd_compProd, F.disintegrateB.disintegrate, F.marginB₂]
lemma margin_A (F : CommonFlow) : F.A ∘ₘ F.nuB = F.nuP := by
  rw [← F.marginA₁, ← Measure.snd_compProd, F.disintegrateA.disintegrate, F.marginA₂]

lemma bounded_coordinate (n : ℕ) (i : Letter) :
    Bounded (fun Q => (coordinate n i Q).toReal) := by
  refine ⟨(measurable_coordinate n i).ennreal_toReal, 1, by norm_num, ?_⟩
  intro Q
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one).trans_eq (by simp)

lemma coordinate_integral_real (F : CommonFlow) (n : ℕ) (i : Letter) (Q : PDescriptor) :
    action F (fun R => (coordinate n i R).toReal) Q =
      (∫⁻ R, coordinate n i R ∂F.L Q).toReal := by
  exact integral_toReal (measurable_coordinate n i).aemeasurable
    (Eventually.of_forall (fun R => (measure_ne_top (law R) _).lt_top))

lemma real_coordinate_step (F : CommonFlow) (n : ℕ) (i : Letter) :
    (fun Q => (coordinate (n+1) i Q).toReal) =ᵐ[F.nuP]
      action F (fun Q => (coordinate n i Q).toReal) := by
  filter_upwards [coordinate_step F n i] with Q hQ
  rw [coordinate_integral_real, hQ]

lemma action_const (F : CommonFlow) (a : ℝ) (Q : PDescriptor) :
    action F (fun _ => a) Q = a * action F (fun _ => 1) Q := by
  simpa using action_mul F (fun _ => 1) a Q

lemma realIterate_nonneg (F : CommonFlow) {f : PDescriptor → ℝ}
    (hf : Bounded f) (h : 0 ≤ᵐ[F.nuP] f) (n : ℕ) :
    0 ≤ᵐ[F.nuP] realIterate F f n := by
  induction n with
  | zero => exact h
  | succ n ih =>
    have hm := ae_action_mono F (bounded_const 0) (hf.realIterate F n) ih
    have hz : action F (fun _ => 0) = 0 := by funext Q; simp [action]
    simpa only [hz, realIterate] using hm

lemma integrated_action_bounds (F : CommonFlow) {f : PDescriptor → ℝ}
    (hf : Bounded f) (h : 0 ≤ᵐ[F.nuP] f) :
    (1/5 : ℝ) * (∫ Q, f Q ∂F.nuP) ≤ ∫ Q, action F f Q ∂F.nuP ∧
      (∫ Q, action F f Q ∂F.nuP) ≤ (4/15 : ℝ) * (∫ Q, f Q ∂F.nuP) := by
  have hc := Measure.ae_ae_of_ae_comp (κ := F.C)
    ((common_flow_word_iteration F).1.symm ▸ h)
  have hint : ∫ Q, (∫ R, f R ∂F.C Q) ∂F.nuP = ∫ R, f R ∂F.nuP := by
    calc
      _ = ∫ R, f R ∂(F.C ∘ₘ F.nuP) := by
        rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (hf.integrable _)]
        rfl
      _ = _ := by rw [(common_flow_word_iteration F).1]
  have hl : ∀ᵐ Q ∂F.nuP, (1/5 : ℝ) * (∫ R, f R ∂F.C Q) ≤ action F f Q ∧
      action F f Q ≤ (4/15 : ℝ) * (∫ R, f R ∂F.C Q) := by
    filter_upwards [hc] with Q hQ
    have bounds := (common_flow_operator_bounds F).1 Q
    constructor
    · have hm := integral_mono_measure bounds.1
        ((L_le_C F Q).absolutelyContinuous.ae_le hQ) (hf.integrable _)
      simpa [action, integral_smul_measure] using hm
    · have hn : 0 ≤ᵐ[(4/15 : ℝ≥0∞) • F.C Q] f := by
        exact (Measure.smul_absolutelyContinuous (μ := F.C Q) (c := (4/15 : ℝ≥0∞))).ae_le hQ
      have hm := integral_mono_measure bounds.2 hn
        ((hf.integrable (F.C Q)).smul_measure (by finiteness : (4/15 : ℝ≥0∞) ≠ ∞))
      simpa [action, integral_smul_measure] using hm

  have hiC : Integrable (fun Q => ∫ R, f R ∂F.C Q) F.nuP := by
    obtain ⟨mf,M,hM,bf⟩ := hf
    apply Integrable.of_bound mf.stronglyMeasurable.integral_kernel.aestronglyMeasurable M
    apply Eventually.of_forall
    intro Q
    simpa using norm_integral_le_of_norm_le_const (Eventually.of_forall bf) (μ := F.C Q)
  constructor
  · have hi := integral_mono_ae (hiC.const_mul (1/5)) ((hf.action F).integrable _) (hl.mono (fun _ hh => hh.1))
    simpa [integral_const_mul, hint] using hi
  · have hi := integral_mono_ae ((hf.action F).integrable _) (hiC.const_mul (4/15)) (hl.mono (fun _ hh => hh.2))
    simpa [integral_const_mul, hint] using hi

lemma integrated_iterate_bounds (F : CommonFlow) {f : PDescriptor → ℝ}
    (hf : Bounded f) (h : 0 ≤ᵐ[F.nuP] f) (n : ℕ) :
    (1/5 : ℝ)^n * (∫ Q, f Q ∂F.nuP) ≤ ∫ Q, realIterate F f n Q ∂F.nuP ∧
      (∫ Q, realIterate F f n Q ∂F.nuP) ≤ (4/15 : ℝ)^n * (∫ Q, f Q ∂F.nuP) := by
  induction n with
  | zero => simp [realIterate]
  | succ n ih =>
    have hs := integrated_action_bounds F (hf.realIterate F n) (realIterate_nonneg F hf h n)
    constructor
    · calc
        (1/5 : ℝ)^(n+1) * _ = (1/5) * ((1/5)^n * _) := by rw [pow_succ]; ring
        _ ≤ (1/5) * (∫ Q, realIterate F f n Q ∂F.nuP) := mul_le_mul_of_nonneg_left ih.1 (by norm_num)
        _ ≤ _ := hs.1
    · calc
        _ ≤ (4/15) * (∫ Q, realIterate F f n Q ∂F.nuP) := hs.2
        _ ≤ (4/15) * ((4/15)^n * _) := mul_le_mul_of_nonneg_left ih.2 (by norm_num)
        _ = (4/15 : ℝ)^(n+1) * _ := by rw [pow_succ]; ring


def cR (b : Bool) : ℝ := if b then 9/25 else 4/9
def zR (b : Bool) : ℝ := if b then 6/25 else 2/9
def signR (b : Bool) : ℝ := if b then -1 else 1
def defect (b : Bool) (Q : PDescriptor) : ℝ := signR b * (cR b - (g Q).toReal)
def late (b : Bool) (j : ℕ) (Q : PDescriptor) : ℝ :=
  signR b * ((coordinate j 1 Q).toReal - cR b * zR b ^ j)
def variation (F : CommonFlow) (b : Bool) (Q : PDescriptor) : ℝ :=
  signR b * (action F (fun _ => 1) Q - zR b)

lemma bounded_defect (b : Bool) : Bounded (defect b) :=
  ((bounded_const (cR b)).sub (bounded_coordinate 0 1)).mul_const (signR b)
lemma bounded_late (b : Bool) (j : ℕ) : Bounded (late b j) :=
  ((bounded_coordinate j 1).sub (bounded_const (cR b * zR b^j))).mul_const (signR b)
lemma bounded_variation (F : CommonFlow) (b : Bool) : Bounded (variation F b) :=
  (((bounded_const 1).action F).sub (bounded_const (zR b))).mul_const (signR b)

lemma native_marker_real (b : Bool) (j : ℕ) :
    ((native .p (endpoint b) : Measure _) {pAtom j 1}).toReal = cR b * zR b^j := by
  rw [(native_atoms _).1]
  simp only [Fin.reduceEq, if_false, ENNReal.toReal_mul, ENNReal.toReal_pow]
  cases b <;> norm_num [endpoint, alphaMass, betaMass, lowerRate, upperRate,
    unitInterval.symm, unitInterval.coe_toNNReal, cR, zR]

lemma late_native_order (j : ℕ) (hj : 3 ≤ j) :
    (4/9 : ℝ) * (2/9 : ℝ)^j ≤ (9/25 : ℝ) * (6/25 : ℝ)^j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k+3 := ⟨j-3, by omega⟩
  clear hj
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hp : 0 ≤ (4/9 : ℝ) * (2/9 : ℝ)^(k+3) := by positivity
    calc
      _ = ((4/9 : ℝ) * (2/9 : ℝ)^(k+3)) * (2/9) := by
        rw [show k+1+3 = (k+3)+1 by omega, pow_succ]; ring
      _ ≤ ((4/9 : ℝ) * (2/9 : ℝ)^(k+3)) * (6/25) :=
        mul_le_mul_of_nonneg_left (by norm_num) hp
      _ ≤ ((9/25 : ℝ) * (6/25 : ℝ)^(k+3)) * (6/25) :=
        mul_le_mul_of_nonneg_right ih (by norm_num)
      _ = _ := by rw [show k+1+3 = (k+3)+1 by omega, pow_succ]; ring

lemma defect_nonneg (F : CommonFlow) (b : Bool) : 0 ≤ᵐ[F.nuP] defect b := by
  filter_upwards [(common_flow_operator_bounds F).2] with Q hQ
  have hlo := ENNReal.toReal_mono (measure_ne_top (law Q) _) hQ.1
  have hhi := ENNReal.toReal_mono (by finiteness : (4/9 : ℝ≥0∞) ≠ ∞) hQ.2.1
  change endpointCompletion.toReal ≤ (g Q).toReal at hlo
  norm_num [endpointCompletion] at hlo hhi
  cases b <;> simp [defect, signR, cR] <;> linarith

lemma late_nonneg (F : CommonFlow) (b : Bool) (j : ℕ) (hj : 3 ≤ j) :
    0 ≤ᵐ[F.nuP] late b j := by
  filter_upwards [F.boxP] with Q hQ
  have hb : min ((native .p (endpoint false) : Measure _) {pAtom j 1})
      ((native .p (endpoint true) : Measure _) {pAtom j 1}) ≤ coordinate j 1 Q ∧
      coordinate j 1 Q ≤ max ((native .p (endpoint false) : Measure _) {pAtom j 1})
      ((native .p (endpoint true) : Measure _) {pAtom j 1}) := by
    simpa only [endpoint, Bool.false_eq_true, if_false, if_true, native_coordinate, coordinate]
      using hQ (pAtom j 1)
  have hlo := ENNReal.toReal_mono (measure_ne_top (law Q) _) hb.1
  have hhi := ENNReal.toReal_mono (max_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) hb.2
  rw [ENNReal.toReal_min (measure_ne_top _ _) (measure_ne_top _ _), native_marker_real, native_marker_real] at hlo
  rw [ENNReal.toReal_max (measure_ne_top _ _) (measure_ne_top _ _), native_marker_real, native_marker_real] at hhi
  have ho := late_native_order j hj
  simp only [cR, zR, Bool.false_eq_true, if_false, if_true] at hlo hhi
  rw [min_eq_left ho] at hlo
  rw [max_eq_right ho] at hhi
  change (4/9 : ℝ)*(2/9 : ℝ)^j ≤ (coordinate j 1 Q).toReal at hlo
  cases b <;> simp [late, signR, cR, zR] <;> linarith

lemma late_step (F : CommonFlow) (b : Bool) (j : ℕ) :
    late b (j+1) =ᵐ[F.nuP]
      (fun Q => action F (late b j) Q + cR b * zR b^j * variation F b Q) := by
  filter_upwards [real_coordinate_step F j 1] with Q hQ
  unfold late variation
  rw [action_mul, action_sub (F := F) (bounded_coordinate j 1)
    (bounded_const (cR b * zR b^j)), action_const, hQ, pow_succ]
  ring


lemma realIterate_mul (F : CommonFlow) (f : PDescriptor → ℝ) (a : ℝ) (n : ℕ) :
    realIterate F (fun Q => a*f Q) n = fun Q => a*realIterate F f n Q := by
  induction n with
  | zero => rfl
  | succ n ih => funext Q; simp only [realIterate, ih, action_mul]

lemma realIterate_mono (F : CommonFlow) {f g : PDescriptor → ℝ}
    (hf : Bounded f) (hg : Bounded g) (h : f ≤ᵐ[F.nuP] g) (n : ℕ) :
    realIterate F f n ≤ᵐ[F.nuP] realIterate F g n := by
  induction n with
  | zero => exact h
  | succ n ih => exact ae_action_mono F (hf.realIterate F n) (hg.realIterate F n) ih

lemma first_defect_identity (F : CommonFlow) (b : Bool) :
    action F (defect b) =ᵐ[F.nuP]
      (fun Q => cR b * variation F b Q - late b 1 Q) := by
  filter_upwards [real_coordinate_step F 0 1] with Q hQ
  unfold defect variation late g
  rw [action_mul, action_sub (F := F) (bounded_const (cR b)) (bounded_coordinate 0 1), action_const]
  change (coordinate 1 1 Q).toReal = action F (fun Q => (coordinate 0 1 Q).toReal) Q at hQ
  rw [hQ]
  ring

lemma second_defect_identity (F : CommonFlow) (b : Bool) :
    realIterate F (defect b) 2 =ᵐ[F.nuP]
      (fun Q => cR b * action F (variation F b) Q + cR b * zR b * variation F b Q - late b 2 Q) := by
  have he := ae_action F (first_defect_identity F b)
  filter_upwards [he, late_step F b 1] with Q hQ h2
  change action F (action F (defect b)) Q = _ at hQ
  change action F (action F (defect b)) Q = _
  rw [hQ, action_sub (F := F) ((bounded_variation F b).mul_const (cR b)) (bounded_late b 1), action_mul]
  simp only [pow_one] at h2
  linarith

lemma three_step_identity (F : CommonFlow) (b : Bool) :
    realIterate F (defect b) 3 =ᵐ[F.nuP]
      (fun Q => cR b * (zR b^2 * variation F b Q + zR b * action F (variation F b) Q +
        realIterate F (variation F b) 2 Q) - late b 3 Q) := by
  have he := ae_action F (second_defect_identity F b)
  filter_upwards [he, late_step F b 2] with Q hQ h3
  change action F (realIterate F (defect b) 2) Q = _ at hQ
  change action F (realIterate F (defect b) 2) Q = _
  rw [hQ, action_sub (F := F)
    ((((bounded_variation F b).action F).mul_const (cR b)).add
      ((bounded_variation F b).mul_const (cR b * zR b))) (bounded_late b 2),
    action_add (F := F) (((bounded_variation F b).action F).mul_const (cR b))
      ((bounded_variation F b).mul_const (cR b * zR b)), action_mul, action_mul]
  change late b 3 Q = action F (late b 2) Q + cR b * zR b^2 * variation F b Q at h3
  change cR b * action F (action F (variation F b)) Q +
      (cR b * zR b) * action F (variation F b) Q - action F (late b 2) Q = _
  rw [h3]
  simp only [realIterate]
  ring

lemma signed_predecessor (F : CommonFlow) (b : Bool) (k : ℕ) :
    (fun Q => cR b * zR b^(k+3) * variation F b Q) ≤ᵐ[F.nuP] late b (k+4) := by
  have hp := realIterate_nonneg F (bounded_late b (k+3)) (late_nonneg F b (k+3) (by omega)) 1
  filter_upwards [hp, late_step F b (k+3)] with Q hQ hs
  change 0 ≤ action F (late b (k+3)) Q at hQ
  have he : k+3+1 = k+4 := by omega
  rw [he] at hs
  linarith

lemma three_step_late_bound (F : CommonFlow) (b : Bool) (k : ℕ) :
    (fun Q => zR b^(k+4) * realIterate F (defect b) 3 Q) ≤ᵐ[F.nuP]
      (fun Q => zR b^3 * late b (k+4) Q + zR b^2 * action F (late b (k+4)) Q +
        zR b * realIterate F (late b (k+4)) 2 Q) := by
  have hb := signed_predecessor F b k
  have h1 := realIterate_mono F ((bounded_variation F b).mul_const (cR b * zR b^(k+3)))
    (bounded_late b (k+4)) hb 1
  have h2 := realIterate_mono F ((bounded_variation F b).mul_const (cR b * zR b^(k+3)))
    (bounded_late b (k+4)) hb 2
  rw [realIterate_mul] at h1 h2
  filter_upwards [hb, h1, h2, three_step_identity F b, late_nonneg F b 3 (by omega)]
    with Q h0 h1 h2 hi hn
  have hz : 0 ≤ zR b := by cases b <;> norm_num [zR]
  have h0' := mul_le_mul_of_nonneg_left h0 (pow_nonneg hz 3)
  have h1' := mul_le_mul_of_nonneg_left h1 (pow_nonneg hz 2)
  have h2' := mul_le_mul_of_nonneg_left h2 hz
  have hsum := add_le_add (add_le_add h0' h1') h2'
  have hfirst : zR b^(k+4)*realIterate F (defect b) 3 Q ≤
      zR b^(k+4) * (cR b * (zR b^2 * variation F b Q +
        zR b * action F (variation F b) Q + realIterate F (variation F b) 2 Q)) := by
    rw [hi]
    exact mul_le_mul_of_nonneg_left (sub_le_self _ hn) (pow_nonneg hz _)
  calc
    _ ≤ _ := hfirst
    _ = zR b^3*(cR b*zR b^(k+3)*variation F b Q) +
        zR b^2*(cR b*zR b^(k+3)*action F (variation F b) Q) +
        zR b*(cR b*zR b^(k+3)*realIterate F (variation F b) 2 Q) := by
      rw [show k+4=(k+3)+1 by omega, pow_succ]
      ring
    _ ≤ _ := hsum

lemma integrated_three_step (F : CommonFlow) (b : Bool) (k : ℕ) :
    (1/5 : ℝ)^3 * zR b^(k+4) * (∫ Q, defect b Q ∂F.nuP) ≤
      (zR b^3 + (4/15 : ℝ)*zR b^2 + (4/15 : ℝ)^2*zR b) *
      (∫ Q, late b (k+4) Q ∂F.nuP) := by
  have hF := integrated_iterate_bounds F (bounded_defect b) (defect_nonneg F b) 3
  have hh := integrated_iterate_bounds F (bounded_late b (k+4)) (late_nonneg F b (k+4) (by omega)) 1
  have hh2 := integrated_iterate_bounds F (bounded_late b (k+4)) (late_nonneg F b (k+4) (by omega)) 2
  have hleft := ((bounded_defect b).realIterate F 3).mul_const (zR b^(k+4))
  have hright := (((bounded_late b (k+4)).mul_const (zR b^3)).add
      (((bounded_late b (k+4)).action F).mul_const (zR b^2))).add
      (((bounded_late b (k+4)).realIterate F 2).mul_const (zR b))
  have hint := integral_mono_ae (hleft.integrable F.nuP) (hright.integrable F.nuP)
    (three_step_late_bound F b k)
  have hi0 : Integrable (fun Q => zR b^3 * late b (k+4) Q) F.nuP :=
    ((bounded_late b (k+4)).mul_const (zR b^3)).integrable _
  have hi1 : Integrable (fun Q => zR b^2 * action F (late b (k+4)) Q) F.nuP :=
    (((bounded_late b (k+4)).action F).mul_const (zR b^2)).integrable _
  have hi2 : Integrable (fun Q => zR b * realIterate F (late b (k+4)) 2 Q) F.nuP :=
    (((bounded_late b (k+4)).realIterate F 2).mul_const (zR b)).integrable _
  have hadd1 := integral_add hi0 hi1
  have hadd2 := integral_add (hi0.add hi1) hi2
  simp only [Pi.add_apply] at hadd1 hadd2
  rw [hadd2,hadd1, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul] at hint
  have hz : 0 ≤ zR b := by cases b <;> norm_num [zR]
  have hFlo := mul_le_mul_of_nonneg_left hF.1 (pow_nonneg hz (k+4))
  have hhi1 := mul_le_mul_of_nonneg_left hh.2 (pow_nonneg hz 2)
  have hhi2 := mul_le_mul_of_nonneg_left hh2.2 hz
  change zR b^2 * (∫ Q, action F (late b (k+4)) Q ∂F.nuP) ≤ _ at hhi1
  simp only [pow_one] at hhi1
  calc
    _ = zR b^(k+4) * ((1/5 : ℝ)^3 * (∫ Q, defect b Q ∂F.nuP)) := by ring
    _ ≤ zR b^(k+4) * (∫ Q, realIterate F (defect b) 3 Q ∂F.nuP) := hFlo
    _ ≤ _ := hint
    _ ≤ zR b^3 * (∫ Q, late b (k+4) Q ∂F.nuP) +
        zR b^2 * ((4/15 : ℝ)*(∫ Q, late b (k+4) Q ∂F.nuP)) +
        zR b * ((4/15 : ℝ)^2*(∫ Q, late b (k+4) Q ∂F.nuP)) :=
      add_le_add (add_le_add le_rfl hhi1) hhi2
    _ = _ := by ring


lemma Bounded.kernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] {f : Y → ℝ} (hf : Bounded f) :
    Bounded (fun x => ∫ y, f y ∂K x) := by
  obtain ⟨mf,M,hM,bf⟩ := hf
  refine ⟨mf.stronglyMeasurable.integral_kernel.measurable, M,hM,?_⟩
  intro x
  simpa using norm_integral_le_of_norm_le_const (Eventually.of_forall bf) (μ := K x)

lemma kernel_transport {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : K ∘ₘ μ = ν) {f : Y → ℝ} (hf : Bounded f) :
    (∫ x, (∫ y, f y ∂K x) ∂μ) = ∫ y, f y ∂ν := by
  calc
    _ = ∫ y, f y ∂(K ∘ₘ μ) := by
      rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp (hf.integrable _)]
      rfl
    _ = _ := by rw [h]

lemma bounded_v : Bounded (fun W => (v W).toReal) := by
  refine ⟨measurable_v.ennreal_toReal, 1, by norm_num, ?_⟩
  intro W
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono ENNReal.one_ne_top tsub_le_self).trans_eq (by simp)

lemma u_real_bounds (Q : PDescriptor) : (1/3 : ℝ) ≤ (u Q).toReal ∧ (u Q).toReal ≤ 2/5 := by
  have hl := ENNReal.toReal_mono (measure_ne_top (law Q) _) Q.property.1
  have hh := ENNReal.toReal_mono (by unfold upper; finiteness : upper ≠ ∞) Q.property.2.1
  norm_num [lower, upper] at hl hh
  exact ⟨hl,hh⟩
lemma v_real_bounds (W : BDescriptor) : (1/3 : ℝ) ≤ (v W).toReal ∧ (v W).toReal ≤ 2/5 := by
  have hl := ENNReal.toReal_mono (ENNReal.sub_ne_top (by simp)) W.property.1
  have hh := ENNReal.toReal_mono (by unfold upper; finiteness : upper ≠ ∞) W.property.2.1
  norm_num [lower, upper] at hl hh
  exact ⟨hl,hh⟩

lemma one_sub_u_real (Q : PDescriptor) : (1-u Q).toReal = 1-(u Q).toReal := by
  rw [ENNReal.toReal_sub_of_le (show u Q ≤ 1 from prob_le_one) ENNReal.one_ne_top]
  simp
lemma one_sub_v_real (W : BDescriptor) : (1-v W).toReal = 1-(v W).toReal := by
  rw [ENNReal.toReal_sub_of_le (show v W ≤ 1 from tsub_le_self) ENNReal.one_ne_top]
  simp

lemma real_completion (F : CommonFlow) : ∀ᵐ Q ∂F.nuP,
    (g Q).toReal = (1-(u Q).toReal) * (∫ W, 1-(v W).toReal ∂F.B Q) := by
  filter_upwards [(common_flow_word_iteration F).2.2] with Q hQ
  rw [hQ, ENNReal.toReal_mul, one_sub_u_real]
  have hi := integral_toReal (μ := F.B Q) (measurable_const.sub measurable_v).aemeasurable
    (Eventually.of_forall (fun W => (ENNReal.sub_ne_top (by simp) : 1-v W ≠ ∞).lt_top))
  simp only [Pi.sub_apply] at hi
  rw [← hi]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall one_sub_v_real

lemma real_row_mass (F : CommonFlow) (Q : PDescriptor) :
    action F (fun _ => 1) Q = (1-(u Q).toReal) * (∫ W, (v W).toReal ∂F.B Q) := by
  rw [weighted_action F (bounded_const 1), one_sub_u_real]
  simp

lemma real_completion_row (F : CommonFlow) : ∀ᵐ Q ∂F.nuP,
    action F (fun _ => 1) Q = 1 - (u Q).toReal - (g Q).toReal := by
  filter_upwards [real_completion F] with Q hQ
  rw [hQ, real_row_mass, integral_sub (integrable_const 1) (bounded_v.integrable _)]
  simp
  ring

def rR (b : Bool) : ℝ := if b then 2/5 else 1/3
def emissionDefectP (b : Bool) (Q : PDescriptor) : ℝ := signR b * ((u Q).toReal-rR b)
def emissionDefectB (b : Bool) (W : BDescriptor) : ℝ := signR b * ((v W).toReal-rR b)
lemma bounded_emissionB (b : Bool) : Bounded (emissionDefectB b) :=
  (bounded_v.sub (bounded_const (rR b))).mul_const (signR b)
lemma emissionP_nonneg (b : Bool) (Q : PDescriptor) : 0 ≤ emissionDefectP b Q := by
  have hb := u_real_bounds Q
  cases b <;> simp [emissionDefectP,signR,rR] <;> linarith
lemma emissionB_nonneg (b : Bool) (W : BDescriptor) : 0 ≤ emissionDefectB b W := by
  have hb := v_real_bounds W
  cases b <;> simp [emissionDefectB,signR,rR] <;> linarith

lemma defect_split (F : CommonFlow) (b : Bool) : ∀ᵐ Q ∂F.nuP,
    defect b Q = (1-rR b)*emissionDefectP b Q +
      (1-(u Q).toReal)*(∫ W, emissionDefectB b W ∂F.B Q) ∧
    defect b Q = (1-rR b)*(∫ W, emissionDefectB b W ∂F.B Q) +
      emissionDefectP b Q*(∫ W, 1-(v W).toReal ∂F.B Q) := by
  filter_upwards [real_completion F] with Q hQ
  unfold defect emissionDefectP emissionDefectB
  rw [integral_const_mul, integral_sub (bounded_v.integrable _) (integrable_const (rR b)),
    integral_sub (integrable_const 1) (bounded_v.integrable _)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [hQ, integral_sub (integrable_const 1) (bounded_v.integrable _)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  cases b <;> norm_num [cR,zR,rR,signR] <;> constructor <;> ring

lemma defect_controls (F : CommonFlow) (b : Bool) : ∀ᵐ Q ∂F.nuP,
    (1-rR b)*emissionDefectP b Q ≤ defect b Q ∧
    (1-rR b)*(∫ W, emissionDefectB b W ∂F.B Q) ≤ defect b Q := by
  filter_upwards [defect_split F b] with Q hQ
  have hy : 0 ≤ ∫ W, emissionDefectB b W ∂F.B Q := integral_nonneg (emissionB_nonneg b)
  have hb : 0 ≤ ∫ W, 1-(v W).toReal ∂F.B Q := by
    apply integral_nonneg; intro W; change 0 ≤ 1-(v W).toReal; have := (v_real_bounds W).2; linarith
  have hu : 0 ≤ 1-(u Q).toReal := by have := (u_real_bounds Q).2; linarith
  constructor
  · rw [hQ.1]; exact le_add_of_nonneg_right (mul_nonneg hu hy)
  · rw [hQ.2]; exact le_add_of_nonneg_right (mul_nonneg (emissionP_nonneg b Q) hb)

lemma variation_control (F : CommonFlow) (b : Bool) :
    (fun Q => -(cR b)*variation F b Q) ≤ᵐ[F.nuP] (fun Q => zR b*defect b Q) := by
  filter_upwards [real_completion_row F, defect_controls F b] with Q hw hc
  have hv : -variation F b Q = emissionDefectP b Q-defect b Q := by
    unfold variation emissionDefectP defect
    rw [hw]
    cases b <;> norm_num [signR,cR,zR,rR] <;> ring
  have hr : 0 ≤ 1-rR b := by cases b <;> norm_num [rR]
  have h := mul_le_mul_of_nonneg_left hc.1 hr
  have hcz : cR b=(1-rR b)^2 ∧ cR b+zR b=1-rR b := by
    cases b <;> norm_num [cR,zR,rR]
  rw [hcz.1]
  have he : (1-rR b)*defect b Q = ((1-rR b)^2+zR b)*defect b Q := by
    rw [← hcz.1,hcz.2]
  rw [he] at h
  rw [show -(1-rR b)^2*variation F b Q = (1-rR b)^2*(-variation F b Q) by ring,hv]
  nlinarith only [h]


lemma Bounded.abs {X : Type*} [MeasurableSpace X] {f : X → ℝ} (hf : Bounded f) :
    Bounded (fun x => |f x|) := by
  obtain ⟨mf,M,hM,hb⟩ := hf
  refine ⟨mf.abs,M,hM,?_⟩
  intro x; simpa [Real.norm_eq_abs] using hb x


end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelSignedAction
