/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelLowerTailRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Eventual endpoint recurrence identifies both original full marginals and flows. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelStabilityConsumers
import Mathlib.Probability.ConditionalProbability

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open NativeBorelCommonFlow NativeBorelEndpointIdentification NativeFullResidual
open NativeConditionalControl.Tail FourthSegmentStoppedLaw
open NativeBorelSignedAction NativeBorelNormalizedStability NativeBorelTVTopology

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelLowerTailRigidity

lemma iterate_sub (F : CommonFlow) {f h : PDescriptor → ℝ}
    (hf : Bounded f) (hh : Bounded h) (n : ℕ) :
    realIterate F (fun Q => f Q - h Q) n =ᵐ[F.nuP]
      fun Q => realIterate F f n Q - realIterate F h n Q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he := ae_action F ih
    filter_upwards [he] with Q hQ
    change action F (realIterate F (fun Q => f Q - h Q) n) Q = _
    rw [hQ, action_sub F (hf.realIterate F n) (hh.realIterate F n)]
    rfl

lemma coordinate_iterates (F : CommonFlow) (k n : ℕ) (i : Letter) :
    (fun Q => (coordinate (k + n) i Q).toReal) =ᵐ[F.nuP]
      realIterate F (fun Q => (coordinate k i Q).toReal) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he := ae_action F ih
    filter_upwards [real_coordinate_step F (k + n) i, he] with Q hQ he
    simpa only [Nat.add_assoc, realIterate] using hQ.trans he

def lowerGap (Q : PDescriptor) : ℝ :=
  (coordinate 3 1 Q).toReal - (2 / 9 : ℝ) ^ 3 * (g Q).toReal

lemma bounded_lowerGap : Bounded lowerGap :=
  (bounded_coordinate 3 1).sub ((bounded_coordinate 0 1).mul_const ((2 / 9 : ℝ) ^ 3))

lemma lowerGap_bound (F : CommonFlow) :
    ∀ᵐ Q ∂F.nuP, 0 ≤ lowerGap Q ∧
      (2 / 9 : ℝ) ^ 3 * defect false Q ≤ lowerGap Q := by
  filter_upwards [late_nonneg F false 3 (by omega), defect_nonneg F false] with Q hl hd
  simp only [late, defect, signR, cR, zR, Bool.false_eq_true, if_false, one_mul] at hl hd ⊢
  simp only [Pi.zero_apply] at hl hd
  unfold lowerGap
  constructor <;> nlinarith

lemma lowerGap_iterates (F : CommonFlow) (n : ℕ) :
    realIterate F lowerGap n =ᵐ[F.nuP]
      fun Q => (coordinate (n + 3) 1 Q).toReal - (2 / 9 : ℝ) ^ 3 * (coordinate n 1 Q).toReal := by
  have he := iterate_sub F (bounded_coordinate 3 1)
    ((bounded_coordinate 0 1).mul_const ((2 / 9 : ℝ) ^ 3)) n
  rw [realIterate_mul] at he
  filter_upwards [he, coordinate_iterates F 3 n 1, coordinate_iterates F 0 n 1]
    with Q hQ h3 h0
  change realIterate F (fun Q => (coordinate 3 1 Q).toReal -
    (2 / 9 : ℝ) ^ 3 * (coordinate 0 1 Q).toReal) n Q = _
  simpa only [Nat.add_comm 3 n, Nat.zero_add] using hQ.trans
    (congrArg₂ (fun a b : ℝ => a - (2 / 9 : ℝ) ^ 3 * b) h3.symm h0.symm)

/-- A single exact lower-root three-return equality forces maximal completion almost everywhere. -/
theorem lower_completion (F : CommonFlow) (n : ℕ)
    (hmean : meanCoordinate F (n + 3) = (2 / 9 : ℝ) ^ 3 * meanCoordinate F n) :
    ∀ᵐ Q ∂F.nuP, (g Q).toReal = 4 / 9 := by
  have hnonneg := (lowerGap_bound F).mono (fun _ h => h.1)
  have hz : (∫ Q, realIterate F lowerGap n Q ∂F.nuP) = 0 := by
    rw [integral_congr_ae (lowerGap_iterates F n),
      integral_sub ((bounded_coordinate (n + 3) 1).integrable _)
        (((bounded_coordinate n 1).integrable _).const_mul ((2 / 9 : ℝ) ^ 3)),
      integral_const_mul]
    exact sub_eq_zero.mpr hmean
  have hl := (integrated_iterate_bounds F bounded_lowerGap hnonneg n).1
  have hm : 0 ≤ ∫ Q, lowerGap Q ∂F.nuP := integral_nonneg_of_ae hnonneg
  have hp : 0 < (1 / 5 : ℝ) ^ n := by positivity
  have hzero : (∫ Q, lowerGap Q ∂F.nuP) = 0 := by rw [hz] at hl; nlinarith
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg
    (bounded_lowerGap.integrable F.nuP)).mp hzero
  filter_upwards [hae, lowerGap_bound F, defect_nonneg F false] with Q hQ hb hd
  simp only [defect, signR, cR, Bool.false_eq_true, if_false, one_mul] at hb hd
  rw [hQ] at hb
  simp only [Pi.zero_apply] at hb hd
  nlinarith

open NativeBorelStabilityConsumers
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle

private lemma descriptor_of_zero_loss (s : ActivePhase) (b : Bool)
    (D : RegularDescriptor s) (h : fullLoss s b D = 0) :
    D = nativeEndpoint s b := by
  apply Subtype.ext
  apply Subtype.ext
  apply Measure.ext
  intro E hE
  have h₁ := directed_event_bound (law D) (native s (endpoint b) : Measure _) E hE
  have h₂ := directed_event_bound (native s (endpoint b) : Measure _) (law D) E hE
  rw [measurable_total_variation_comm] at h₂
  change _ ≤ fullLoss s b D at h₁ h₂
  rw [h] at h₁ h₂
  change law D E = (native s (endpoint b) : Measure _) E
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (law D) E)
    (measure_ne_top (native s (endpoint b) : Measure _) E)).mp
  change (law D).real E = (native s (endpoint b) : Measure _).real E
  linarith

private lemma dirac_of_ae_eq {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure X) [IsProbabilityMeasure μ] (x : X)
    (h : ∀ᵐ y ∂μ, y = x) : μ = Measure.dirac x := by
  classical
  have he := Measure.ae_mem_finset_iff.mp
    (show ∀ᵐ y ∂μ, y ∈ ({x} : Finset X) from h.mono (fun y hy => by simp [hy]))
  simp only [Finset.sum_singleton] at he
  have hm := congrArg (fun ν : Measure X => ν Set.univ) he
  simp only [measure_univ, Measure.smul_apply, smul_eq_mul, mul_one] at hm
  rw [← hm, one_smul] at he
  exact he

/-- Exact lower-root completion determines both entire marginals and the actual
original B and A joint measures. -/
theorem lower_native_flow (F : CommonFlow) (n : ℕ)
    (hmean : meanCoordinate F (n + 3) = (2 / 9 : ℝ) ^ 3 * meanCoordinate F n) :
    F.nuP = Measure.dirac (nativeEndpoint .p false) ∧
    F.nuB = Measure.dirac (nativeEndpoint .beta false) ∧
    F.GammaB = Measure.dirac (nativeEndpoint .p false, nativeEndpoint .beta false) ∧
    F.GammaA = Measure.dirac (nativeEndpoint .beta false, nativeEndpoint .p false) := by
  have hd : defect false =ᵐ[F.nuP] fun _ => 0 := by
    filter_upwards [lower_completion F n hmean] with Q hQ
    simp [defect, signR, cR, hQ]
  have hi : (∫ Q, defect false Q ∂F.nuP) = 0 := by
    rw [integral_congr_ae hd]
    simp
  have hp := integrated_p_loss F false
  have hb := integrated_b_loss F false
  rw [hi, mul_zero] at hp hb
  have hzp : ∀ᵐ Q ∂F.nuP, fullLoss .p false Q = 0 := by
    apply (integral_eq_zero_iff_of_nonneg
      (fun _ => ENNReal.toReal_nonneg) (p_loss_integrable F false)).mp
    exact le_antisymm hp (integral_nonneg (fun _ => ENNReal.toReal_nonneg))
  have hzb : ∀ᵐ W ∂F.nuB, fullLoss .beta false W = 0 := by
    apply (integral_eq_zero_iff_of_nonneg
      (fun _ => ENNReal.toReal_nonneg)
      ((bounded_target_loss .beta (endpoint false)).integrable F.nuB)).mp
    exact le_antisymm hb (integral_nonneg (fun _ => ENNReal.toReal_nonneg))
  have hP := hzp.mono (fun Q hQ => descriptor_of_zero_loss .p false Q hQ)
  have hB := hzb.mono (fun W hW => descriptor_of_zero_loss .beta false W hW)
  refine ⟨dirac_of_ae_eq F.nuP _ hP, dirac_of_ae_eq F.nuB _ hB, ?_, ?_⟩
  · apply dirac_of_ae_eq
    have h₁ : ∀ᵐ x ∂F.GammaB, x.1 = nativeEndpoint .p false :=
      ae_of_ae_map measurable_fst.aemeasurable
        (show ∀ᵐ Q ∂F.GammaB.fst, Q = nativeEndpoint .p false from
          F.marginB₁.symm ▸ hP)
    have h₂ : ∀ᵐ x ∂F.GammaB, x.2 = nativeEndpoint .beta false :=
      ae_of_ae_map measurable_snd.aemeasurable
        (show ∀ᵐ W ∂F.GammaB.snd, W = nativeEndpoint .beta false from
          F.marginB₂.symm ▸ hB)
    filter_upwards [h₁, h₂] with x hx₁ hx₂
    exact Prod.ext hx₁ hx₂
  · apply dirac_of_ae_eq
    have h₁ : ∀ᵐ x ∂F.GammaA, x.1 = nativeEndpoint .beta false :=
      ae_of_ae_map measurable_fst.aemeasurable
        (show ∀ᵐ W ∂F.GammaA.fst, W = nativeEndpoint .beta false from
          F.marginA₁.symm ▸ hB)
    have h₂ : ∀ᵐ x ∂F.GammaA, x.2 = nativeEndpoint .p false :=
      ae_of_ae_map measurable_snd.aemeasurable
        (show ∀ᵐ Q ∂F.GammaA.snd, Q = nativeEndpoint .p false from
          F.marginA₂.symm ▸ hP)
    filter_upwards [h₁, h₂] with x hx₁ hx₂
    exact Prod.ext hx₁ hx₂

private lemma native_barycenter_support (s : ActivePhase) (b : Bool)
    (μ : Measure (RegularDescriptor s)) [IsProbabilityMeasure μ]
    (hbox : ∀ᵐ D ∂μ, EndpointBox D)
    (hbar : (lawKernel s) ∘ₘ μ = law (nativeEndpoint s b)) :
    ∀ᵐ D ∂μ, D = nativeEndpoint s b := by
  let E : Set (ValidTail s) := match s with | .p => Ep | .beta => Eb
  have hE : MeasurableSet E := (Set.to_countable _).measurableSet
  have hformula : ∀ᵐ D ∂μ, fullLoss s b D =
      signR b * ((native s (endpoint b) : Measure _).real E - (law D).real E) := by
    filter_upwards [hbox] with D hD
    cases s
    · exact p_event_loss D hD b
    · exact b_loss_event D hD b
  have hevent : (∫ D, (law D).real E ∂μ) =
      (native s (endpoint b) : Measure _).real E := by
    have hi := congrArg (fun ν : Measure (ValidTail s) => (ν E).toReal) hbar
    change ((μ.bind (lawKernel s)) E).toReal = _ at hi
    rw [Measure.bind_apply hE (lawKernel s).aemeasurable] at hi
    change (∫⁻ D, law D E ∂μ).toReal =
      (native s (endpoint b) : Measure _).real E at hi
    exact (integral_toReal (f := fun D : RegularDescriptor s => law D E)
      (((Measure.measurable_coe hE).comp (measurable_law s)).aemeasurable)
      (ae_of_all _ (fun D => (measure_ne_top (law D) E).lt_top))).trans hi
  have hz : (∫ D, fullLoss s b D ∂μ) = 0 := by
    rw [integral_congr_ae hformula, integral_const_mul,
      integral_sub (integrable_const _) ((bounded_event_real s E hE).integrable μ)]
    simp [hevent]
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ => ENNReal.toReal_nonneg)
    ((bounded_target_loss s (endpoint b)).integrable μ)).mp hz
  exact hae.mono (fun D hD => descriptor_of_zero_loss s b D hD)

/-- The upper native singletons are absorbing for both original directional kernels. -/
theorem upper_native_successors (F : CommonFlow) :
    (∀ᵐ Q ∂F.nuP, Q = nativeEndpoint .p true →
      ∀ᵐ W ∂F.B Q, W = nativeEndpoint .beta true) ∧
    (∀ᵐ W ∂F.nuB, W = nativeEndpoint .beta true →
      ∀ᵐ Q ∂F.A W, Q = nativeEndpoint .p true) := by
  constructor
  · filter_upwards [(common_flow_upper_endpoint_limits F).1,
      common_flow_surviving_transitions F] with Q hd ht
    intro hn
    have hq : NativeBorelSuperharmonic.q F Q ≠ 0 := by
      rw [hd.1, if_pos hn]
      norm_num [endpointCompletion]
    exact (ht hq).2.2.mono (fun _ hW => hW.1)
  · have hbox := Measure.ae_ae_of_ae_comp (κ := F.A) ((margin_A F).symm ▸ F.boxP)
    filter_upwards [F.normalizedA, hbox] with W hn hW
    intro he
    apply native_barycenter_support .p true (F.A W) hW
    rw [← hn, he, native_endpoint_residualA]

/-- Both original upper native masses coincide, and both joint measures have no
edges between the upper singleton and its complement. -/
theorem upper_native_edges (F : CommonFlow) :
    F.nuP {nativeEndpoint .p true} = F.nuB {nativeEndpoint .beta true} ∧
    (∀ᵐ x ∂F.GammaB, x.1 = nativeEndpoint .p true ↔ x.2 = nativeEndpoint .beta true) ∧
    (∀ᵐ x ∂F.GammaA, x.1 = nativeEndpoint .beta true ↔ x.2 = nativeEndpoint .p true) := by
  let p := nativeEndpoint .p true
  let b := nativeEndpoint .beta true
  have hmB : MeasurableSet {x : PDescriptor × BDescriptor | x.1 = p → x.2 = b} := by
    simp only [imp_iff_not_or]
    exact ((measurableSet_singleton p).preimage measurable_fst).compl.union
      ((measurableSet_singleton b).preimage measurable_snd)
  have hmA : MeasurableSet {x : BDescriptor × PDescriptor | x.1 = b → x.2 = p} := by
    simp only [imp_iff_not_or]
    exact ((measurableSet_singleton b).preimage measurable_fst).compl.union
      ((measurableSet_singleton p).preimage measurable_snd)
  have hB : ∀ᵐ x ∂F.GammaB, x.1 = p → x.2 = b := by
    rw [← F.disintegrateB.disintegrate, F.marginB₁]
    apply Measure.ae_compProd_of_ae_ae hmB
    filter_upwards [(upper_native_successors F).1] with Q hQ
    by_cases he : Q = p
    · exact (hQ he).mono (fun W hW _ => hW)
    · exact ae_of_all _ (fun _ h => False.elim (he h))
  have hA : ∀ᵐ x ∂F.GammaA, x.1 = b → x.2 = p := by
    rw [← F.disintegrateA.disintegrate, F.marginA₁]
    apply Measure.ae_compProd_of_ae_ae hmA
    filter_upwards [(upper_native_successors F).2] with W hW
    by_cases he : W = b
    · exact (hW he).mono (fun Q hQ _ => hQ)
    · exact ae_of_all _ (fun _ h => False.elim (he h))
  have hleB : F.nuP {p} ≤ F.nuB {b} := by
    rw [← F.marginB₁, ← F.marginB₂, Measure.fst_apply (measurableSet_singleton p),
      Measure.snd_apply (measurableSet_singleton b)]
    exact measure_mono_ae hB
  have hleA : F.nuB {b} ≤ F.nuP {p} := by
    rw [← F.marginA₁, ← F.marginA₂, Measure.fst_apply (measurableSet_singleton b),
      Measure.snd_apply (measurableSet_singleton p)]
    exact measure_mono_ae hA
  have he : F.nuP {p} = F.nuB {b} := le_antisymm hleB hleA
  refine ⟨he, ?_, ?_⟩
  · have hge : F.GammaB (Prod.snd ⁻¹' {b}) ≤ F.GammaB (Prod.fst ⁻¹' {p}) := by
      rw [← Measure.snd_apply (measurableSet_singleton b),
        ← Measure.fst_apply (measurableSet_singleton p), F.marginB₁, F.marginB₂, he]
    have hx := ae_eq_of_ae_subset_of_measure_ge hB hge
      (((measurableSet_singleton p).preimage measurable_fst).nullMeasurableSet)
      (measure_ne_top _ _)
    exact hx.mono (fun _ h => Iff.of_eq h)
  · have hge : F.GammaA (Prod.snd ⁻¹' {p}) ≤ F.GammaA (Prod.fst ⁻¹' {b}) := by
      rw [← Measure.snd_apply (measurableSet_singleton p),
        ← Measure.fst_apply (measurableSet_singleton b), F.marginA₁, F.marginA₂, he]
    have hx := ae_eq_of_ae_subset_of_measure_ge hA hge
      (((measurableSet_singleton b).preimage measurable_fst).nullMeasurableSet)
      (measure_ne_top _ _)
    exact hx.mono (fun _ h => Iff.of_eq h)

private lemma restrict_compProd_left {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) [SFinite μ]
    (K : Kernel X Y) [IsSFiniteKernel K] (S : Set X) (hS : MeasurableSet S) :
    μ.restrict S ⊗ₘ K = (μ ⊗ₘ K).restrict (Prod.fst ⁻¹' S) := by
  change (Kernel.const Unit (μ.restrict S) ⊗ₖ Kernel.prodMkLeft Unit K) () = _
  rw [← Kernel.restrict_const hS, Kernel.compProd_restrict_left hS,
    Kernel.restrict_apply _ (hS.prod MeasurableSet.univ)]
  congr 1
  ext x
  simp

private lemma snd_restrict_complement {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (γ : Measure (X × Y)) (a : X) (b : Y)
    (h : ∀ᵐ x ∂γ, x.1 = a ↔ x.2 = b) :
    (γ.restrict (Prod.fst ⁻¹' {a})ᶜ).snd = γ.snd.restrict {b}ᶜ := by
  ext E hE
  rw [Measure.snd_apply hE, Measure.restrict_apply (hE.preimage measurable_snd),
    Measure.restrict_apply hE, Measure.snd_apply (hE.inter (measurableSet_singleton b).compl)]
  apply measure_congr
  filter_upwards [h] with x hx
  change (x.2 ∈ E ∧ x.1 ≠ a) = (x.2 ∈ E ∧ x.2 ≠ b)
  exact propext (and_congr_right (fun _ => not_congr hx))

/-- Removing the actual upper singleton subflows and normalizing their complements
preserves both full equations, both boxes and the same original kernels. -/
theorem upper_excision (F : CommonFlow)
    (hm : F.nuP {nativeEndpoint .p true} < 1) :
    ∃ R : CommonFlow,
      R.nuP = F.nuP[|{nativeEndpoint .p true}ᶜ] ∧
      R.nuB = F.nuB[|{nativeEndpoint .beta true}ᶜ] ∧
      R.GammaB = (1 - F.nuP {nativeEndpoint .p true})⁻¹ •
        F.GammaB.restrict (Prod.fst ⁻¹' {nativeEndpoint .p true})ᶜ ∧
      R.GammaA = (1 - F.nuP {nativeEndpoint .p true})⁻¹ •
        F.GammaA.restrict (Prod.fst ⁻¹' {nativeEndpoint .beta true})ᶜ ∧
      R.B = F.B ∧ R.A = F.A := by
  let p := nativeEndpoint .p true
  let b := nativeEndpoint .beta true
  let w : ℝ≥0∞ := 1 - F.nuP {p}
  let νP := F.nuP[|{p}ᶜ]
  let νB := F.nuB[|{b}ᶜ]
  have he := upper_native_edges F
  have hw : w ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hm)
  have hp : F.nuP {p}ᶜ = w := by
    rw [measure_compl (measurableSet_singleton p) (measure_ne_top _ _), measure_univ]
  have hb : F.nuB {b}ᶜ = w := by
    rw [measure_compl (measurableSet_singleton b) (measure_ne_top _ _), measure_univ,
      ← he.1]
  have : IsProbabilityMeasure νP := cond_isProbabilityMeasure (hp ▸ hw)
  have : IsProbabilityMeasure νB := cond_isProbabilityMeasure (hb ▸ hw)
  have hFB : F.nuP ⊗ₘ F.B = F.GammaB := by
    rw [← F.marginB₁]
    exact F.disintegrateB.disintegrate
  have hFA : F.nuB ⊗ₘ F.A = F.GammaA := by
    rw [← F.marginA₁]
    exact F.disintegrateA.disintegrate
  have hΓB : νP ⊗ₘ F.B = w⁻¹ • F.GammaB.restrict (Prod.fst ⁻¹' {p})ᶜ := by
    change (F.nuP[|{p}ᶜ]) ⊗ₘ F.B = _
    rw [ProbabilityTheory.cond, hp, Measure.compProd_smul_left,
      restrict_compProd_left _ _ _ (measurableSet_singleton p).compl, hFB]
    rfl
  have hΓA : νB ⊗ₘ F.A = w⁻¹ • F.GammaA.restrict (Prod.fst ⁻¹' {b})ᶜ := by
    change (F.nuB[|{b}ᶜ]) ⊗ₘ F.A = _
    rw [ProbabilityTheory.cond, hb, Measure.compProd_smul_left,
      restrict_compProd_left _ _ _ (measurableSet_singleton b).compl, hFA]
    rfl
  have hsB : (νP ⊗ₘ F.B).snd = νB := by
    rw [hΓB, Measure.snd, Measure.map_smul _ measurable_snd.aemeasurable]
    change w⁻¹ • (F.GammaB.restrict (Prod.fst ⁻¹' {p})ᶜ).snd = _
    rw [snd_restrict_complement _ p b he.2.1, F.marginB₂]
    change _ = F.nuB[|{b}ᶜ]
    rw [ProbabilityTheory.cond, hb]
  have hsA : (νB ⊗ₘ F.A).snd = νP := by
    rw [hΓA, Measure.snd, Measure.map_smul _ measurable_snd.aemeasurable]
    change w⁻¹ • (F.GammaA.restrict (Prod.fst ⁻¹' {b})ᶜ).snd = _
    rw [snd_restrict_complement _ b p he.2.2, F.marginA₂]
    change _ = F.nuP[|{p}ᶜ]
    rw [ProbabilityTheory.cond, hp]
  let R : CommonFlow := {
    nuP := νP
    nuB := νB
    probP := inferInstance
    probB := inferInstance
    GammaB := νP ⊗ₘ F.B
    GammaA := νB ⊗ₘ F.A
    probGammaB := inferInstance
    probGammaA := inferInstance
    B := F.B
    A := F.A
    markovB := inferInstance
    markovA := inferInstance
    disintegrateB := ⟨by rw [Measure.fst_compProd]⟩
    disintegrateA := ⟨by rw [Measure.fst_compProd]⟩
    marginB₁ := Measure.fst_compProd _ _
    marginB₂ := hsB
    marginA₁ := Measure.fst_compProd _ _
    marginA₂ := hsA
    normalizedB := cond_absolutelyContinuous.ae_le F.normalizedB
    normalizedA := cond_absolutelyContinuous.ae_le F.normalizedA
    boxP := cond_absolutelyContinuous.ae_le F.boxP
    boxB := cond_absolutelyContinuous.ae_le F.boxB }
  exact ⟨R, rfl, rfl, hΓB, hΓA, rfl, rfl⟩

private lemma singleton_complement_decomposition {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure X) [IsProbabilityMeasure μ] (a : X)
    (hm : μ {a} < 1) :
    μ = (1 - μ {a}) • μ[|{a}ᶜ] + μ {a} • Measure.dirac a := by
  rw [ProbabilityTheory.cond,
    measure_compl (measurableSet_singleton a) (measure_ne_top _ _), measure_univ,
    smul_smul, ENNReal.mul_inv_cancel (ne_of_gt (tsub_pos_iff_lt.mpr hm))
      (ENNReal.sub_ne_top (by simp)), one_smul, ← Measure.restrict_singleton]
  exact (μ.restrict_compl_add_restrict (measurableSet_singleton a)).symm

private lemma isolated_joint_decomposition {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (γ : Measure (X × Y)) (a : X) (b : Y)
    (h : ∀ᵐ x ∂γ, x.1 = a ↔ x.2 = b) :
    γ = γ.restrict (Prod.fst ⁻¹' {a})ᶜ + γ.fst {a} • Measure.dirac (a, b) := by
  have he : (Prod.fst ⁻¹' {a}) =ᵐ[γ] ({(a, b)} : Set (X × Y)) := by
    filter_upwards [h] with x hx
    change (x.1 = a) = (x = (a, b))
    exact propext ⟨fun ha => Prod.ext ha (hx.mp ha), fun hp => congrArg Prod.fst hp⟩
  have hm : γ {(a, b)} = γ.fst {a} := by
    rw [Measure.fst_apply (measurableSet_singleton a)]
    exact measure_congr he.symm
  have hr : γ.restrict (Prod.fst ⁻¹' {a}) = γ.fst {a} • Measure.dirac (a, b) := by
    rw [Measure.restrict_congr_set he, Measure.restrict_singleton, hm]
  rw [← hr]
  exact (γ.restrict_compl_add_restrict
    ((measurableSet_singleton a).preimage measurable_fst)).symm

/-- The same normalized complement gives simultaneous exact decompositions of
all four original measures with the common upper-native coefficient. -/
theorem upper_complement_decomposition (F : CommonFlow)
    (hm : F.nuP {nativeEndpoint .p true} < 1) :
    ∃ R : CommonFlow,
      R.nuP {nativeEndpoint .p true} = 0 ∧
      F.nuP = (1 - F.nuP {nativeEndpoint .p true}) • R.nuP +
        F.nuP {nativeEndpoint .p true} • Measure.dirac (nativeEndpoint .p true) ∧
      F.nuB = (1 - F.nuP {nativeEndpoint .p true}) • R.nuB +
        F.nuP {nativeEndpoint .p true} • Measure.dirac (nativeEndpoint .beta true) ∧
      F.GammaB = (1 - F.nuP {nativeEndpoint .p true}) • R.GammaB +
        F.nuP {nativeEndpoint .p true} •
          Measure.dirac (nativeEndpoint .p true, nativeEndpoint .beta true) ∧
      F.GammaA = (1 - F.nuP {nativeEndpoint .p true}) • R.GammaA +
        F.nuP {nativeEndpoint .p true} •
          Measure.dirac (nativeEndpoint .beta true, nativeEndpoint .p true) := by
  obtain ⟨R, hp, hb, hΓB, hΓA, _, _⟩ := upper_excision F hm
  have he := upper_native_edges F
  have hw : 1 - F.nuP {nativeEndpoint .p true} ≠ 0 :=
    ne_of_gt (tsub_pos_iff_lt.mpr hm)
  have hf : 1 - F.nuP {nativeEndpoint .p true} ≠ ∞ := ENNReal.sub_ne_top (by simp)
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp]
    simp [ProbabilityTheory.cond, Measure.restrict_apply]
  · rw [hp]
    exact singleton_complement_decomposition F.nuP _ hm
  · rw [hb, he.1]
    exact singleton_complement_decomposition F.nuB _ (he.1 ▸ hm)
  · rw [hΓB, smul_smul, ENNReal.mul_inv_cancel hw hf, one_smul,
      ← F.marginB₁]
    exact isolated_joint_decomposition F.GammaB _ _ he.2.1
  · rw [hΓA, smul_smul, ENNReal.mul_inv_cancel hw hf, one_smul, he.1,
      ← F.marginA₁]
    exact isolated_joint_decomposition F.GammaA _ _ he.2.2

private lemma recurrence_lower_three_return (d : ℕ → ℝ) (N : ℕ)
    (hrec : ∀ n ≥ N, d (n + 2) - (2 / 9 + 6 / 25 : ℝ) * d (n + 1) +
      (2 / 9 : ℝ) * (6 / 25) * d n = 0)
    (hlim : Tendsto (fun n => d n / (6 / 25 : ℝ) ^ n) atTop (𝓝 0)) :
    d (N + 3) = (2 / 9 : ℝ) ^ 3 * d N := by
  let w : ℕ → ℝ := fun n =>
    (d (n + 1) - (2 / 9 : ℝ) * d n) / (6 / 25 : ℝ) ^ n
  have hstep (n : ℕ) (hn : N ≤ n) : w (n + 1) = w n := by
    have hr := hrec n hn
    dsimp [w]
    rw [pow_succ]
    field_simp
    nlinarith
  have hw (k : ℕ) : w (N + k) = w N := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show N + (k + 1) = (N + k) + 1 by omega, hstep (N + k) (by omega), ih]
  have hlimw : Tendsto w atTop (𝓝 0) := by
    have hshift := hlim.comp (tendsto_add_atTop_nat 1)
    have he : w = fun n =>
        (6 / 25 : ℝ) * (d (n + 1) / (6 / 25 : ℝ) ^ (n + 1)) -
          (2 / 9 : ℝ) * (d n / (6 / 25 : ℝ) ^ n) := by
      funext n
      dsimp [w]
      rw [pow_succ]
      field_simp
    rw [he]
    simpa using (hshift.const_mul (6 / 25 : ℝ)).sub (hlim.const_mul (2 / 9 : ℝ))
  have htail : Tendsto (fun k => w (N + k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.add_comm] using hlimw.comp (tendsto_add_atTop_nat N)
  have hw0 : w N = 0 := by
    simp only [hw] at htail
    exact tendsto_nhds_unique tendsto_const_nhds htail
  have hz (k : ℕ) : d (N + k + 1) = (2 / 9 : ℝ) * d (N + k) := by
    have hi : w (N + k) = 0 := (hw k).trans hw0
    dsimp [w] at hi
    exact sub_eq_zero.mp ((div_eq_zero_iff).mp hi |>.resolve_right (by positivity))
  have h₀ := hz 0
  have h₁ := hz 1
  have h₂ := hz 2
  simp only [Nat.add_zero] at h₀
  norm_num at h₁ h₂ ⊢
  nlinarith

private lemma zero_upper_mean_limit (F : CommonFlow)
    (hm : F.nuP {nativeEndpoint .p true} = 0) :
    Tendsto (fun n => meanCoordinate F n / (6 / 25 : ℝ) ^ n) atTop (𝓝 0) := by
  have ht := (common_flow_upper_endpoint_limits F).2.2
  rw [hm, mul_zero] at ht
  have hr := ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp ht
  have he (n : ℕ) :
      ((∫⁻ Q, coordinate n 1 Q ∂F.nuP) / endpointRate ^ n).toReal =
        meanCoordinate F n / (6 / 25 : ℝ) ^ n := by
    rw [ENNReal.toReal_div, ENNReal.toReal_pow, ← integral_toReal
      (f := fun Q => coordinate n 1 Q) (measurable_coordinate n 1).aemeasurable
      (ae_of_all _ (fun Q => (measure_ne_top (law Q) _).lt_top))]
    norm_num [endpointRate, meanCoordinate]
  simpa only [Function.comp_def, he, ENNReal.toReal_zero] using hr

private lemma mean_decomposition (F R : CommonFlow) (m w : ℝ≥0∞)
    (hm : m ≠ ∞) (hw : w ≠ ∞)
    (hp : F.nuP = w • R.nuP + m • Measure.dirac (nativeEndpoint .p true)) (n : ℕ) :
    meanCoordinate F n = w.toReal * meanCoordinate R n +
      m.toReal * ((9 / 25 : ℝ) * (6 / 25 : ℝ) ^ n) := by
  unfold meanCoordinate
  rw [hp, integral_add_measure
    (((bounded_coordinate n 1).integrable R.nuP).smul_measure hw)
    (((bounded_coordinate n 1).integrable
      (Measure.dirac (nativeEndpoint .p true))).smul_measure hm),
    integral_smul_measure, integral_smul_measure, integral_dirac]
  have hn : (coordinate n 1 (nativeEndpoint .p true)).toReal = cR true * zR true ^ n :=
    native_marker_real true n
  rw [hn]
  simp [cR, zR, smul_eq_mul]

private lemma upper_native_flow (F : CommonFlow)
    (hm : F.nuP {nativeEndpoint .p true} = 1) :
    F.nuP = Measure.dirac (nativeEndpoint .p true) ∧
    F.nuB = Measure.dirac (nativeEndpoint .beta true) ∧
    F.GammaB = Measure.dirac (nativeEndpoint .p true, nativeEndpoint .beta true) ∧
    F.GammaA = Measure.dirac (nativeEndpoint .beta true, nativeEndpoint .p true) := by
  have hP : ∀ᵐ Q ∂F.nuP, Q = nativeEndpoint .p true := by
    rw [ae_iff]
    change F.nuP {nativeEndpoint .p true}ᶜ = 0
    rw [measure_compl (measurableSet_singleton _) (measure_ne_top _ _), measure_univ, hm]
    simp
  have hB : ∀ᵐ W ∂F.nuB, W = nativeEndpoint .beta true := by
    rw [ae_iff]
    change F.nuB {nativeEndpoint .beta true}ᶜ = 0
    rw [measure_compl (measurableSet_singleton _) (measure_ne_top _ _), measure_univ,
      ← (upper_native_edges F).1, hm]
    simp
  refine ⟨dirac_of_ae_eq F.nuP _ hP, dirac_of_ae_eq F.nuB _ hB, ?_, ?_⟩
  · apply dirac_of_ae_eq
    have h₁ : ∀ᵐ x ∂F.GammaB, x.1 = nativeEndpoint .p true :=
      ae_of_ae_map measurable_fst.aemeasurable (F.marginB₁.symm ▸ hP)
    have h₂ : ∀ᵐ x ∂F.GammaB, x.2 = nativeEndpoint .beta true :=
      ae_of_ae_map measurable_snd.aemeasurable (F.marginB₂.symm ▸ hB)
    filter_upwards [h₁, h₂] with x hx₁ hx₂
    exact Prod.ext hx₁ hx₂
  · apply dirac_of_ae_eq
    have h₁ : ∀ᵐ x ∂F.GammaA, x.1 = nativeEndpoint .beta true :=
      ae_of_ae_map measurable_fst.aemeasurable (F.marginA₁.symm ▸ hB)
    have h₂ : ∀ᵐ x ∂F.GammaA, x.2 = nativeEndpoint .p true :=
      ae_of_ae_map measurable_snd.aemeasurable (F.marginA₂.symm ▸ hP)
    filter_upwards [h₁, h₂] with x hx₁ hx₂
    exact Prod.ext hx₁ hx₂

/-- Eventual endpoint recurrence determines both original full marginals and both
original full directional flows, with one common upper-endpoint coefficient. -/
theorem recurrence_native_flow (F : CommonFlow) (N : ℕ)
    (hrec : ∀ n ≥ N,
      meanCoordinate F (n + 2) - (2 / 9 + 6 / 25 : ℝ) * meanCoordinate F (n + 1) +
        (2 / 9 : ℝ) * (6 / 25) * meanCoordinate F n = 0) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      F.nuP = ENNReal.ofReal (1 - θ) • Measure.dirac (nativeEndpoint .p false) +
        ENNReal.ofReal θ • Measure.dirac (nativeEndpoint .p true) ∧
      F.nuB = ENNReal.ofReal (1 - θ) • Measure.dirac (nativeEndpoint .beta false) +
        ENNReal.ofReal θ • Measure.dirac (nativeEndpoint .beta true) ∧
      F.GammaB = ENNReal.ofReal (1 - θ) •
          Measure.dirac (nativeEndpoint .p false, nativeEndpoint .beta false) +
        ENNReal.ofReal θ • Measure.dirac (nativeEndpoint .p true, nativeEndpoint .beta true) ∧
      F.GammaA = ENNReal.ofReal (1 - θ) •
          Measure.dirac (nativeEndpoint .beta false, nativeEndpoint .p false) +
        ENNReal.ofReal θ • Measure.dirac (nativeEndpoint .beta true, nativeEndpoint .p true) := by
  let m := F.nuP {nativeEndpoint .p true}
  have hle : m ≤ 1 := prob_le_one
  have hfinite : m ≠ ∞ := measure_ne_top _ _
  have hreal : m.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) hle
  have hcoef : ENNReal.ofReal (1 - m.toReal) = 1 - m := by
    rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal hfinite]
  refine ⟨m.toReal, ENNReal.toReal_nonneg, hreal, ?_⟩
  rw [hcoef, ENNReal.ofReal_toReal hfinite]
  by_cases hm : m = 1
  · have hf := upper_native_flow F hm
    simpa [hm] using hf
  · have hlt : m < 1 := lt_of_le_of_ne hle hm
    obtain ⟨R, hz, hp, hb, hΓB, hΓA⟩ := upper_complement_decomposition F hlt
    have hw : (1 - m).toReal ≠ 0 := by
      apply ENNReal.toReal_ne_zero.mpr
      exact ⟨ne_of_gt (tsub_pos_iff_lt.mpr hlt), ENNReal.sub_ne_top (by simp)⟩
    have hd (n : ℕ) := mean_decomposition F R m (1 - m) hfinite (ENNReal.sub_ne_top (by simp)) hp n
    have hRrec : ∀ n ≥ N,
        meanCoordinate R (n + 2) - (2 / 9 + 6 / 25 : ℝ) * meanCoordinate R (n + 1) +
          (2 / 9 : ℝ) * (6 / 25) * meanCoordinate R n = 0 := by
      intro n hn
      have hr := hrec n hn
      rw [hd (n + 2), hd (n + 1), hd n] at hr
      simp only [pow_succ] at hr
      have he : (1 - m).toReal *
          (meanCoordinate R (n + 2) - (2 / 9 + 6 / 25 : ℝ) * meanCoordinate R (n + 1) +
            (2 / 9 : ℝ) * (6 / 25) * meanCoordinate R n) = 0 := by
        convert hr using 1
        ring
      exact (mul_eq_zero.mp he).resolve_left hw
    have hn := recurrence_lower_three_return (meanCoordinate R) N hRrec
      (zero_upper_mean_limit R hz)
    obtain ⟨hrp, hrb, hrΓB, hrΓA⟩ := lower_native_flow R N hn
    exact ⟨hp.trans (by rw [hrp]), hb.trans (by rw [hrb]),
      hΓB.trans (by rw [hrΓB]), hΓA.trans (by rw [hrΓA])⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeBorelLowerTailRigidity
