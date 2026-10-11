/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeClampedCompleteTable
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeClampedCompleteTable
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original closed acquired supports give a normalized clamped complete table. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.CompleteTailGeometricSurvival

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeClampedCompleteTable
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal BigOperators
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeObserverJointLaw NativeFullResidual
open NativeInstalledFullLaw NativeStoppedTailRegeneration NativeEmissionClipping
open NativePaidHistoryCommonRowLimits NativePaidHistoryCommonRowRisks ConstantSuspensionSeparator
open CompleteTailWeightedDistortion CompleteTailGeometricSurvival NativePaidHistoryCommonRow
open NativeConditionalControl.DepthLaw
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
universe u
variable {Z : Type u} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

private theorem support_sum (p : PMF Z) (f : Z → ℝ)
    (hf : ∀ z, z ∉ p.support → f z = 0) :
    ∑ z : p.support, f z = ∑ z : Z, f z := by
  rw [Finset.sum_set_coe]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro z _ hz
  exact hf z (by simpa using hz)

private theorem pmf_sum_real (p : PMF Z) : ∑ z, (p z).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun z _ => p.apply_ne_top z)]
  have h : ∑ z, p z = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h]; norm_num

private theorem closed_sum (p q : PMF Z) (U : Z → PMF Z)
    (hc : ∀ x ∈ p.support, ∀ y ∈ (U x).support, y ∈ q.support)
    (x : p.support) (f : Z → ℝ) :
    (∑ y : q.support, (U x y).toReal*f y) = ∑ y : Z, (U x y).toReal*f y := by
  apply support_sum q (fun y : Z => (U x y).toReal * f y)
  intro y hy
  have he : U x y = 0 := by
    by_contra h
    exact hy (hc x x.property y ((PMF.mem_support_iff _ _).mpr h))
  simp [he]

private def table (M : Observer Z) (e : InstalledEmitter M) (pi tau : PMF Z)
    (hB : pi.bind (M.update (.read 1)) = tau)
    (hA : tau.bind (M.update (.read 0)) = pi)
    (hX : ∀ z ∈ pi.support, (M.project z).control = .fourth (.active .p))
    (hY : ∀ z ∈ tau.support, (M.project z).control = .fourth (.active .beta))
    (hcB : ∀ x ∈ pi.support, ∀ y ∈ (M.update (.read 1) x).support, y ∈ tau.support)
    (hcA : ∀ y ∈ tau.support, ∀ x ∈ (M.update (.read 0) y).support, x ∈ pi.support) :
    RegularTable pi.support tau.support where
  pi x := (pi x).toReal
  tau y := (tau y).toReal
  B x y := (M.update (.read 1) x y).toReal
  A y x := (M.update (.read 0) y x).toReal
  u x := clampEmission (e.emit x (some (.read 0))).toReal
  v y := clampEmission (e.emit y (some (.read 0))).toReal
  pi_nonneg _ := ENNReal.toReal_nonneg
  tau_nonneg _ := ENNReal.toReal_nonneg
  pi_sum := by
    rw [support_sum pi (fun z : Z => (pi z).toReal) (by intro z hz; simp [(pi.apply_eq_zero_iff z).mpr hz])]
    exact pmf_sum_real pi
  tau_sum := by
    rw [support_sum tau (fun z : Z => (tau z).toReal) (by intro z hz; simp [(tau.apply_eq_zero_iff z).mpr hz])]
    exact pmf_sum_real tau
  B_nonneg _ _ := ENNReal.toReal_nonneg
  A_nonneg _ _ := ENNReal.toReal_nonneg
  B_sum x := by
    have h := closed_sum pi tau (M.update (.read 1)) hcB x (fun _ => 1)
    simp only [mul_one] at h
    rw [h]; exact pmf_sum_real _
  A_sum y := by
    have h := closed_sum tau pi (M.update (.read 0)) hcA y (fun _ => 1)
    simp only [mul_one] at h
    rw [h]; exact pmf_sum_real _
  pi_B y := by
    rw [support_sum pi (fun z : Z => (pi z).toReal * (M.update (.read 1) z y).toReal) (by intro z hz; simp [(pi.apply_eq_zero_iff z).mpr hz])]
    rw [← bind_real pi (M.update (.read 1)) y,hB]
  tau_A x := by
    rw [support_sum tau (fun z : Z => (tau z).toReal * (M.update (.read 0) z x).toReal) (by intro z hz; simp [(tau.apply_eq_zero_iff z).mpr hz])]
    rw [← bind_real tau (M.update (.read 0)) x,hA]
  u_box x := clamp_box _
  v_box y := clamp_box _
  Q x := rawTailLaw M (clampedEmitter M e) .p x
  W y := rawTailLaw M (clampedEmitter M e) .beta y
  Qprob _ := inferInstance
  Wprob _ := inferInstance
  q_generate x E := by
    have h := (native_stopped_tail_regeneration M (clampedEmitter M e)).1 x
      (hX x x.property) E
    rw [clamp_read_zero M e x .p (hX x x.property)] at h
    rw [closed_sum pi tau (M.update (.read 1)) hcB x (fun z : Z => (rawTailLaw M (clampedEmitter M e) .beta z).real (prefixRaw 1 ⁻¹' E))]
    exact h
  w_generate y E := by
    have h := (native_stopped_tail_regeneration M (clampedEmitter M e)).2 y
      (hY y y.property) E
    rw [clamp_read_zero M e y .beta (hY y y.property)] at h
    rw [closed_sum tau pi (M.update (.read 0)) hcA y (fun z : Z => (rawTailLaw M (clampedEmitter M e) .p z).real (prefixRaw 0 ⁻¹' E))]
    exact h

/-- Both comparisons use the same acquired kernels and the same normalized positive rows. -/
theorem native_clamped_complete_distortion (M : Observer Z) (e : InstalledEmitter M)
    (pi tau : PMF Z)
    (hB : pi.bind (M.update (.read 1)) = tau)
    (hA : tau.bind (M.update (.read 0)) = pi)
    (hX : ∀ z ∈ pi.support, (M.project z).control = .fourth (.active .p))
    (hY : ∀ z ∈ tau.support, (M.project z).control = .fourth (.active .beta))
    (hcB : ∀ x ∈ pi.support, ∀ y ∈ (M.update (.read 1) x).support, y ∈ tau.support)
    (hcA : ∀ y ∈ tau.support, ∀ x ∈ (M.update (.read 0) y).support, x ∈ pi.support) :
    let du := ∑ x : pi.support, (pi x).toReal*
      |(e.emit x (some (.read 0))).toReal-clampEmission (e.emit x (some (.read 0))).toReal|
    let dv := ∑ y : tau.support, (tau y).toReal*
      |(e.emit y (some (.read 0))).toReal-clampEmission (e.emit y (some (.read 0))).toReal|
    let DQ := ∑ x : pi.support, (pi x).toReal*
      (measurableTotalVariation (rawTailLaw M e .p x)
        (rawTailLaw M (clampedEmitter M e) .p x)).toReal
    let DW := ∑ y : tau.support, (tau y).toReal*
      (measurableTotalVariation (rawTailLaw M e .beta y)
        (rawTailLaw M (clampedEmitter M e) .beta y)).toReal
    ∃ R : RegularTable pi.support tau.support,
      (∀ x, R.pi x = (pi x).toReal ∧ R.u x =
        clampEmission (e.emit x (some (.read 0))).toReal ∧
        R.Q x = rawTailLaw M (clampedEmitter M e) .p x) ∧
      (∀ y, R.tau y = (tau y).toReal ∧ R.v y =
        clampEmission (e.emit y (some (.read 0))).toReal ∧
        R.W y = rawTailLaw M (clampedEmitter M e) .beta y) ∧
      (∀ x y, R.B x y = (M.update (.read 1) x y).toReal) ∧
      (∀ y x, R.A y x = (M.update (.read 0) y x).toReal) ∧
      (DQ ≤ du+(2/3)*DW ∧ DW ≤ dv+(2/5)*DQ ∧
        DQ ≤ (15*du+10*dv)/11 ∧ DW ≤ (6*du+15*dv)/11) ∧
      (∀ x, R.Q x {none} = 0) ∧ (∀ y, R.W y {none} = 0) := by
  dsimp only
  let R := table M e pi tau hB hA hX hY hcB hcA
  refine ⟨R,(fun _ => ⟨rfl,rfl,rfl⟩),(fun _ => ⟨rfl,rfl,rfl⟩),
    (fun _ _ => rfl),(fun _ _ => rfl),?_⟩
  refine ⟨?_, (regular_complete_survival R).2.1, (regular_complete_survival R).2.2⟩
  apply stationary_weighted_complete_distortion R
    (fun x => (e.emit x (some (.read 0))).toReal)
    (fun y => (e.emit y (some (.read 0))).toReal)
    (fun x => rawTailLaw M e .p x) (fun y => rawTailLaw M e .beta y)
    (fun _ => inferInstance) (fun _ => inferInstance)
  · intro x E
    dsimp [R,table]
    rw [closed_sum pi tau (M.update (.read 1)) hcB x (fun z : Z => (rawTailLaw M e .beta z).real (prefixRaw 1 ⁻¹' E))]
    exact (native_stopped_tail_regeneration M e).1 x (hX x x.property) E
  · intro y E
    dsimp [R,table]
    rw [closed_sum tau pi (M.update (.read 0)) hcA y (fun z : Z => (rawTailLaw M e .p z).real (prefixRaw 0 ⁻¹' E))]
    exact (native_stopped_tail_regeneration M e).2 y (hY y y.property) E

def depthA : Depth := ⟨1,by omega⟩
def depthB : Depth := ⟨2,by omega⟩

private theorem rate_a : rate depthA = endpointA := by
  apply Subtype.ext
  norm_num [rate,depthA,endpointA,Nat.fib]
private theorem rate_b : rate depthB = endpointB := by
  apply Subtype.ext
  norm_num [rate,depthB,endpointB,Nat.fib]

private theorem original_cost (M : Observer Z) (e : InstalledEmitter M)
    (mu : PMF Depth) (s : ActivePhase) (eta : PMF Z) (k : Depth)
    (h : (∑ z, eta z*measurableTotalVariation (tailLaw M e s z) (pureTail k s)) ≤
      installedRisk M e mu s) :
    (∑ z : eta.support, (eta z).toReal*
      (measurableTotalVariation (rawTailLaw M e s z)
        (explicitStoppedWordLaw s (rate k))).toReal) ≤
      (installedRisk M e mu s).toReal := by
  have hr := ENNReal.toReal_mono (risk_finite M e mu s) h
  rw [ENNReal.toReal_sum (fun z _ => ENNReal.mul_ne_top (eta.apply_ne_top z)
    (probability_tv_finite _ _))] at hr
  simp only [ENNReal.toReal_mul] at hr
  rw [support_sum eta (fun z : Z => (eta z).toReal * (measurableTotalVariation (rawTailLaw M e s z) (explicitStoppedWordLaw s (rate k))).toReal) (by intro z hz; simp [(eta.apply_eq_zero_iff z).mpr hz])]
  simp_rw [← pure_raw_law k s,rawTailLaw,raw_projection_tv]
  exact hr

private theorem averaged_clipping (M : Observer Z) (e : InstalledEmitter M)
    (s : ActivePhase) (eta : PMF Z)
    (hphase : ∀ z ∈ eta.support, (M.project z).control = .fourth (.active s))
    (risk rho : ℝ)
    (hcostA : (∑ z : eta.support, (eta z).toReal*
      (measurableTotalVariation (rawTailLaw M e s z) (explicitStoppedWordLaw s endpointA)).toReal)
      ≤ risk)
    (hcostB : (∑ z : eta.support, (eta z).toReal*
      (measurableTotalVariation (rawTailLaw M e s z) (explicitStoppedWordLaw s endpointB)).toReal)
      ≤ risk)
    (hrho : rho = match s with | .p => 1116529/22781250 | .beta => 239/6750) :
    (∑ z : eta.support, (eta z).toReal*
      |(e.emit z (some (.read 0))).toReal-clampEmission (e.emit z (some (.read 0))).toReal|)
      ≤ 2*(risk-rho) := by
  have hp (z : eta.support) :
      |(e.emit z (some (.read 0))).toReal-clampEmission (e.emit z (some (.read 0))).toReal| ≤
      (measurableTotalVariation (rawTailLaw M e s z) (explicitStoppedWordLaw s endpointA)).toReal+
      (measurableTotalVariation (rawTailLaw M e s z) (explicitStoppedWordLaw s endpointB)).toReal-
        2*rho := by
    cases s
    · have h := (native_configuration_clipping_budget M e).1 z (hphase z z.property)
      rw [clamp_read_zero M e z .p (hphase z z.property)] at h
      simpa only [hrho] using h
    · have h := (native_configuration_clipping_budget M e).2 z (hphase z z.property)
      rw [clamp_read_zero M e z .beta (hphase z z.property)] at h
      simpa only [hrho] using h
  have hsum : ∑ z : eta.support, (eta z).toReal = 1 := by
    rw [support_sum eta (fun z : Z => (eta z).toReal) (by intro z hz; simp [(eta.apply_eq_zero_iff z).mpr hz])]
    exact pmf_sum_real eta
  calc
    _ ≤ ∑ z : eta.support, (eta z).toReal*
      ((measurableTotalVariation (rawTailLaw M e s z) (explicitStoppedWordLaw s endpointA)).toReal+
      (measurableTotalVariation (rawTailLaw M e s z) (explicitStoppedWordLaw s endpointB)).toReal-
        2*rho) := Finset.sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left (hp z) ENNReal.toReal_nonneg
    _ = (∑ z : eta.support, (eta z).toReal*
        (measurableTotalVariation (rawTailLaw M e s z) (explicitStoppedWordLaw s endpointA)).toReal)+
      (∑ z : eta.support, (eta z).toReal*
        (measurableTotalVariation (rawTailLaw M e s z) (explicitStoppedWordLaw s endpointB)).toReal)-
          2*rho := by
      simp_rw [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
      rw [← Finset.sum_mul,hsum,one_mul]
    _ ≤ _ := by linarith

/-- Constancy is required only on positive original histories at the designated held fibre. -/
def SuspendedConstant (M : Observer Z) (e : InstalledEmitter M) (mu : PMF Depth) : Prop :=
  ∃ s0 : ℝ, 0 ≤ s0 ∧ s0 ≤ 1 ∧
    ∀ H : PhaseHistory .beta, 0 < NativeConditionalControl.DepthLaw.normalizer mu H.val.1 →
      H.val.2.source.finiteFields = heldFields .beta →
      ∀ z : Z, 0 < row M H.val.1 z → (e.emit z (some (.read 0))).toReal = s0

def phaseExcess (M : Observer Z) (e : InstalledEmitter M) (mu : PMF Depth) (s : ActivePhase) : ℝ :=
  (installedRisk M e mu s).toReal -
    match s with | .p => 1116529/22781250 | .beta => 239/6750

private theorem mean_comparison {X : Type*} [Fintype X] (pi : X → ℝ)
    (hpi : ∀ x, 0 ≤ pi x) (hpis : ∑ x, pi x = 1)
    (Q Q' : X → Measure RawTail) (P : Measure RawTail)
    (hQ : ∀ x, IsProbabilityMeasure (Q x)) (hQ' : ∀ x, IsProbabilityMeasure (Q' x))
    [IsProbabilityMeasure P] (E : Set RawTail) :
    |(∑ x, pi x*(Q' x).real E)-P.real E| ≤
      (∑ x, pi x*(measurableTotalVariation (Q x) P).toReal)+
        ∑ x, pi x*(measurableTotalVariation (Q x) (Q' x)).toReal := by
  haveI (x : X) : IsProbabilityMeasure (Q x) := hQ x
  haveI (x : X) : IsProbabilityMeasure (Q' x) := hQ' x
  have he : (∑ x, pi x*(Q' x).real E)-P.real E =
      ∑ x, pi x*((Q' x).real E-P.real E) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hpis,one_mul]
  rw [he]
  calc
    _ ≤ ∑ x, |pi x*((Q' x).real E-P.real E)| := abs_sum_le_sum_abs _ _
    _ = ∑ x, pi x*|(Q' x).real E-P.real E| := by
      simp_rw [abs_mul,abs_of_nonneg (hpi _)]
    _ ≤ ∑ x, pi x*((measurableTotalVariation (Q x) P).toReal+
        (measurableTotalVariation (Q x) (Q' x)).toReal) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hpi x)
      calc
        _ = |((Q x).real E-P.real E)-((Q x).real E-(Q' x).real E)| := by congr 1; ring
        _ ≤ |(Q x).real E-P.real E|+|(Q x).real E-(Q' x).real E| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            (abs_add_le ((Q x).real E-P.real E) (-((Q x).real E-(Q' x).real E)))
        _ ≤ _ := add_le_add (event_gap _ _ E (by trivial)) (event_gap _ _ E (by trivial))
    _ = _ := by simp only [mul_add,Finset.sum_add_distrib]

/-- The gap uses the original complete configuration risk on all positive histories. -/
theorem original_constant_suspension_gap (M : Observer Z) (e : InstalledEmitter M)
    (mu : PMF Depth) (ha : mu depthA ≠ 0) (hb : mu depthB ≠ 0)
    (hc : SuspendedConstant M e mu) :
    0 ≤ phaseExcess M e mu .p ∧ 0 ≤ phaseExcess M e mu .beta ∧
      1/195200 < max (phaseExcess M e mu .p) (phaseExcess M e mu .beta) := by
  obtain ⟨pi,tau,hB,hA,hrisk,hreach,hcB,hcA,_⟩ := native_complete_common_rows M e mu
  have hX (z : Z) (hz : z ∈ pi.support) :
      (M.project z).control = .fourth (.active .p) := by
    obtain ⟨_,_,_,_,_,hf,_⟩ := hreach .p z hz
    exact congrArg FiniteFields.control hf
  have hY (z : Z) (hz : z ∈ tau.support) :
      (M.project z).control = .fourth (.active .beta) := by
    obtain ⟨_,_,_,_,_,hf,_⟩ := hreach .beta z hz
    exact congrArg FiniteFields.control hf
  let R := table M e pi tau hB hA hX hY hcB hcA
  let ep := phaseExcess M e mu .p
  let eb := phaseExcess M e mu .beta
  let du := ∑ x : pi.support, R.pi x*|(e.emit x (some (.read 0))).toReal-R.u x|
  let dv := ∑ y : tau.support, R.tau y*|(e.emit y (some (.read 0))).toReal-R.v y|
  let DQ := ∑ x : pi.support, R.pi x*
    (measurableTotalVariation (rawTailLaw M e .p x) (R.Q x)).toReal
  let DW := ∑ y : tau.support, R.tau y*
    (measurableTotalVariation (rawTailLaw M e .beta y) (R.W y)).toReal
  have hpa := original_cost M e mu .p pi depthA (hrisk depthA ha .p).1
  have hpb := original_cost M e mu .p pi depthB (hrisk depthB hb .p).1
  have hba := original_cost M e mu .beta tau depthA (hrisk depthA ha .beta).1
  have hbb := original_cost M e mu .beta tau depthB (hrisk depthB hb .beta).1
  rw [rate_a] at hpa hba
  rw [rate_b] at hpb hbb
  have hdu : du ≤ 2*ep := averaged_clipping M e .p pi hX _ _ hpa hpb rfl
  have hdv : dv ≤ 2*eb := averaged_clipping M e .beta tau hY _ _ hba hbb rfl
  have hdu0 : 0 ≤ du := Finset.sum_nonneg fun x _ => mul_nonneg (R.pi_nonneg x) (abs_nonneg _)
  have hdv0 : 0 ≤ dv := Finset.sum_nonneg fun y _ => mul_nonneg (R.tau_nonneg y) (abs_nonneg _)
  have hep : 0 ≤ ep := by linarith
  have heb : 0 ≤ eb := by linarith
  obtain ⟨R',hidX,hidY,hidB,hidA,⟨hd1,hd2,hd3,hd4⟩,_,_⟩ :=
    native_clamped_complete_distortion M e pi tau hB hA hX hY hcB hcA
  have hDQ : DQ ≤ (30*ep+20*eb)/11 := by
    change DQ ≤ (15*du+10*dv)/11 at hd3
    linarith
  have hDW : DW ≤ (12*ep+30*eb)/11 := by
    change DW ≤ (6*du+15*dv)/11 at hd4
    linarith
  obtain ⟨s0,hs00,hs01,hconstant⟩ := hc
  have hs (y : tau.support) : R.v y = clampEmission s0 := by
    obtain ⟨m,t,j,hy,hn,_,_⟩ := hreach .beta y y.property
    have hh := hconstant (windowPhaseHistory m t j .beta) hn rfl y hy
    change clampEmission (e.emit y (some (.read 0))).toReal = clampEmission s0
    rw [hh]
  let hp := (41*ep+20*eb)/11
  let hb' := (12*ep+41*eb)/11
  have hQbound : ∀ r : unitInterval, (r:ℝ) = 1/3 ∨ (r:ℝ) = 2/5 →
      FullTVBound R.qMean (explicitStoppedWordLaw .p r) (1116529/22781250+hp) := by
    intro r hr E
    haveI := endpoint_probability .p r
    have h := mean_comparison R.pi R.pi_nonneg R.pi_sum
      (fun x => rawTailLaw M e .p x) R.Q (explicitStoppedWordLaw .p r)
      (fun _ => inferInstance) R.Qprob E
    have hold : (∑ x : pi.support, R.pi x*
        (measurableTotalVariation (rawTailLaw M e .p x) (explicitStoppedWordLaw .p r)).toReal)
        ≤ (installedRisk M e mu .p).toReal := by
      rcases hr with hr | hr
      · have he : r = endpointA := Subtype.ext hr
        subst r; exact hpa
      · have he : r = endpointB := Subtype.ext hr
        subst r; exact hpb
    change |R.qMean E-(explicitStoppedWordLaw .p r).real E| ≤ _ at h
    change |R.qMean E-(explicitStoppedWordLaw .p r).real E| ≤ _
    change _ ≤ _+DQ at h
    have hrisk : (installedRisk M e mu .p).toReal = 1116529/22781250+ep := by
      dsimp [ep,phaseExcess]; ring
    dsimp [hp]
    linarith
  have hWbound : ∀ r : unitInterval, (r:ℝ) = 1/3 ∨ (r:ℝ) = 2/5 →
      FullTVBound R.wMean (explicitStoppedWordLaw .beta r) (239/6750+hb') := by
    intro r hr E
    haveI := endpoint_probability .beta r
    have h := mean_comparison R.tau R.tau_nonneg R.tau_sum
      (fun y => rawTailLaw M e .beta y) R.W (explicitStoppedWordLaw .beta r)
      (fun _ => inferInstance) R.Wprob E
    have hold : (∑ y : tau.support, R.tau y*
        (measurableTotalVariation (rawTailLaw M e .beta y) (explicitStoppedWordLaw .beta r)).toReal)
        ≤ (installedRisk M e mu .beta).toReal := by
      rcases hr with hr | hr
      · have he : r = endpointA := Subtype.ext hr
        subst r; exact hba
      · have he : r = endpointB := Subtype.ext hr
        subst r; exact hbb
    change |R.wMean E-(explicitStoppedWordLaw .beta r).real E| ≤ _ at h
    change |R.wMean E-(explicitStoppedWordLaw .beta r).real E| ≤ _
    change _ ≤ _+DW at h
    have hrisk : (installedRisk M e mu .beta).toReal = 239/6750+eb := by
      dsimp [eb,phaseExcess]; ring
    dsimp [hb']
    linarith
  have hsep := R.constant_suspension_separator (clampEmission s0) hp hb'
    (clamp_box s0) (fun y _ => hs y) (by dsimp [hp]; positivity)
    (by dsimp [hb']; positivity) hQbound hWbound
  have hepm : ep ≤ max ep eb := le_max_left _ _
  have hebm : eb ≤ max ep eb := le_max_right _ _
  have hpm : hp ≤ (61/11)*max ep eb := by dsimp [hp]; linarith
  have hbm : hb' ≤ (61/11)*max ep eb := by dsimp [hb']; linarith
  have hmax := max_le hpm hbm
  exact ⟨hep,heb,by linarith⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeClampedCompleteTable
