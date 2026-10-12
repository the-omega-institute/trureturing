/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRow
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native paid histories control their full target laws and preserve supported installed generators. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeInstalledFullLaw
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.Order.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Classical

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRow

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeConditionalControl.DepthLaw NativeConditionalControl.Prefix
open NativeObserverJointLaw NativeInstalledFullLaw NativeFullResidual
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

universe u
variable {Z : Type u} [Fintype Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]

/-- Deterministic seed 1 and markers 100; this is a held register value, not an archive. -/
def heldRegisters : Registers := markerRegisters 1 [1, 0, 0]

def windowForm (m t j : ℕ) (s : ActivePhase) : PrefixForm :=
  ⟨List.replicate m 0 ++ List.replicate t 1,
    .acquired 1 (.segment 0 1 (.segment 0 0 (.segment 0 0 (.active j s))))⟩

/-- Equal-pair rejections, the literal latch suffix, then actual returns and optional beta. -/
def windowWord (m t j : ℕ) (s : ActivePhase) : List Letter :=
  retryWord (List.replicate m 0 ++ List.replicate t 1) ++
    [1, 0, 1, 1, 0, 0] ++ loopWord j ++ phaseWord s

def windowHistory (m t j : ℕ) (s : ActivePhase) : List Operation :=
  reads (windowWord m t j s)

def windowState (m t j : ℕ) (s : ActivePhase) : AcquiredNativeState :=
  atPhase 3 heldRegisters j
    ⟨2*m+3+j, 2*t+3+j + match s with | .p => 0 | .beta => 1⟩ s

private theorem window_render (m t j : ℕ) (s : ActivePhase) :
    render (windowForm m t j s) = windowHistory m t j s := by
  simp [windowForm, windowHistory, windowWord, render, renderPayload, seedWord,
    pWord, reads, loopWord, List.map_append, List.append_assoc]

private theorem window_reconstruct (m t j : ℕ) (s : ActivePhase) :
    reconstruct (windowForm m t j s) = windowState m t j s := by
  cases s <;> simp [windowForm, windowState, reconstruct, reconstructPayload,
    retryCounts, heldRegisters, markerRegisters, foldMarkers, atPhase, payloadControl,
    List.count_replicate, Nat.add_assoc]

private theorem window_run (m t j : ℕ) (s : ActivePhase) :
    run (windowHistory m t j s) = some (windowState m t j s) := by
  rw [← window_render, ← window_reconstruct]
  exact run_render _

def windowPhaseHistory (m t j : ℕ) (s : ActivePhase) : PhaseHistory s :=
  ⟨(windowHistory m t j s, windowState m t j s), window_run m t j s, rfl⟩

private theorem window_counts (m t j : ℕ) (s : ActivePhase) :
    (windowWord m t j s).count 0 = 2*m+3+j ∧
    (windowWord m t j s).count 1 =
      2*t+3+j + match s with | .p => 0 | .beta => 1 := by
  have hc (j : ℕ) : (loopWord j).count 0 = j ∧ (loopWord j).count 1 = j := by
    induction j with
    | zero => simp [loopWord]
    | succ j ih => simpa [loop_succ, List.count_append] using ih
  have hr (l : List Letter) (a : Letter) :
      (retryWord l).count a = 2*l.count a := by
    induction l with
    | nil => simp [retryWord]
    | cons b l ih =>
      simp only [retryWord, List.map_cons, List.flatten_cons, List.count_append,
        List.count_cons, List.count_nil] at *
      split_ifs <;> omega
  cases s <;> simp [windowWord, List.count_append, hr, hc, phaseWord,
    List.count_replicate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  <;> omega

/-- Complete tail mixture on the original countable outcome space, including none. -/
def tailMixture (M : Observer Z) (e : InstalledEmitter M) (s : ActivePhase)
    (η : PMF Z) : Measure (ValidTail s) := ∑ z, η z • tailLaw M e s z

/-- Law-before-TV uses exactly the same unrestricted legal-history domain as installedRisk. -/
def installedLawRisk (M : Observer Z) (e : InstalledEmitter M) (μ : PMF Depth)
    (s : ActivePhase) : ℝ≥0∞ :=
  ⨆ H : PhaseHistory s, measurableTotalVariation
    (∑ z, row M H.val.1 z • fullLaw M e z) (fullTarget M μ H.val.1 H.val.2)

def rawLawRisk (M : Observer Z) (e : InstalledEmitter M) (μ : PMF Depth)
    (s : ActivePhase) : ℝ≥0∞ :=
  ⨆ H : PhaseHistory s, measurableTotalVariation
    (tailMixture M e s (row M H.val.1)) (rawTarget μ H.val.1 H.val.2 s)

private theorem mixture_tv_le {A : Type*} [MeasurableSpace A]
    (η : PMF Z) (P : Z → Measure A) (Q : Measure A) :
    measurableTotalVariation (∑ z, η z • P z) Q ≤
      ∑ z, η z * measurableTotalVariation (P z) Q := by
  have hs : ∑ z, η z = 1 := by simpa only [tsum_fintype] using η.tsum_coe
  unfold measurableTotalVariation
  refine iSup_le fun E => ?_
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply max_le
  · apply (tsub_le_iff_right).mpr
    calc
      ∑ z, η z * P z E.val ≤ ∑ z, η z *
          (Q E.val + ⨆ F : {F : Set A // MeasurableSet F},
            max (P z F.val - Q F.val) (Q F.val - P z F.val)) := by
        apply Finset.sum_le_sum
        intro z _
        gcongr
        apply (tsub_le_iff_left).mp
        exact (le_max_left (P z E.val-Q E.val) (Q E.val-P z E.val)).trans
          (le_iSup (fun F : {F : Set A // MeasurableSet F} =>
            max (P z F.val-Q F.val) (Q F.val-P z F.val)) E)
      _ = Q E.val + ∑ z, η z *
          (⨆ F : {F : Set A // MeasurableSet F},
            max (P z F.val - Q F.val) (Q F.val - P z F.val)) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul]
      _ = _ := add_comm _ _
  · apply (tsub_le_iff_right).mpr
    calc
      Q E.val = ∑ z, η z * Q E.val := by rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ ∑ z, η z * (P z E.val +
          ⨆ F : {F : Set A // MeasurableSet F},
            max (P z F.val - Q F.val) (Q F.val - P z F.val)) := by
        apply Finset.sum_le_sum
        intro z _
        gcongr
        apply (tsub_le_iff_left).mp
        exact (le_max_right (P z E.val-Q E.val) (Q E.val-P z E.val)).trans
          (le_iSup (fun F : {F : Set A // MeasurableSet F} =>
            max (P z F.val-Q F.val) (Q F.val-P z F.val)) E)
      _ = _ := by simp_rw [mul_add]; rw [Finset.sum_add_distrib, add_comm]

private theorem mixture_renderer (M : Observer Z) (e : InstalledEmitter M)
    (s : ActivePhase) (H : PhaseHistory s) :
    ∑ z, row M H.val.1 z • fullLaw M e z =
      (tailMixture M e s (row M H.val.1)).map (fullRenderer H.val.2 s) := by
  rw [tailMixture, Measure.map_finset_sum' (measurable_of_countable _).aemeasurable]
  apply Finset.sum_congr rfl
  intro z _
  rw [Measure.map_smul]
  by_cases hz : row M H.val.1 z = 0
  · simp [hz]
  · rw [installed_configuration_identity M e s z H.val.2
      ((actual_row_refines M _ _ H.property.1).1 z hz) H.property.2]

private theorem history_law_tv (M : Observer Z) (e : InstalledEmitter M)
    (μ : PMF Depth) (s : ActivePhase) (H : PhaseHistory s) :
    measurableTotalVariation (∑ z, row M H.val.1 z • fullLaw M e z)
        (fullTarget M μ H.val.1 H.val.2) =
      measurableTotalVariation (tailMixture M e s (row M H.val.1))
        (rawTarget μ H.val.1 H.val.2 s) := by
  rw [mixture_renderer M e s H,
    ((native_history_risk_transport M μ s (fun _ z => tailLaw M e s z)).1 H).2.2.1,
    full_renderer_tv _ s H.property.2]

/-- A Bernoulli log likelihood, per rejected pair before the deterministic suffix. -/
def pairLogRatio (m t : ℕ) (r a : ℝ) : ℝ :=
  2*((m:ℝ)*Real.log (a/r) + (t:ℝ)*Real.log ((1-a)/(1-r)))

private theorem bernoulli_quadratic (q r a : ℝ)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r) (hr1 : r < 1)
    (ha : 0 < a) (ha1 : a < 1) :
    q*Real.log (a/r) + (1-q)*Real.log ((1-a)/(1-r)) ≤
      (q-r)^2/(r*(1-r)) := by
  have hqa : q*Real.log (a/q) ≤ q*(a/q-1) :=
    mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos ha hq)) hq.le
  have hqb : (1-q)*Real.log ((1-a)/(1-q)) ≤ (1-q)*((1-a)/(1-q)-1) :=
    mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (sub_pos.mpr ha1) (sub_pos.mpr hq1)))
      (sub_nonneg.mpr hq1.le)
  have hqr : q*Real.log (q/r) ≤ q*(q/r-1) :=
    mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hq hr)) hq.le
  have hqs : (1-q)*Real.log ((1-q)/(1-r)) ≤ (1-q)*((1-q)/(1-r)-1) :=
    mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (sub_pos.mpr hq1) (sub_pos.mpr hr1)))
      (sub_nonneg.mpr hq1.le)
  have hsplit : q*Real.log (a/r) + (1-q)*Real.log ((1-a)/(1-r)) =
      (q*Real.log (a/q) + (1-q)*Real.log ((1-a)/(1-q))) +
      (q*Real.log (q/r) + (1-q)*Real.log ((1-q)/(1-r))) := by
    rw [Real.log_div ha.ne' hr.ne', Real.log_div ha.ne' hq.ne',
      Real.log_div hq.ne' hr.ne',
      Real.log_div (sub_pos.mpr ha1).ne' (sub_pos.mpr hr1).ne',
      Real.log_div (sub_pos.mpr ha1).ne' (sub_pos.mpr hq1).ne',
      Real.log_div (sub_pos.mpr hq1).ne' (sub_pos.mpr hr1).ne']
    ring
  have hcancel : q*(a/q-1)+(1-q)*((1-a)/(1-q)-1) = 0 := by
    field_simp [hq.ne', (sub_pos.mpr hq1).ne']
    <;> ring
  have hquad : q*(q/r-1)+(1-q)*((1-q)/(1-r)-1) = (q-r)^2/(r*(1-r)) := by
    field_simp [hr.ne', (sub_pos.mpr hr1).ne']
    <;> ring
  rw [hsplit]
  linarith

private theorem pair_quadratic (m t : ℕ) (hm : 0 < m) (ht : 0 < t)
    (r a : ℝ) (hr : 0 < r) (hr1 : r < 1) (ha : 0 < a) (ha1 : a < 1) :
    pairLogRatio m t r a ≤
      2*((m:ℝ)-r*(m+t))^2/((m+t)*r*(1-r)) := by
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have ht' : (0:ℝ) < t := Nat.cast_pos.mpr ht
  have hT : (0:ℝ) < m+t := add_pos hm' ht'
  have hq : 0 < (m:ℝ)/(m+t) := div_pos hm' hT
  have hq1 : (m:ℝ)/(m+t) < 1 := (div_lt_one hT).mpr (by linarith)
  have h := mul_le_mul_of_nonneg_left
    (bernoulli_quadratic ((m:ℝ)/(m+t)) r a hq hq1 hr hr1 ha ha1) hT.le
  have he : (m+t:ℝ)*((m:ℝ)/(m+t)-r)^2/(r*(1-r)) =
      ((m:ℝ)-r*(m+t))^2/((m+t)*r*(1-r)) := by
    field_simp
    <;> ring
  have hleft : (m+t:ℝ)*((m:ℝ)/(m+t)*Real.log (a/r) +
      (1-(m:ℝ)/(m+t))*Real.log ((1-a)/(1-r))) =
      (m:ℝ)*Real.log (a/r)+(t:ℝ)*Real.log ((1-a)/(1-r)) := by
    field_simp
    <;> ring
  rw [hleft, ← mul_div_assoc, he] at h
  unfold pairLogRatio
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left h (show (0:ℝ) ≤ 2 by norm_num)

private theorem strict_native_log (k i : Depth) (hi : i ≠ k) :
    (rate k:ℝ)*Real.log ((rate i:ℝ)/(rate k:ℝ)) +
      (1-(rate k:ℝ))*Real.log ((1-(rate i:ℝ))/(1-(rate k:ℝ))) < 0 := by
  have hr := ratio_interior k
  have ha := ratio_interior i
  change 0 < (rate k:ℝ) ∧ (rate k:ℝ) < 1 at hr
  change 0 < (rate i:ℝ) ∧ (rate i:ℝ) < 1 at ha
  have hne : (rate i:ℝ)/(rate k:ℝ) ≠ 1 := by
    intro h
    apply hi
    apply FourthSegmentLawRecovery.Rates.rate_injective
    exact (div_eq_one_iff_eq hr.1.ne').mp h
  have h1 := mul_lt_mul_of_pos_left
    (Real.log_lt_sub_one_of_pos (div_pos ha.1 hr.1) hne) hr.1
  have h2 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos
      (div_pos (sub_pos.mpr ha.2) (sub_pos.mpr hr.2))) (sub_nonneg.mpr hr.2.le)
  have he : (rate k:ℝ)*((rate i:ℝ)/(rate k:ℝ)-1) +
      (1-(rate k:ℝ))*((1-(rate i:ℝ))/(1-(rate k:ℝ))-1) = 0 := by
    field_simp [hr.1.ne', (sub_pos.mpr hr.2).ne']
    <;> ring
  linarith

def suffixLogRatio (j : ℕ) (s : ActivePhase) (k i : Depth) : ℝ :=
  (3+j:ℕ)*Real.log ((rate i:ℝ)/(rate k:ℝ)) +
    (3+j + match s with | .p => 0 | .beta => 1 : ℕ)*
      Real.log ((1-(rate i:ℝ))/(1-(rate k:ℝ)))

private theorem window_likelihood_real (m t j : ℕ) (s : ActivePhase) (k : Depth) :
    (likelihood (windowHistory m t j s) k).toReal =
      (rate k:ℝ)^(2*m+3+j) *
        (1-(rate k:ℝ))^(2*t+3+j + match s with | .p => 0 | .beta => 1) := by
  rw [likelihood, windowHistory,
    show readLetters (reads (windowWord m t j s)) = windowWord m t j s
      from by simpa only [List.append_nil, readLetters] using erase_reads (windowWord m t j s) [],
    word_counts, (window_counts m t j s).1, (window_counts m t j s).2]
  simp [ENNReal.toReal_mul, ENNReal.toReal_pow, alphaMass, betaMass]

private theorem window_log_ratio (m t j : ℕ) (s : ActivePhase) (k i : Depth) :
    Real.log ((likelihood (windowHistory m t j s) i).toReal /
      (likelihood (windowHistory m t j s) k).toReal) =
      pairLogRatio m t (rate k) (rate i) + suffixLogRatio j s k i := by
  have hn (i : Depth) : (rate i:ℝ) ≠ 0 := (ratio_interior i).1.ne'
  have hb (i : Depth) : 1-(rate i:ℝ) ≠ 0 := (sub_pos.mpr (ratio_interior i).2).ne'
  rw [window_likelihood_real, window_likelihood_real,
    Real.log_div (mul_ne_zero (pow_ne_zero _ (hn i)) (pow_ne_zero _ (hb i)))
      (mul_ne_zero (pow_ne_zero _ (hn k)) (pow_ne_zero _ (hb k))),
    Real.log_mul (pow_ne_zero _ (hn i)) (pow_ne_zero _ (hb i)),
    Real.log_mul (pow_ne_zero _ (hn k)) (pow_ne_zero _ (hb k))]
  simp only [Real.log_pow, pairLogRatio, suffixLogRatio,
    Real.log_div (hn i) (hn k), Real.log_div (hb i) (hb k)]
  cases s <;> push_cast <;> ring

/-- Literal native windows, both original risk orders and the uniform quadratic envelope.
No row average, exposure premise, stationarity premise or completion conditioning is used. -/
theorem native_paid_window_control (M : Observer Z) (e : InstalledEmitter M)
    (μ : PMF Depth) (m t j : ℕ) (s : ActivePhase) :
    let H := windowPhaseHistory m t j s
    (run H.val.1 = some H.val.2) ∧
    H.val.2.source.finiteFields = ⟨.fourth (.active s), heldRegisters⟩ ∧
    H.val.2.counts = ⟨2*m+3+j, 2*t+3+j + match s with | .p => 0 | .beta => 1⟩ ∧
    (∀ k : Depth, 0 < likelihood H.val.1 k ∧
      likelihood H.val.1 k = alphaMass (rate k)^(2*m+3+j) *
        betaMass (rate k)^(2*t+3+j + match s with | .p => 0 | .beta => 1)) ∧
    (0 < normalizer μ H.val.1 ∧ normalizer μ H.val.1 ≤ 1) ∧
    (∀ z ∈ (row M H.val.1).support,
      M.project z = ⟨.fourth (.active s), heldRegisters⟩ ∧
      fullLaw M e z = (tailLaw M e s z).map (fullRenderer H.val.2 s)) ∧
    (∑ z, row M H.val.1 z * measurableTotalVariation (tailLaw M e s z)
      (rawTarget μ H.val.1 H.val.2 s)) ≤ installedRisk M e μ s ∧
    measurableTotalVariation (tailMixture M e s (row M H.val.1))
      (rawTarget μ H.val.1 H.val.2 s) ≤ installedLawRisk M e μ s ∧
    rawLawRisk M e μ s = installedLawRisk M e μ s ∧
    installedLawRisk M e μ s ≤ installedRisk M e μ s ∧
    (∀ k i : Depth, 0 < m → 0 < t →
      Real.log ((likelihood H.val.1 i).toReal / (likelihood H.val.1 k).toReal) ≤
        2*((m:ℝ)-(rate k:ℝ)*(m+t))^2/((m+t)*(rate k:ℝ)*(1-(rate k:ℝ))) +
          suffixLogRatio j s k i) ∧
    (∀ k i : Depth, i ≠ k →
      (rate k:ℝ)*Real.log ((rate i:ℝ)/(rate k:ℝ)) +
        (1-(rate k:ℝ))*Real.log ((1-(rate i:ℝ))/(1-(rate k:ℝ))) < 0) := by
  dsimp only
  let H := windowPhaseHistory m t j s
  have hf : H.val.2.source.finiteFields = ⟨.fourth (.active s), heldRegisters⟩ := rfl
  refine ⟨H.property.1, hf, rfl, ?_, normalizer_bounds μ _ _ H.property.1,
    ?_, ?_, ?_, ?_, ?_, ?_, strict_native_log⟩
  · intro k
    refine ⟨likelihood_pos _ k, ?_⟩
    change likelihood (reads (windowWord m t j s)) k = _
    rw [likelihood, show readLetters (reads (windowWord m t j s)) = windowWord m t j s
      from by simpa only [List.append_nil, readLetters] using erase_reads (windowWord m t j s) [],
      word_counts, (window_counts m t j s).1, (window_counts m t j s).2]
  · intro z hz
    have hp := (actual_row_refines M _ _ H.property.1).1 z hz
    exact ⟨hp.trans hf, installed_configuration_identity M e s z H.val.2 hp H.property.2⟩
  · rw [(installed_full_law M e).2.2.2.2.2 μ s]
    exact le_iSup (fun G : PhaseHistory s => ∑ z, row M G.val.1 z *
      measurableTotalVariation (tailLaw M e s z) (rawTarget μ G.val.1 G.val.2 s)) H
  · rw [← history_law_tv M e μ s H]
    exact le_iSup (fun G : PhaseHistory s => measurableTotalVariation
      (∑ z, row M G.val.1 z • fullLaw M e z) (fullTarget M μ G.val.1 G.val.2)) H
  · unfold rawLawRisk installedLawRisk
    congr 1
    funext G
    exact (history_law_tv M e μ s G).symm
  · apply iSup_le
    intro G
    exact (mixture_tv_le (row M G.val.1) (fullLaw M e) _).trans
      (le_iSup (fun J : PhaseHistory s => ∑ z, row M J.val.1 z *
        measurableTotalVariation (fullLaw M e z) (fullTarget M μ J.val.1 J.val.2)) G)
  · intro k i hm ht
    change Real.log ((likelihood (windowHistory m t j s) i).toReal /
      (likelihood (windowHistory m t j s) k).toReal) ≤ _
    rw [window_log_ratio]
    gcongr
    exact pair_quadratic m t hm ht (rate k) (rate i)
      (ratio_interior k).1 (ratio_interior k).2 (ratio_interior i).1 (ratio_interior i).2

#print axioms native_paid_window_control

def windowCount (w : ℕ) (r : ℝ) (u : ℕ) : ℕ := ⌊(w:ℝ)^3*r⌋₊ + u

private theorem growing_counts (k : Depth) (w u v : ℕ)
    (hw : 2 ≤ w) (hu : u < w) (hv : v < w) :
    let r := (rate k:ℝ)
    let m := windowCount w r u
    let t := windowCount w (1-r) v
    0 < m ∧ 0 < t ∧ |(m:ℝ)-r*(m+t)| ≤ w ∧ (w:ℝ)^3/2 ≤ (m:ℝ)+t := by
  dsimp only
  let r := (rate k:ℝ)
  let N := (w:ℝ)^3
  let m := windowCount w r u
  let t := windowCount w (1-r) v
  have hr : (1/3:ℝ) ≤ r ∧ r ≤ 2/5 := FourthSegmentLawRecovery.Rates.rate_bounds k
  have hr0 : 0 ≤ r := by linarith
  have hr1 : 0 ≤ 1-r := by linarith
  have hw' : (2:ℝ) ≤ w := by exact_mod_cast hw
  have hu' : (u:ℝ)+1 ≤ w := by exact_mod_cast (Nat.succ_le_iff.mpr hu)
  have hv' : (v:ℝ)+1 ≤ w := by exact_mod_cast (Nat.succ_le_iff.mpr hv)
  have hN : (8:ℝ) ≤ N := by
    dsimp [N]
    nlinarith [mul_nonneg (show (0:ℝ) ≤ w-2 by linarith)
      (show (0:ℝ) ≤ (w:ℝ)^2+2*w+4 by positivity)]
  have hNr : 1 ≤ N*r := by
    have h := mul_nonneg (show 0 ≤ N-8 by linarith) hr0
    nlinarith
  have hNs : 1 ≤ N*(1-r) := by
    have h := mul_nonneg (show 0 ≤ N-8 by linarith) hr1
    nlinarith
  have hm : 0 < m := Nat.add_pos_left (Nat.floor_pos.mpr hNr) _
  have ht : 0 < t := Nat.add_pos_left (Nat.floor_pos.mpr hNs) _
  have hmU : (m:ℝ) ≤ N*r+u := by
    have h := Nat.floor_le (show 0 ≤ N*r by linarith)
    simpa [m, windowCount, N, Nat.cast_add] using add_le_add_right h (u:ℝ)
  have hmL : N*r+u-1 < (m:ℝ) := by
    have h := Nat.lt_floor_add_one (N*r)
    dsimp [m, windowCount]
    push_cast
    dsimp [N] at *
    linarith
  have htU : (t:ℝ) ≤ N*(1-r)+v := by
    have h := Nat.floor_le (show 0 ≤ N*(1-r) by linarith)
    simpa [t, windowCount, N, Nat.cast_add] using add_le_add_right h (v:ℝ)
  have htL : N*(1-r)+v-1 < (t:ℝ) := by
    have h := Nat.lt_floor_add_one (N*(1-r))
    dsimp [t, windowCount]
    push_cast
    dsimp [N] at *
    linarith
  refine ⟨hm, ht, abs_le.mpr ⟨?_, ?_⟩, ?_⟩
  · have h1 := mul_nonneg hr1 (show 0 ≤ (m:ℝ)-(N*r+u-1) by linarith)
    have h2 := mul_nonneg hr0 (show 0 ≤ N*(1-r)+v-(t:ℝ) by linarith)
    have h3 := mul_nonneg hr1 (Nat.cast_nonneg u : (0:ℝ) ≤ u)
    have h4 := mul_nonneg hr0 (show 0 ≤ (w:ℝ)-1-v by linarith)
    nlinarith
  · have h1 := mul_nonneg hr1 (show 0 ≤ N*r+u-(m:ℝ) by linarith)
    have h2 := mul_nonneg hr0 (show 0 ≤ (t:ℝ)-(N*(1-r)+v-1) by linarith)
    have h3 := mul_nonneg hr0 (Nat.cast_nonneg v : (0:ℝ) ≤ v)
    have h4 := mul_nonneg hr1 (show 0 ≤ (w:ℝ)-1-u by linarith)
    nlinarith
  · change N/2 ≤ (m:ℝ)+t
    nlinarith [(Nat.cast_nonneg u : (0:ℝ) ≤ u), (Nat.cast_nonneg v : (0:ℝ) ≤ v)]

/-- The growing rectangular paid windows have a competitor-uniform quadratic envelope.
The return suffix is fixed but arbitrary; its likelihood factor is retained explicitly. -/
theorem native_growing_window_likelihood (k i : Depth) (w u v j : ℕ)
    (s : ActivePhase) (hw : 2 ≤ w) (hu : u < w) (hv : v < w) :
    let m := windowCount w (rate k) u
    let t := windowCount w (1-(rate k:ℝ)) v
    Real.log ((likelihood (windowHistory m t j s) i).toReal /
      (likelihood (windowHistory m t j s) k).toReal) ≤
      18/(w:ℝ) + suffixLogRatio j s k i := by
  dsimp only
  obtain ⟨hm,ht,hd,hT⟩ := growing_counts k w u v hw hu hv
  rw [window_log_ratio]
  have hpair := pair_quadratic _ _ hm ht (rate k) (rate i)
    (ratio_interior k).1 (ratio_interior k).2 (ratio_interior i).1 (ratio_interior i).2
  have hw' : (0:ℝ) < w := by exact_mod_cast (by omega : 0 < w)
  have hr := (FourthSegmentLawRecovery.Rates.xi_bounds k).1
  change (2/9:ℝ) ≤ (rate k:ℝ)*(1-(rate k:ℝ)) at hr
  let m := windowCount w (rate k) u
  let t := windowCount w (1-(rate k:ℝ)) v
  let d := (m:ℝ)-(rate k:ℝ)*(m+t)
  have hd' : d^2 ≤ (w:ℝ)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg d) hw'.le).mpr hd
  have hT' : (0:ℝ) < m+t := by exact_mod_cast (Nat.add_pos_left hm t)
  have hden : (w:ℝ)^3/9 ≤ ((m:ℝ)+t)*(rate k:ℝ)*(1-(rate k:ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hr hT'.le
    nlinarith
  have hden0 : 0 < ((m:ℝ)+t)*(rate k:ℝ)*(1-(rate k:ℝ)) :=
    lt_of_lt_of_le (by positivity : (0:ℝ) < (w:ℝ)^3/9) hden
  have hquad : 2*d^2/(((m:ℝ)+t)*(rate k:ℝ)*(1-(rate k:ℝ))) ≤ 18/(w:ℝ) := by
    apply (div_le_div_iff₀ hden0 hw').mpr
    nlinarith [mul_le_mul_of_nonneg_right hd' hw'.le]
  have h := hpair.trans hquad
  gcongr

#print axioms native_growing_window_likelihood

open Filter Topology

private def nativeEntropy (k i : Depth) : ℝ :=
  (rate k:ℝ)*Real.log ((rate i:ℝ)/(rate k:ℝ)) +
    (1-(rate k:ℝ))*Real.log ((1-(rate i:ℝ))/(1-(rate k:ℝ)))

private def logError (k i : Depth) : ℝ :=
  |Real.log ((rate i:ℝ)/(rate k:ℝ))| +
    |Real.log ((1-(rate i:ℝ))/(1-(rate k:ℝ)))|

private theorem suffix_bound (j : ℕ) (s : ActivePhase) (k i : Depth) :
    suffixLogRatio j s k i ≤ (7+2*j:ℕ) := by
  have hr := FourthSegmentLawRecovery.Rates.rate_bounds k
  have ha := FourthSegmentLawRecovery.Rates.rate_bounds i
  have h1 : Real.log ((rate i:ℝ)/(rate k:ℝ)) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos
      (div_pos (ratio_interior i).1 (ratio_interior k).1)
    change Real.log ((rate i:ℝ)/(rate k:ℝ)) ≤ (rate i:ℝ)/(rate k:ℝ)-1 at h
    have hb : (rate i:ℝ)/(rate k:ℝ) ≤ 2 := by
      apply (div_le_iff₀ (ratio_interior k).1).mpr
      change (rate i:ℝ) ≤ 2*(rate k:ℝ)
      linarith
    linarith
  have h2 : Real.log ((1-(rate i:ℝ))/(1-(rate k:ℝ))) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos
      (div_pos (sub_pos.mpr (ratio_interior i).2) (sub_pos.mpr (ratio_interior k).2))
    change Real.log ((1-(rate i:ℝ))/(1-(rate k:ℝ))) ≤
      (1-(rate i:ℝ))/(1-(rate k:ℝ))-1 at h
    have hb : (1-(rate i:ℝ))/(1-(rate k:ℝ)) ≤ 2 := by
      apply (div_le_iff₀ (sub_pos.mpr (ratio_interior k).2)).mpr
      change 1-(rate i:ℝ) ≤ 2*(1-(rate k:ℝ))
      linarith
    linarith
  have h1' := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ (3+j:ℕ) by positivity)
  cases s <;> dsimp [suffixLogRatio] <;> push_cast at *
  · have h2' := mul_le_mul_of_nonneg_left h2 (show (0:ℝ) ≤ 3+j by positivity)
    linarith
  · have h2' := mul_le_mul_of_nonneg_left h2 (show (0:ℝ) ≤ 3+j+1 by positivity)
    linarith

private theorem floor_window_error (w u : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hw : 2 ≤ w) (hu : u < w) :
    |(windowCount w r u:ℝ)-(w:ℝ)^3*r| ≤ w := by
  have hL := Nat.lt_floor_add_one ((w:ℝ)^3*r)
  have hU := Nat.floor_le (show 0 ≤ (w:ℝ)^3*r by positivity)
  have hu' : (u:ℝ)+1 ≤ w := by exact_mod_cast (Nat.succ_le_iff.mpr hu)
  have hw' : (2:ℝ) ≤ w := by exact_mod_cast hw
  unfold windowCount
  push_cast
  apply abs_le.mpr
  constructor <;> linarith [(Nat.cast_nonneg u : (0:ℝ) ≤ u)]

private theorem growing_log_linear (k i : Depth) (w u v j : ℕ) (s : ActivePhase)
    (hw : 2 ≤ w) (hu : u < w) (hv : v < w) :
    Real.log ((likelihood (windowHistory (windowCount w (rate k) u)
      (windowCount w (1-(rate k:ℝ)) v) j s) i).toReal /
      (likelihood (windowHistory (windowCount w (rate k) u)
      (windowCount w (1-(rate k:ℝ)) v) j s) k).toReal) ≤
      2*((w:ℝ)^3*nativeEntropy k i + (w:ℝ)*logError k i) + suffixLogRatio j s k i := by
  rw [window_log_ratio]
  let a := Real.log ((rate i:ℝ)/(rate k:ℝ))
  let b := Real.log ((1-(rate i:ℝ))/(1-(rate k:ℝ)))
  let m := windowCount w (rate k) u
  let t := windowCount w (1-(rate k:ℝ)) v
  have hm := floor_window_error w u (rate k) (ratio_interior k).1.le hw hu
  have ht := floor_window_error w v (1-(rate k:ℝ))
    (sub_nonneg.mpr (ratio_interior k).2.le) hw hv
  have hma : ((m:ℝ)-(w:ℝ)^3*(rate k:ℝ))*a ≤ (w:ℝ)*|a| := by
    calc
      _ ≤ |((m:ℝ)-(w:ℝ)^3*(rate k:ℝ))*a| := le_abs_self _
      _ = |(m:ℝ)-(w:ℝ)^3*(rate k:ℝ)| * |a| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hm (abs_nonneg a)
  have htb : ((t:ℝ)-(w:ℝ)^3*(1-(rate k:ℝ)))*b ≤ (w:ℝ)*|b| := by
    calc
      _ ≤ |((t:ℝ)-(w:ℝ)^3*(1-(rate k:ℝ)))*b| := le_abs_self _
      _ = |(t:ℝ)-(w:ℝ)^3*(1-(rate k:ℝ))| * |b| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right ht (abs_nonneg b)
  dsimp [pairLogRatio, nativeEntropy, logError]
  change 2*((m:ℝ)*a+(t:ℝ)*b)+_ ≤
    2*((w:ℝ)^3*((rate k:ℝ)*a+(1-(rate k:ℝ))*b)+(w:ℝ)*(|a|+|b|))+_
  linarith

private def competitorEnvelope (w j : ℕ) (s : ActivePhase) (k i : Depth) : ℝ :=
  min (Real.exp (16+2*(j:ℝ)))
    (Real.exp (2*((w:ℝ)^3*nativeEntropy k i+(w:ℝ)*logError k i) + suffixLogRatio j s k i))

private theorem competitor_nonneg (w j : ℕ) (s : ActivePhase) (k i : Depth) :
    0 ≤ competitorEnvelope w j s k i := le_min (Real.exp_pos _).le (Real.exp_pos _).le

private theorem cubic_decay (D E C : ℝ) (hD : D < 0) :
    Tendsto (fun w : ℕ => Real.exp (2*((w:ℝ)^3*D+(w:ℝ)*E)+C)) atTop (𝓝 0) := by
  have hW : Tendsto (fun w : ℕ => (w:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hQ : Tendsto (fun w : ℕ => (w:ℝ)^2*D+E) atTop atBot :=
    (Tendsto.atTop_mul_const_of_neg hD
      ((tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0)).comp hW)).atBot_add
      tendsto_const_nhds
  apply Real.tendsto_exp_atBot.comp
  apply tendsto_atBot_mono' _ ?_ (((tendsto_neg_atTop_atBot.comp hW).atBot_add tendsto_const_nhds) :
    Tendsto (fun w : ℕ => -(w:ℝ)+C) atTop atBot)
  filter_upwards [hQ.eventually_le_atBot (-1)] with w hw
  have h := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg w : (0:ℝ) ≤ w)
  simp only [Function.comp_apply] at *
  ring_nf at h ⊢
  linarith [(Nat.cast_nonneg w : (0:ℝ) ≤ w)]

private theorem competitor_tendsto (j : ℕ) (s : ActivePhase) (k i : Depth) (hi : i ≠ k) :
    Tendsto (fun w => competitorEnvelope w j s k i) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => competitor_nonneg _ _ _ _ _) (fun _ => min_le_right _ _)
  exact cubic_decay _ _ _ (strict_native_log k i hi)

private theorem likelihood_finite (h : List Operation) (k : Depth) : likelihood h k ≠ ∞ := by
  rw [likelihood, word_counts]
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp [alphaMass]))
    (ENNReal.pow_ne_top (by simp [betaMass]))

private theorem likelihood_real_pos (h : List Operation) (k : Depth) :
    0 < (likelihood h k).toReal :=
  ENNReal.toReal_pos (likelihood_pos h k).ne' (likelihood_finite h k)

private theorem ratio_envelope (k i : Depth) (w u v j : ℕ) (s : ActivePhase)
    (hw : 2 ≤ w) (hu : u < w) (hv : v < w) :
    let h := windowHistory (windowCount w (rate k) u) (windowCount w (1-(rate k:ℝ)) v) j s
    (likelihood h i).toReal/(likelihood h k).toReal ≤ competitorEnvelope w j s k i := by
  dsimp only
  let h := windowHistory (windowCount w (rate k) u) (windowCount w (1-(rate k:ℝ)) v) j s
  have he : Real.exp (Real.log ((likelihood h i).toReal/(likelihood h k).toReal)) =
      (likelihood h i).toReal/(likelihood h k).toReal :=
    Real.exp_log (div_pos (likelihood_real_pos h i) (likelihood_real_pos h k))
  apply le_min
  · rw [← he]
    apply Real.exp_le_exp.mpr
    have h1 := native_growing_window_likelihood k i w u v j s hw hu hv
    have h2 := suffix_bound j s k i
    have hw' : (2:ℝ) ≤ w := by exact_mod_cast hw
    have h3 : 18/(w:ℝ) ≤ 9 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    push_cast at h2
    linarith
  · rw [← he]
    exact Real.exp_le_exp.mpr (growing_log_linear k i w u v j s hw hu hv)

private def posteriorEnvelope (μ : PMF Depth) (k : Depth) (j : ℕ)
    (s : ActivePhase) (w : ℕ) : ℝ :=
  ∑' i, if i = k then 0 else (μ i).toReal * competitorEnvelope w j s k i

private theorem posterior_envelope_summable (μ : PMF Depth) (k : Depth) (j : ℕ)
    (s : ActivePhase) (w : ℕ) :
    Summable (fun i => if i = k then 0 else (μ i).toReal * competitorEnvelope w j s k i) := by
  apply Summable.of_nonneg_of_le
    (g := fun i : Depth => if i = k then 0 else
      (μ i).toReal * competitorEnvelope w j s k i)
    (fun i => by
      split_ifs
      · exact le_rfl
      · exact mul_nonneg ENNReal.toReal_nonneg (competitor_nonneg w j s k i))
    (fun i => ?_) ((FourthSegmentLawRecovery.RealAtoms.pmf_real_summable μ).mul_right
      (Real.exp (16+2*(j:ℝ))))
  split_ifs
  · positivity
  · exact mul_le_mul_of_nonneg_left (min_le_left _ _) ENNReal.toReal_nonneg

private theorem posterior_envelope_tendsto (μ : PMF Depth) (k : Depth) (j : ℕ)
    (s : ActivePhase) : Tendsto (posteriorEnvelope μ k j s) atTop (𝓝 0) := by
  have hh := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    ((FourthSegmentLawRecovery.RealAtoms.pmf_real_summable μ).mul_right
      (Real.exp (16+2*(j:ℝ))))
    (g := fun _ : Depth => (0:ℝ)) (f := fun w i =>
      if i = k then 0 else (μ i).toReal * competitorEnvelope w j s k i) ?_ ?_
  · change Tendsto (fun w => ∑' i, if i = k then 0 else
      (μ i).toReal * competitorEnvelope w j s k i) atTop (𝓝 0)
    simpa only [tsum_zero] using hh
  · intro i
    by_cases hi : i = k
    · simp [hi]
    · simpa [hi] using (competitor_tendsto j s k i hi).const_mul (μ i).toReal
  · apply Eventually.of_forall
    intro w i
    by_cases hi : i = k
    · simp [hi]; positivity
    · simp only [hi, if_false, Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg ENNReal.toReal_nonneg (competitor_nonneg w j s k i))]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) ENNReal.toReal_nonneg

private theorem posterior_window_bound (μ : PMF Depth) (k : Depth) (hk : μ k ≠ 0)
    (w u v j : ℕ) (s : ActivePhase) (hw : 2 ≤ w) (hu : u < w) (hv : v < w) :
    let H := windowPhaseHistory (windowCount w (rate k) u)
      (windowCount w (1-(rate k:ℝ)) v) j s
    1-(posterior μ H.val.1 H.val.2 H.property.1 k).toReal ≤
      posteriorEnvelope μ k j s w / (μ k).toReal := by
  dsimp only
  let H := windowPhaseHistory (windowCount w (rate k) u)
    (windowCount w (1-(rate k:ℝ)) v) j s
  let L := (likelihood H.val.1 k).toReal
  let a := (μ k).toReal
  let b := posteriorEnvelope μ k j s w
  let R := (normalizer μ H.val.1).toReal / L
  have hL : 0 < L := likelihood_real_pos _ k
  have ha : 0 < a := ENNReal.toReal_pos hk (μ.apply_ne_top k)
  have hN := normalizer_bounds μ H.val.1 H.val.2 H.property.1
  have hNf : normalizer μ H.val.1 ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hN.2
  have hNr : 0 < (normalizer μ H.val.1).toReal := ENNReal.toReal_pos hN.1.ne' hNf
  have hreal : (normalizer μ H.val.1).toReal =
      ∑' i, (μ i).toReal*(likelihood H.val.1 i).toReal := by
    rw [normalizer, ENNReal.tsum_toReal_eq
      (fun i => ENNReal.mul_ne_top (μ.apply_ne_top i) (likelihood_finite _ i))]
    simp only [ENNReal.toReal_mul]
  have hsum : Summable (fun i => (μ i).toReal*(likelihood H.val.1 i).toReal) := by
    simpa only [ENNReal.toReal_mul] using ENNReal.summable_toReal hNf
  have hrat : Summable (fun i => (μ i).toReal*((likelihood H.val.1 i).toReal/L)) := by
    simpa only [div_eq_mul_inv, mul_assoc] using hsum.mul_right L⁻¹
  have hR : R = ∑' i, (μ i).toReal*((likelihood H.val.1 i).toReal/L) := by
    dsimp [R]
    rw [hreal, ← tsum_div_const]
    apply tsum_congr
    intro i
    ring
  have hsplit : R = a + ∑' i, if i = k then 0 else
      (μ i).toReal*((likelihood H.val.1 i).toReal/L) := by
    rw [hR, hrat.tsum_eq_add_tsum_ite k]
    simp [L, a, hL.ne']
  have hrest : (∑' i, if i = k then 0 else
      (μ i).toReal*((likelihood H.val.1 i).toReal/L)) ≤ b := by
    apply Summable.tsum_le_tsum
      (fun i => ?_) (hrat.congr_cofinite (by
        filter_upwards [eventually_cofinite_ne k] with i hi
        simp [hi]))
      (posterior_envelope_summable μ k j s w)
    by_cases hi : i = k
    · simp [hi]
    · simp only [hi, if_false]
      exact mul_le_mul_of_nonneg_left (ratio_envelope k i w u v j s hw hu hv)
        ENNReal.toReal_nonneg
  have hRa : a ≤ R := by
    rw [hsplit]
    exact le_add_of_nonneg_right (tsum_nonneg fun i => by
      split_ifs; exact le_rfl; exact mul_nonneg ENNReal.toReal_nonneg
        (div_nonneg ENNReal.toReal_nonneg hL.le))
  have hRb : R ≤ a+b := by rw [hsplit]; linarith
  have hp : (posterior μ H.val.1 H.val.2 H.property.1 k).toReal = a/R := by
    rw [posterior, PMF.normalize_apply]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv]
    change a*L*(normalizer μ H.val.1).toReal⁻¹ = a / ((normalizer μ H.val.1).toReal/L)
    field_simp
  rw [hp]
  apply (le_div_iff₀ ha).mpr
  have hR0 : 0 < R := div_pos hNr hL
  have h1 : (1-a/R)*R = R-a := by field_simp
  have h2 : 0 ≤ 1-a/R := sub_nonneg.mpr ((div_le_one hR0).mpr hRa)
  have h3 := mul_le_mul_of_nonneg_left hRa h2
  nlinarith

/-- A supported depth concentrates uniformly over the finite native windows.
The prior is arbitrary on the countable depth space, and each return suffix is fixed.
The posterior is that of each individual actual history. -/
theorem native_countable_posterior_concentration (μ : PMF Depth) (k : Depth)
    (hk : μ k ≠ 0) (j : ℕ) (s : ActivePhase) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w : ℕ in atTop, 2 ≤ w ∧
      ∀ u v : ℕ, u < w → v < w →
        let H := windowPhaseHistory (windowCount w (rate k) u)
          (windowCount w (1-(rate k:ℝ)) v) j s
        1-(posterior μ H.val.1 H.val.2 H.property.1 k).toReal < ε := by
  intro ε hε
  have ha : (μ k).toReal ≠ 0 := (ENNReal.toReal_pos hk (μ.apply_ne_top k)).ne'
  have ht : Tendsto (fun w => posteriorEnvelope μ k j s w/(μ k).toReal) atTop (𝓝 0) := by
    simpa using (posterior_envelope_tendsto μ k j s).div_const (μ k).toReal
  filter_upwards [eventually_ge_atTop 2, ht.eventually (gt_mem_nhds hε)] with w hw hb
  refine ⟨hw, fun u v hu hv => ?_⟩
  exact (posterior_window_bound μ k hk w u v j s hw hu hv).trans_lt hb

#print axioms native_countable_posterior_concentration

/-- The pure original stopped-tail law, retaining its noncompletion outcome. -/
def pureTail (k : Depth) (s : ActivePhase) : Measure (ValidTail s) :=
  (rawReadLaw (rate k)).map (validStopped s)

instance (k : Depth) (s : ActivePhase) : IsProbabilityMeasure (pureTail k s) :=
  Measure.isProbabilityMeasure_map (validStopped_measurable s).aemeasurable

private theorem target_mixture_apply (μ : PMF Depth) (s : ActivePhase) (H : PhaseHistory s) (E : Set (ValidTail s)) (hE : MeasurableSet E) :
    rawTarget μ H.val.1 H.val.2 s E =
      ∑' i, posterior μ H.val.1 H.val.2 H.property.1 i * pureTail i s E := by
  let V : Depth × Stream → ValidTail s := fun t => validStopped s t.2
  let shift : Depth × Stream → Depth × Stream :=
    fun t => (t.1,rawTail t.2 (readLetters H.val.1).length)
  have hV : Measurable V := (validStopped_measurable s).comp measurable_snd
  have hs : Measurable shift := by dsimp [shift]; unfold rawTail; fun_prop
  change ((ProbabilityTheory.cond (jointLaw μ) (nativeEvent H.val.1 H.val.2)).map
    (V ∘ shift)) E = _
  rw [← Measure.map_map hV hs, NativeConditionalControl.Tail.sameK_conditional_tail μ
    H.val.1 H.val.2 H.property.1, Measure.map_apply hV hE,
    jointLaw, Measure.sum_apply_of_countable]
  apply tsum_congr
  intro i
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (by fun_prop) (hE.preimage hV),
    pureTail, Measure.map_apply (validStopped_measurable s) hE]
  rfl

private theorem countable_mixture_atom_tv {A : Type*} [MeasurableSpace A]
    (ν : PMF Depth) (P : Depth → Measure A) (Q : Measure A)
    (hP : ∀ i, IsProbabilityMeasure (P i))
    (hQ : ∀ E, MeasurableSet E → Q E = ∑' i, ν i*P i E) (k : Depth) :
    measurableTotalVariation Q (P k) ≤ 1-ν k := by
  classical
  have hν : ν k ≤ 1 := PMF.coe_le_one ν k
  have hrem : (∑' i, if i=k then 0 else ν i) = 1-ν k := by
    apply ENNReal.eq_sub_of_add_eq (ν.apply_ne_top k)
    rw [add_comm]
    convert (ENNReal.tsum_eq_add_tsum_ite (f := fun i => ν i) k).symm.trans ν.tsum_coe using 1
    congr 1
    apply tsum_congr
    intro i
    split_ifs <;> rfl
  have hpart : ν k+(1-ν k) = 1 := add_tsub_cancel_of_le hν
  unfold measurableTotalVariation
  apply iSup_le
  intro E
  have hmass (i : Depth) : P i E.val ≤ 1 := by
    haveI := hP i
    exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
  have hrest : (∑' i, if i=k then 0 else ν i*P i E.val) ≤ 1-ν k := by
    rw [← hrem]
    apply ENNReal.tsum_le_tsum
    intro i
    split_ifs
    · exact le_rfl
    · exact mul_le_of_le_one_right zero_le (hmass i)
  have hl : ν k*P k E.val ≤ Q E.val := by
    rw [hQ E.val E.property]
    exact ENNReal.le_tsum k
  have hu : Q E.val ≤ ν k*P k E.val+(1-ν k) := by
    rw [hQ E.val E.property, ENNReal.tsum_eq_add_tsum_ite k]
    convert add_le_add (le_refl (ν k * P k E.val)) hrest using 1 <;> try rfl
    apply congrArg (fun a : ℝ≥0∞ => ν k * P k E.val + a)
    apply tsum_congr
    intro i
    split_ifs <;> rfl
  apply max_le
  · apply (tsub_le_iff_right).mpr
    have hm : ν k * P k E.val ≤ P k E.val :=
      mul_le_of_le_one_left zero_le hν
    exact hu.trans (by simpa only [add_comm] using add_le_add hm (le_refl (1-ν k)))
  · apply (tsub_le_iff_right).mpr
    calc
      P k E.val = (ν k+(1-ν k))*P k E.val := by rw [hpart, one_mul]
      _ = ν k*P k E.val+(1-ν k)*P k E.val := add_mul _ _ _
      _ ≤ (1-ν k)+Q E.val := by
        have hm : (1-ν k)*P k E.val ≤ 1-ν k :=
          mul_le_of_le_one_right zero_le (hmass k)
        simpa only [add_comm] using add_le_add hl hm

/-- The original countable stopped-tail target collapses, in total variation,
to the supported depth's complete law. No finite outcome approximation is used. -/
theorem native_countable_target_concentration (μ : PMF Depth) (k : Depth)
    (hk : μ k ≠ 0) (j : ℕ) (s : ActivePhase) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w : ℕ in atTop, 2 ≤ w ∧
      ∀ u v : ℕ, u < w → v < w →
        let H := windowPhaseHistory (windowCount w (rate k) u)
          (windowCount w (1-(rate k:ℝ)) v) j s
        (measurableTotalVariation (rawTarget μ H.val.1 H.val.2 s) (pureTail k s)).toReal < ε := by
  intro ε hε
  filter_upwards [native_countable_posterior_concentration μ k hk j s ε hε]
    with w hw
  refine ⟨hw.1, fun u v hu hv => ?_⟩
  let H := windowPhaseHistory (windowCount w (rate k) u)
    (windowCount w (1-(rate k:ℝ)) v) j s
  have ht : measurableTotalVariation (rawTarget μ H.val.1 H.val.2 s) (pureTail k s) ≤
      1-posterior μ H.val.1 H.val.2 H.property.1 k := by
    apply countable_mixture_atom_tv _ (fun i => pureTail i s) _ (fun _ => inferInstance)
    intro E hE
    exact target_mixture_apply μ s H E hE
  have hf : 1-posterior μ H.val.1 H.val.2 H.property.1 k ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hb := ENNReal.toReal_mono hf ht
  rw [ENNReal.toReal_sub_of_le (PMF.coe_le_one _ _) ENNReal.one_ne_top,
    ENNReal.toReal_one] at hb
  exact hb.trans_lt (hw.2 u v hu hv)

#print axioms native_countable_target_concentration


local instance : DecidableEq Z := Classical.decEq Z

private theorem prefix_coupling {W : Type*} [Fintype W] (P Q : W → PMF W)
    (G : Set W) (hrow : ∀ w ∈ G, P w = Q w)
    (hclosed : ∀ w ∈ G, ∀ v ∈ (P w).support, v ∈ G) (w : W) (hw : w ∈ G) :
    ∀ (n : ℕ) (v : Fin (n+1) → W),
      ((if v 0=w then 1 else 0)*∏ i : Fin n, P (v i.castSucc) (v i.succ)) =
        ((if v 0=w then 1 else 0)*∏ i : Fin n, Q (v i.castSucc) (v i.succ)) ∧
      (((if v 0=w then 1 else 0)*∏ i : Fin n, P (v i.castSucc) (v i.succ)) ≠ 0 →
        v (Fin.last n) ∈ G) := by
  classical
  intro n
  induction n with
  | zero =>
    intro v
    simp only [Fin.prod_univ_zero, mul_one]
    refine ⟨True.intro, ?_⟩
    intro h
    by_cases hv : v 0=w
    · simpa only [Fin.last_zero, hv] using hw
    · simp [hv] at h
  | succ n ih =>
    intro v
    let vp : Fin (n+1) → W := fun i => v i.castSucc
    obtain ⟨he,hg⟩ := ih vp
    have hp : (if v 0=w then (1:ℝ≥0∞) else 0)*∏ i : Fin (n+1), P (v i.castSucc) (v i.succ) =
        ((if vp 0=w then 1 else 0)*∏ i : Fin n, P (vp i.castSucc) (vp i.succ))*
          P (v (Fin.last n).castSucc) (v (Fin.last (n+1))) := by
      rw [Fin.prod_univ_castSucc, ← mul_assoc]
      rfl
    have hq : (if v 0=w then (1:ℝ≥0∞) else 0)*∏ i : Fin (n+1), Q (v i.castSucc) (v i.succ) =
        ((if vp 0=w then 1 else 0)*∏ i : Fin n, Q (vp i.castSucc) (vp i.succ))*
          Q (v (Fin.last n).castSucc) (v (Fin.last (n+1))) := by
      rw [Fin.prod_univ_castSucc, ← mul_assoc]
      rfl
    rw [hp, hq]
    by_cases hz : ((if vp 0=w then (1:ℝ≥0∞) else 0)*∏ i : Fin n,
      P (vp i.castSucc) (vp i.succ)) = 0
    · rw [hz, ← he, hz, zero_mul, zero_mul]
      exact ⟨rfl, fun h => False.elim (h rfl)⟩
    · have hv : v (Fin.last n).castSucc ∈ G := hg hz
      have hr := hrow _ hv
      refine ⟨by rw [he, hr], ?_⟩
      intro h
      have ha : P (v (Fin.last n).castSucc) (v (Fin.last (n+1))) ≠ 0 := by
        intro ha; exact h (by rw [ha, mul_zero])
      exact hclosed _ hv _ ((PMF.mem_support_iff _ _).mpr ha)

/-- Equality of supported acquired generators determines their entire infinite path law.
The finite-prefix equality is extended by projective uniqueness, retaining noncompletion. -/
theorem installed_law_invariant (M N : Observer Z) (e : InstalledEmitter M)
    (f : InstalledEmitter N) (G : Set Z)
    (hrow : ∀ z ∈ G, ∀ a, markedRow M e (z,a) = markedRow N f (z,a))
    (hclosed : ∀ z ∈ G, ∀ a, ∀ v ∈ (markedRow M e (z,a)).support, v.1 ∈ G)
    (hproject : N.project = M.project) (z : Z) (hz : z ∈ G) :
    markedLaw N f (z,none) = markedLaw M e (z,none) ∧
      fullLaw N f z = fullLaw M e z ∧
      (∀ s : ActivePhase, tailLaw N f s z = tailLaw M e s z) := by
  let Gw : Set (Marked Z) := {w | w.1 ∈ G}
  have h := prefix_coupling (markedRow M e) (markedRow N f) Gw
    (fun w hw => hrow w.1 hw w.2) (fun w hw v hv => hclosed w.1 hw w.2 v hv) (z,none) hz
  have hl : markedLaw M e (z,none) = markedLaw N f (z,none) := by
    apply path_ext
    intro n
    apply Measure.ext_of_singleton
    intro v
    rw [prefix_mass, prefix_mass]
    by_cases hv : v 0 = (z,none)
    · simpa only [if_pos hv] using (h n v).1
    · simp only [if_neg hv, zero_mul]
  refine ⟨hl.symm, ?_, ?_⟩
  · unfold fullLaw
    rw [← hl]
    congr 1
    funext x n
    simp only [markedTranscript, hproject]
  · intro s
    unfold tailLaw
    rw [← hl]

#print axioms installed_law_invariant

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRow
