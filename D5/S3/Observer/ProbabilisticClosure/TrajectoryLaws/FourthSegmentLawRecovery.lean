/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original fourth-segment length laws recover phase, countable depth posterior and residual transcript laws. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

set_option autoImplicit false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Boundary
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Prefix D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.DepthLaw D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Tail
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Stopping

private theorem pending_permissions (c : AcquiredNativeState) (b : Letter)
    (hc : c.source.finiteFields.control = .fourth (.pending b)) (ω : Stream) :
    nativeDrive c ω 0 = some ([],c,0) ∧
    nativeDrive c ω 1 = some ([.stop b],delivered c,0) ∧
    (∀ n : ℕ, nativeDrive c ω (n+2) = none) ∧
    (∀ x : Letter, nativeRead c x = none) ∧
    (∀ a : Letter, a ≠ b → nativeStop c a = none) := by
  refine ⟨rfl,?_,?_,?_,?_⟩
  · simp [nativeDrive,nextNative,nextOperation,nativeStep,nativeStop,finiteStop,hc,
      readCost,delivered]
  · intro n
    rw [show n+2=1+(n+1) by omega,drive_append]
    have h1 : nativeDrive c ω 1 = some ([.stop b],delivered c,0) := by
      simp [nativeDrive,nextNative,nextOperation,nativeStep,nativeStop,finiteStop,hc,
        readCost,delivered]
    rw [h1]
    simp [delivered_positive_none (delivered c) rfl]
  · intro x
    simp [nativeRead,finiteRead,hc]
  · intro a hab
    simp [nativeStop,finiteStop,hc,hab]

private theorem terminal_paid_zero (c : AcquiredNativeState) (ω : Stream) (n : ℕ)
    (ops : List Operation) (d : AcquiredNativeState) (paid : ℕ)
    (hc : (∃ b : Letter, c.source.finiteFields.control = .fourth (.pending b)) ∨
      c.source.finiteFields.control = .fourth .delivered)
    (hd : nativeDrive c ω n = some (ops,d,paid)) : paid = 0 := by
  cases n with
  | zero =>
    have he := Option.some.inj hd
    exact (Prod.mk.inj ((Prod.mk.inj he).2)).2.symm
  | succ n =>
    rcases hc with ⟨b,hb⟩ | hdel
    · cases n with
      | zero =>
        have h1 := (pending_permissions c b hb ω).2.1
        have he := Option.some.inj (h1.symm.trans hd)
        exact (Prod.mk.inj ((Prod.mk.inj he).2)).2.symm
      | succ n =>
        have hn := (pending_permissions c b hb ω).2.2.1 n
        rw [hn] at hd
        contradiction
    · rw [delivered_positive_none c hdel] at hd
      contradiction

private theorem native_no_earlier_terminal (c e : AcquiredNativeState) (ω : Stream)
    (w : List Letter) (hword : nativeDrive c ω w.length = some (reads w,e,w.length))
    (n : ℕ) (hn : n < w.length) (ops : List Operation) (d : AcquiredNativeState)
    (paid : ℕ) (hprefix : nativeDrive c ω n = some (ops,d,paid)) :
    (∀ b : Letter, d.source.finiteFields.control ≠ .fourth (.pending b)) ∧
      d.source.finiteFields.control ≠ .fourth .delivered := by
  have ht : ¬((∃ b : Letter, d.source.finiteFields.control = .fourth (.pending b)) ∨
      d.source.finiteFields.control = .fourth .delivered) := by
    intro hterminal
    have hm : w.length = n+(w.length-n) := by omega
    rw [hm,drive_append,hprefix] at hword
    simp only [Option.bind_some,Option.map_eq_some_iff] at hword
    obtain ⟨⟨v,f,j⟩,hsuffix,he⟩ := hword
    have hj := terminal_paid_zero d (rawTail ω paid) (w.length-n) v f j hterminal hsuffix
    have hspec := (drive_spec n c d ω ops paid).mp hprefix
    have hp : paid ≤ n := by
      rw [hspec.2.2.2,← hspec.1,erasure_eq]
      exact List.length_filterMap_le eraseOp ops
    have hcursor := (Prod.mk.inj ((Prod.mk.inj he).2)).2
    dsimp only at hcursor
    omega
  exact ⟨fun b hb => ht (Or.inl ⟨b,hb⟩),fun hd => ht (Or.inr hd)⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Boundary

set_option autoImplicit false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Infinite
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Prefix D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.DepthLaw D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Tail
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Stopping D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Boundary

private theorem loop_length (j : ℕ) : (loopWord j).length = 2*j := by
  rw [loop_as_prefix,prefix_length]

private theorem infinite_p_prefix (j : ℕ) (s : ActivePhase) :
    Prefix (infiniteTail .p) (loopWord j ++ phaseWord s) := by
  cases s with
  | p => simp [phaseWord,Prefix,loop_length,← loop_as_prefix]
  | beta =>
    simp only [phaseWord,Prefix,List.length_append,loop_length,List.length_singleton]
    rw [readPrefix,List.ofFn_succ_last]
    change readPrefix (infiniteTail .p) (2*j) ++ [infiniteTail .p (2*j)] = loopWord j ++ [1]
    rw [← loop_as_prefix]
    simp [infiniteTail]

private theorem active_cut_execute (r : Registers) (S : ℕ) (C : Counts) (j : ℕ) (s : ActivePhase) :
    execute (atPhase 3 r S C .p) (reads (loopWord j ++ phaseWord s)) =
      some (atPhase 3 r (S+j)
        ⟨C.alpha+j,C.beta+j+(match s with | .p => 0 | .beta => 1)⟩ s) := by
  rcases C with ⟨A,B⟩
  cases s with
  | p =>
    simpa [freshPayload,reconstructPayload,renderPayload,atPhase] using
      execute_payload (.active (n := 0) (last := (0 : Letter)) j .p) 3 r S ⟨A,B⟩ (by omega)
  | beta =>
    simpa [freshPayload,reconstructPayload,renderPayload,atPhase] using
      execute_payload (.active (n := 0) (last := (0 : Letter)) j .beta) 3 r S ⟨A,B⟩ (by omega)

private theorem infinite_p_native_active (r : Registers) (S : ℕ) (C : Counts) (n : ℕ) :
    ∃ (ops : List Operation) (d : AcquiredNativeState) (paid : ℕ) (s : ActivePhase),
      nativeDrive (atPhase 3 r S C .p) (infiniteTail .p) n = some (ops,d,paid) ∧
      d.source.finiteFields.control = .fourth (.active s) := by
  have hn := Nat.mod_two_eq_zero_or_one n
  rcases hn with hn | hn
  · have he : n=2*(n/2) := by omega
    let w := loopWord (n/2) ++ phaseWord .p
    refine ⟨reads w,atPhase 3 r (S+n/2) ⟨C.alpha+n/2,C.beta+n/2⟩ .p,w.length,.p,?_,rfl⟩
    apply (drive_spec _ _ _ _ _ _).mpr
    exact ⟨by simpa only [reads,List.length_map,w,phaseWord,List.length_append,loop_length,
        List.length_nil,Nat.add_zero] using he.symm,
      by simpa [w] using active_cut_execute r S C (n/2) .p,
      by simpa [w] using infinite_p_prefix (n/2) .p,by simp⟩
  · have he : n=2*(n/2)+1 := by omega
    let w := loopWord (n/2) ++ phaseWord .beta
    refine ⟨reads w,atPhase 3 r (S+n/2) ⟨C.alpha+n/2,C.beta+n/2+1⟩ .beta,
      w.length,.beta,?_,rfl⟩
    apply (drive_spec _ _ _ _ _ _).mpr
    exact ⟨by simpa only [reads,List.length_map,w,phaseWord,List.length_append,loop_length,
        List.length_singleton] using he.symm,
      active_cut_execute r S C (n/2) .beta,
      by simpa [w] using infinite_p_prefix (n/2) .beta,by simp⟩

private theorem infinite_beta_shift : rawTail (infiniteTail .beta) 1 = infiniteTail .p := by
  funext i
  rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;>
    simp [rawTail,infiniteTail,Nat.add_mod,hi]

private theorem infinite_beta_native_active (r : Registers) (S : ℕ) (C : Counts) (n : ℕ) :
    ∃ (ops : List Operation) (d : AcquiredNativeState) (paid : ℕ) (s : ActivePhase),
      nativeDrive (atPhase 3 r S C .beta) (infiniteTail .beta) n = some (ops,d,paid) ∧
      d.source.finiteFields.control = .fourth (.active s) := by
  cases n with
  | zero => exact ⟨[],atPhase 3 r S C .beta,0,.beta,rfl,rfl⟩
  | succ n =>
    have hfirst : nativeDrive (atPhase 3 r S C .beta) (infiniteTail .beta) 1 =
        some ([.read 0],atPhase 3 r (S+1) ⟨C.alpha+1,C.beta⟩ .p,1) := by
      apply (drive_spec _ _ _ _ _ _).mpr
      exact ⟨rfl,by simpa [execute,reads] using beta_return r S C [],rfl,rfl⟩
    obtain ⟨ops,d,paid,s,hd,hc⟩ := infinite_p_native_active r (S+1) ⟨C.alpha+1,C.beta⟩ n
    refine ⟨.read 0 :: ops,d,1+paid,s,?_,hc⟩
    rw [show n+1=1+n by omega,drive_append,hfirst]
    simp [infinite_beta_shift,hd]

theorem infinite_tail_native_noncompletion (c : AcquiredNativeState) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s)) :
    stoppedReadWord s (infiniteTail s) = none ∧
    ∀ n : ℕ, ¬ ∃ ops d paid,
      nativeDrive c (infiniteTail s) n = some (ops,d,paid) ∧
      d.source.finiteFields.control = .fourth .delivered := by
  refine ⟨(noncompletion_fiber _ _).mpr rfl,?_⟩
  intro n
  rcases c with ⟨⟨⟨ctrl,r⟩,S⟩,C⟩
  dsimp at hs
  subst ctrl
  have hex : ∃ ops d paid t,
      nativeDrive (atPhase 3 r S C s) (infiniteTail s) n = some (ops,d,paid) ∧
      d.source.finiteFields.control = .fourth (.active t) := by
    cases s with
    | p => exact infinite_p_native_active r S C n
    | beta => exact infinite_beta_native_active r S C n
  obtain ⟨ops,d,paid,t,hd,hactive⟩ := hex
  rintro ⟨ops',d',paid',hd',hdel⟩
  have he := (Prod.mk.inj ((Prod.mk.inj (Option.some.inj (hd.symm.trans hd'))).2)).1
  rw [← he,hactive] at hdel
  simp at hdel

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Infinite

set_option autoImplicit false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.WordLaw
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.DepthLaw D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Tail D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Stopping
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Control

def lastLetter (w : List Letter) : Letter := w.getLast?.getD 0
def nativeRenderer (c : AcquiredNativeState) (t : RawTail) : NativeOutput :=
  t.bind fun w => (execute c (reads w ++ [.stop (lastLetter w)])).map
    fun d => (reads w ++ [.stop (lastLetter w)],d,w.length)
def nativeStopped (c : AcquiredNativeState) (s : ActivePhase) (ω : Stream) : NativeOutput :=
  (stoppedReadWord s ω).bind fun w => nativeDrive c ω (w.length+1)
private theorem family_last (s : ActivePhase) (b : Letter) (w : List Letter)
    (hf : WordFamily s b w) : lastLetter w = b := by
  cases s with
  | p => obtain ⟨j,rfl⟩ := hf; fin_cases b <;> simp [lastLetter,pWord]
  | beta =>
    rcases hf with ⟨rfl,rfl⟩ | ⟨j,rfl⟩
    · rfl
    · fin_cases b
      · change ((0 :: loopWord j) ++ [0]).getLast?.getD 0 = 0
        rw [List.getLast?_append_of_ne_nil _ (by simp)]; rfl
      · change ((0 :: loopWord j) ++ [1,1]).getLast?.getD 0 = 1
        rw [List.getLast?_append_of_ne_nil _ (by simp)]; rfl

theorem native_renderer_eq (c : AcquiredNativeState) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s)) (ω : Stream) :
    nativeStopped c s ω = nativeRenderer c (stoppedReadWord s ω) := by
  cases hw : stoppedReadWord s ω with
  | none => simp [nativeStopped,nativeRenderer,hw]
  | some w =>
    obtain ⟨b,d,hf,hd,_⟩ := (native_stopped_iff c s hs ω w).mp hw
    have he := ((drive_spec _ _ _ _ _ _).mp hd).2.1
    simp [nativeStopped,nativeRenderer,hw,hd,family_last s b w hf,he]

def wordLaw (μ : PMF Depth) (h : List Operation) (c : AcquiredNativeState)
    (s : ActivePhase) : Measure RawTail :=
  (ProbabilityTheory.cond (jointLaw μ) (nativeEvent h c)).map
    (fun z => stoppedReadWord s (rawTail z.2 (readLetters h).length))
def wordMixture (ν : PMF Depth) (s : ActivePhase) : Measure RawTail :=
  Measure.sum fun k => ν k • explicitStoppedWordLaw s (rate k)

theorem posterior_word_law (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c) (s : ActivePhase) :
    wordLaw μ h c s = wordMixture (posterior μ h c hc) s := by
  have hs : Measurable (fun z : Depth × Stream =>
      (z.1,rawTail z.2 (readLetters h).length)) := by unfold rawTail; fun_prop
  have hw : Measurable (fun z : Depth × Stream => stoppedReadWord s z.2) :=
    (measurable_stopped_read_word s).comp measurable_snd
  unfold wordLaw
  change (ProbabilityTheory.cond (jointLaw μ) (nativeEvent h c)).map
    ((fun z : Depth × Stream => stoppedReadWord s z.2) ∘
      (fun z : Depth × Stream => (z.1,rawTail z.2 (readLetters h).length))) = _
  rw [← Measure.map_map hw hs,sameK_conditional_tail μ h c hc]
  unfold jointLaw wordMixture
  rw [Measure.map_sum hw.aemeasurable]
  apply congrArg Measure.sum
  funext k
  rw [Measure.map_smul,Measure.map_map hw (by fun_prop)]
  exact congrArg (fun m => posterior μ h c hc k • m)
    (actual_fourth_segment_stopped_word_law (rate k) s).2

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.WordLaw

set_option autoImplicit false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Rates
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.DepthLaw

def xi (k : Depth) : ℝ := (rate k : ℝ)*(1-(rate k : ℝ))

theorem rate_bounds (k : Depth) : (1/3:ℝ) ≤ (rate k : ℝ) ∧ (rate k : ℝ) ≤ 2/5 := by
  have hb : (Nat.fib k.val : ℝ) ≤ Nat.fib (k.val+1) := by
    exact_mod_cast Nat.fib_mono (show k.val ≤ k.val+1 by omega)
  have ha : (Nat.fib (k.val+1) : ℝ) ≤ 2*Nat.fib k.val := by
    have hh := Nat.fib_mono (show k.val-1 ≤ k.val by omega)
    have hf := Nat.fib_add_one (show k.val ≠ 0 from k.ne_zero)
    exact_mod_cast (show Nat.fib (k.val+1) ≤ 2*Nat.fib k.val by omega)
  have hf : (Nat.fib (k.val+3) : ℝ) = 2*Nat.fib (k.val+1)+Nat.fib k.val := by
    have h1 : (Nat.fib (k.val+2) : ℝ) = Nat.fib k.val+Nat.fib (k.val+1) := by
      exact_mod_cast Nat.fib_add_two (n := k.val)
    have h2 : (Nat.fib (k.val+3) : ℝ) = Nat.fib (k.val+1)+Nat.fib (k.val+2) := by
      exact_mod_cast (show Nat.fib (k.val+3) = _ from by simpa [Nat.add_assoc] using Nat.fib_add_two (n := k.val+1))
    linarith
  have hd : 0 < (Nat.fib (k.val+3) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < k.val+3)
  change (1/3:ℝ) ≤ (Nat.fib (k.val+1):ℝ)/Nat.fib (k.val+3) ∧
    (Nat.fib (k.val+1):ℝ)/Nat.fib (k.val+3) ≤ 2/5
  constructor
  · apply (le_div_iff₀ hd).mpr; nlinarith
  · apply (div_le_iff₀ hd).mpr; nlinarith

private theorem fib_gap_coprime (k : Depth) :
    Nat.Coprime (Nat.fib (k.val+1)) (Nat.fib (k.val+3)) := by
  have h := Nat.fib_coprime_fib_succ (k.val+1)
  rw [show k.val+3 = (k.val+1)+2 by omega,Nat.fib_add_two,Nat.coprime_self_add_right]
  exact h

theorem rate_injective : Function.Injective (fun k : Depth => (rate k : ℝ)) := by
  intro k l he
  have hd (i : Depth) : 0 < (Nat.fib (i.val+3) : ℤ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < i.val+3)
  have hrat : (Nat.fib (k.val+1):ℚ)/Nat.fib (k.val+3) =
      (Nat.fib (l.val+1):ℚ)/Nat.fib (l.val+3) := by
    apply Rat.cast_injective (α := ℝ)
    simpa [rate] using he
  have hh := Rat.div_int_inj (a := (Nat.fib (k.val+1):ℤ)) (c := (Nat.fib (l.val+1):ℤ)) (hd k) (hd l)
    (by simpa using fib_gap_coprime k) (by simpa using fib_gap_coprime l)
    (by simpa using hrat)
  have hn : Nat.fib (k.val+1) = Nat.fib (l.val+1) := by exact_mod_cast hh.1
  have hi : k.val+1 = l.val+1 := Nat.fib_strictMonoOn.injOn
    (show k.val+1 ∈ Set.Ici 2 from Nat.succ_le_succ k.property)
    (show l.val+1 ∈ Set.Ici 2 from Nat.succ_le_succ l.property) hn
  apply Subtype.ext
  exact Nat.add_right_cancel hi

theorem xi_bounds (k : Depth) : (2/9:ℝ) ≤ xi k ∧ xi k ≤ 6/25 := by
  obtain ⟨hl,hu⟩ := rate_bounds k
  have hlp : 0 ≤ ((rate k:ℝ)-1/3)*(2/3-(rate k:ℝ)) :=
    mul_nonneg (by linarith) (by linarith)
  have hup : 0 ≤ (2/5-(rate k:ℝ))*(3/5-(rate k:ℝ)) :=
    mul_nonneg (by linarith) (by linarith)
  unfold xi
  constructor <;> nlinarith

private theorem xi_injective : Function.Injective xi := by
  intro k l he
  obtain ⟨_,hk⟩ := rate_bounds k
  obtain ⟨_,hl⟩ := rate_bounds l
  have hp : (1-(rate k:ℝ)-(rate l:ℝ)) ≠ 0 := by linarith
  have heq : ((rate k:ℝ)-(rate l:ℝ))*(1-(rate k:ℝ)-(rate l:ℝ)) = 0 := by
    unfold xi at he; nlinarith
  apply rate_injective
  exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right hp)

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Rates

set_option autoImplicit false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Length
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.DepthLaw D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.WordLaw D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Rates

instance : MeasurableSpace (Option ℕ) := ⊤
def lengthProjection (t : RawTail) : Option ℕ := t.map List.length
def lengthLaw (μ : PMF Depth) (h : List Operation) (c : AcquiredNativeState)
    (s : ActivePhase) : Measure (Option ℕ) :=
  (ProbabilityTheory.cond (jointLaw μ) (nativeEvent h c)).map
    (fun z => lengthProjection (stoppedReadWord s (rawTail z.2 (readLetters h).length)))
def lengthMixture (ν : PMF Depth) (s : ActivePhase) : Measure (Option ℕ) :=
  (wordMixture ν s).map lengthProjection

private theorem actual_length_projection (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState) (s : ActivePhase) :
    lengthLaw μ h c s = (wordLaw μ h c s).map lengthProjection := by
  unfold lengthLaw wordLaw
  exact (Measure.map_map (measurable_of_countable lengthProjection)
    ((measurable_stopped_read_word s).comp (by unfold rawTail; fun_prop))).symm

private theorem posterior_length_law (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c) (s : ActivePhase) :
    lengthLaw μ h c s = lengthMixture (posterior μ h c hc) s := by
  rw [actual_length_projection,posterior_word_law μ h c hc]
  rfl

private theorem p_kernel_atoms (r : unitInterval) (j : ℕ) :
    ((explicitStoppedWordLaw .p r).map lengthProjection) {some (2*j+1)} =
      alphaMass r*(alphaMass r*betaMass r)^j ∧
    ((explicitStoppedWordLaw .p r).map lengthProjection) {some (2*j+2)} =
      betaMass r^2*(alphaMass r*betaMass r)^j := by
  have hodd (i : ℕ) : 2*i+1 = 2*j+1 ↔ i = j := by omega
  have heven (i : ℕ) : 2*i+2 = 2*j+2 ↔ i = j := by omega
  have hno1 (i : ℕ) : ¬2*i+2 = 2*j+1 := by omega
  have hno2 (i : ℕ) : ¬2*i+1 = 2*j+2 := by omega
  have hn0 (i : ℕ) : ¬2*i = 2*j+1 := by omega
  constructor <;> simp [explicitStoppedWordLaw,Measure.map_apply
    (measurable_of_countable lengthProjection),Measure.sum_apply,lengthProjection,p_word_length,
    Set.indicator,hn0,hodd,heven,hno1,hno2,Pi.single_apply]

private theorem beta_kernel_atoms (r : unitInterval) (j : ℕ) :
    ((explicitStoppedWordLaw .beta r).map lengthProjection) {some 1} = betaMass r ∧
    ((explicitStoppedWordLaw .beta r).map lengthProjection) {some (2*j+2)} =
      alphaMass r^2*(alphaMass r*betaMass r)^j ∧
    ((explicitStoppedWordLaw .beta r).map lengthProjection) {some (2*j+3)} =
      alphaMass r*betaMass r^2*(alphaMass r*betaMass r)^j := by
  have heven (i : ℕ) : 2*i+1+1 = 2*j+2 ↔ i = j := by omega
  have hodd (i : ℕ) : 2*i+2+1 = 2*j+3 ↔ i = j := by omega
  have hn1 (i : ℕ) : ¬2*i+1+1 = 1 := by omega
  have hn2 (i : ℕ) : ¬2*i+2+1 = 1 := by omega
  have hn3 (i : ℕ) : ¬2*i+2+1 = 2*j+2 := by omega
  have hn4 (i : ℕ) : ¬2*i+1+1 = 2*j+3 := by omega
  have hn5 : ¬(1:ℕ) = 2*j+2 := by omega
  have hn6 : ¬(1:ℕ) = 2*j+3 := by omega
  have hna (i : ℕ) : ¬2*i+1 = 2*j := by omega
  have hnb (i : ℕ) : ¬2*i = 2*j+1 := by omega
  refine ⟨?_,?_,?_⟩ <;> simp [explicitStoppedWordLaw,Measure.map_apply
    (measurable_of_countable lengthProjection),Measure.sum_apply,lengthProjection,p_word_length,
    Set.indicator,hna,hnb,heven,hodd,hn1,hn2,hn3,hn4,hn5,hn6,Pi.single_apply]

private theorem length_mixture_singleton (ν : PMF Depth) (s : ActivePhase) (n : Option ℕ) :
    lengthMixture ν s {n} = ∑' k, ν k *
      ((explicitStoppedWordLaw s (rate k)).map lengthProjection) {n} := by
  unfold lengthMixture wordMixture
  rw [Measure.map_sum (measurable_of_countable lengthProjection).aemeasurable]
  simp [Measure.sum_apply,Measure.map_smul]

private theorem five_atoms (ν : PMF Depth) (j : ℕ) :
    lengthMixture ν .p {some (2*j+1)} =
      (∑' k,ν k*(alphaMass (rate k)*(alphaMass (rate k)*betaMass (rate k))^j)) ∧
    lengthMixture ν .p {some (2*j+2)} =
      (∑' k,ν k*(betaMass (rate k)^2*(alphaMass (rate k)*betaMass (rate k))^j)) ∧
    lengthMixture ν .beta {some 1} = (∑' k,ν k*betaMass (rate k)) ∧
    lengthMixture ν .beta {some (2*j+2)} =
      (∑' k,ν k*(alphaMass (rate k)^2*(alphaMass (rate k)*betaMass (rate k))^j)) ∧
    lengthMixture ν .beta {some (2*j+3)} =
      (∑' k,ν k*(alphaMass (rate k)*betaMass (rate k)^2*(alphaMass (rate k)*betaMass (rate k))^j)) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp only [length_mixture_singleton,(p_kernel_atoms _ _).1]
  · simp only [length_mixture_singleton,(p_kernel_atoms _ _).2]
  · simp only [length_mixture_singleton,(beta_kernel_atoms _ 0).1]
  · simp only [length_mixture_singleton,(beta_kernel_atoms _ _).2.1]
  · simp only [length_mixture_singleton,(beta_kernel_atoms _ _).2.2]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Length

set_option autoImplicit false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.RealAtoms
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.DepthLaw D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Rates D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Length

private theorem alpha_real (k : Depth) : (alphaMass (rate k)).toReal = (rate k:ℝ) := by
  simp [alphaMass]
private theorem beta_real (k : Depth) : (betaMass (rate k)).toReal = 1-(rate k:ℝ) := by
  simp [betaMass]
private theorem mass_finite (k : Depth) : alphaMass (rate k) ≠ ∞ ∧ betaMass (rate k) ≠ ∞ := by
  simp [alphaMass,betaMass]
private theorem pmf_real_sum (ν : PMF Depth) : (∑' k,(ν k).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (ν.apply_ne_top),ν.tsum_coe,ENNReal.toReal_one]
theorem pmf_real_summable (ν : PMF Depth) : Summable (fun k => (ν k).toReal) :=
  ENNReal.summable_toReal (by rw [ν.tsum_coe]; exact ENNReal.one_ne_top)

def mean (ν : PMF Depth) : ℝ := ∑' k,(ν k).toReal*(rate k:ℝ)

private theorem mean_summable (ν : PMF Depth) : Summable (fun k => (ν k).toReal*(rate k:ℝ)) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg ENNReal.toReal_nonneg (rate k).property.1)
    (fun k => mul_le_of_le_one_right ENNReal.toReal_nonneg (rate k).property.2)
    (pmf_real_summable ν)

private theorem mean_bounds (ν : PMF Depth) : (1/3:ℝ) ≤ mean ν ∧ mean ν ≤ 2/5 := by
  have hl := (pmf_real_summable ν).mul_right (1/3:ℝ)
  have hu := (pmf_real_summable ν).mul_right (2/5:ℝ)
  have hlo := hl.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (rate_bounds k).1 ENNReal.toReal_nonneg)
    (mean_summable ν)
  have hup := (mean_summable ν).tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_left (rate_bounds k).2 ENNReal.toReal_nonneg) hu
  simp only [tsum_mul_right,pmf_real_sum,one_mul] at hlo hup
  exact ⟨hlo,hup⟩

private theorem real_five_atoms (ν : PMF Depth) (j : ℕ) :
    (lengthMixture ν .p {some (2*j+1)}).toReal =
      (∑' k,(ν k).toReal*(rate k:ℝ)*xi k^j) ∧
    (lengthMixture ν .p {some (2*j+2)}).toReal =
      (∑' k,(ν k).toReal*(1-(rate k:ℝ))^2*xi k^j) ∧
    (lengthMixture ν .beta {some 1}).toReal = 1-mean ν ∧
    (lengthMixture ν .beta {some (2*j+2)}).toReal =
      (∑' k,(ν k).toReal*(rate k:ℝ)^2*xi k^j) ∧
    (lengthMixture ν .beta {some (2*j+3)}).toReal =
      (∑' k,(ν k).toReal*(rate k:ℝ)*(1-(rate k:ℝ))^2*xi k^j) := by
  have ht (f : Depth → ℝ≥0∞) (hf : ∀ k,f k ≠ ∞) :
      (∑' k,ν k*f k).toReal = ∑' k,(ν k).toReal*(f k).toReal := by
    rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.mul_ne_top (ν.apply_ne_top k) (hf k))]
    simp only [ENNReal.toReal_mul]
  obtain ⟨hp1,hp2,hb1,hb2,hb3⟩ := five_atoms ν j
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [hp1,ht _ (by intro k; simp [alphaMass,betaMass,ENNReal.mul_ne_top,ENNReal.pow_ne_top])]
    simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,alpha_real,beta_real,xi,mul_assoc]
  · rw [hp2,ht _ (by intro k; simp [alphaMass,betaMass,ENNReal.mul_ne_top,ENNReal.pow_ne_top])]
    simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,alpha_real,beta_real,xi,mul_assoc]
  · rw [hb1,ht _ (fun k => (mass_finite k).2)]
    simp only [beta_real]
    simp_rw [mul_sub,mul_one]
    rw [(pmf_real_summable ν).tsum_sub (mean_summable ν),pmf_real_sum]
    rfl
  · rw [hb2,ht _ (by intro k; simp [alphaMass,betaMass,ENNReal.mul_ne_top,ENNReal.pow_ne_top])]
    simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,alpha_real,beta_real,xi,mul_assoc]
  · rw [hb3,ht _ (by intro k; simp [alphaMass,betaMass,ENNReal.mul_ne_top,ENNReal.pow_ne_top])]
    simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,alpha_real,beta_real,xi,mul_assoc]

private theorem phase_intervals (ν : PMF Depth) :
    (1/3:ℝ) ≤ (lengthMixture ν .p {some 1}).toReal ∧
    (lengthMixture ν .p {some 1}).toReal ≤ 2/5 ∧
    (3/5:ℝ) ≤ (lengthMixture ν .beta {some 1}).toReal ∧
    (lengthMixture ν .beta {some 1}).toReal ≤ 2/3 := by
  have hp := (real_five_atoms ν 0).1
  have hb := (real_five_atoms ν 0).2.2.1
  simp only [Nat.mul_zero,Nat.zero_add,pow_zero,mul_one] at hp
  obtain ⟨hl,hu⟩ := mean_bounds ν
  change _ = mean ν at hp
  rw [hp,hb]
  exact ⟨hl,hu,by linarith,by linarith⟩

private theorem phase_separation (ν ρ : PMF Depth) (s t : ActivePhase)
    (he : lengthMixture ν s = lengthMixture ρ t) : s = t := by
  have he1 := congrArg (fun m : Measure (Option ℕ) => (m {some 1}).toReal) he
  have hn := phase_intervals ν
  have hr := phase_intervals ρ
  cases s <;> cases t <;> first | rfl | (exfalso; linarith)

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.RealAtoms

set_option autoImplicit false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.CompactPosterior
open MeasureTheory ProbabilityTheory Polynomial
open scoped ENNReal BigOperators BoundedContinuousFunction
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.DepthLaw D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Rates D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Length

abbrev J := Set.Icc (2/9:ℝ) (6/25:ℝ)
instance : PolishSpace J := isClosed_Icc.polishSpace
def xiPoint (k : Depth) : J := ⟨xi k,xi_bounds k⟩
def eta (ν : PMF Depth) (e : ℕ) : Measure J :=
  Measure.sum fun k => (ν k * alphaMass (rate k)^e) • Measure.dirac (xiPoint k)

private theorem alpha_le_one (k : Depth) : alphaMass (rate k) ≤ 1 := by
  unfold alphaMass
  exact_mod_cast (show (unitInterval.toNNReal (rate k)) ≤ 1 from by
    exact_mod_cast (rate k).property.2)

private theorem eta_mass (ν : PMF Depth) (e : ℕ) : eta ν e Set.univ ≤ 1 := by
  simp only [eta,Measure.sum_apply_of_countable,Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one]
  calc
    (∑' k, ν k*alphaMass (rate k)^e) ≤ ∑' k,ν k := by
      apply ENNReal.tsum_le_tsum
      intro k
      exact mul_le_of_le_one_right' (pow_le_one₀ (show 0 ≤ alphaMass (rate k) from zero_le) (alpha_le_one k))
    _ = 1 := ν.tsum_coe

instance eta_finite (ν : PMF Depth) (e : ℕ) : IsFiniteMeasure (eta ν e) :=
  ⟨lt_of_le_of_lt (eta_mass ν e) ENNReal.one_lt_top⟩

def polynomialBounded : ℝ[X] →ₐ[ℝ] (J →ᵇ ℝ) where
  toFun p := BoundedContinuousFunction.mkOfCompact (p.toContinuousMapOn J)
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' := by intros; ext; simp
  map_mul' := by intros; ext; simp
  commutes' := by intro r; ext; simp

def polynomialAlgebra : StarSubalgebra ℝ (J →ᵇ ℝ) :=
  { toSubalgebra := polynomialBounded.range
    star_mem' := by
      intro f hf
      have hs : star f = f := by ext; simp
      rwa [hs] }

private theorem polynomial_separates :
    (polynomialAlgebra.map (BoundedContinuousFunction.toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  intro x y hxy
  refine ⟨(polynomialBounded Polynomial.X).toContinuousMap,?_,?_⟩
  · refine ⟨_, ?_, rfl⟩
    exact StarSubalgebra.mem_map.mpr ⟨polynomialBounded Polynomial.X,⟨Polynomial.X,rfl⟩,rfl⟩
  · simpa [polynomialBounded] using (fun he : x.val = y.val => hxy (Subtype.ext he))

private theorem eta_moment (ν : PMF Depth) (e n : ℕ) :
    (∫ x : J, (x:ℝ)^n ∂eta ν e) =
      ∑' k,(ν k).toReal*(rate k:ℝ)^e*xi k^n := by
  rw [eta,integral_sum_dirac]
  · simp [alphaMass,ENNReal.toReal_mul,ENNReal.toReal_pow,smul_eq_mul,mul_assoc,xiPoint]
  · intro k
    exact ENNReal.mul_ne_top (ν.apply_ne_top k) (ENNReal.pow_ne_top (by simp [alphaMass]))

private theorem eta_singleton (ν : PMF Depth) (e : ℕ) (k : Depth) :
    eta ν e {xiPoint k} = ν k*alphaMass (rate k)^e := by
  have hi : Function.Injective xiPoint := by
    intro k l he
    exact xi_injective (congrArg Subtype.val he)
  simp [eta,Measure.sum_apply,hi.eq_iff,Pi.single_apply]

private theorem all_moments_posterior (ν ρ : PMF Depth) (e : ℕ)
    (hm : ∀ n : ℕ,
      (∑' k,(ν k).toReal*(rate k:ℝ)^e*xi k^n) =
      ∑' k,(ρ k).toReal*(rate k:ℝ)^e*xi k^n) : ν = ρ := by
  have hint (p : ℝ[X]) (σ : PMF Depth) :
      Integrable (fun x : J => p.eval (x:ℝ)) (eta σ e) := by
    convert (polynomialBounded p).integrable (μ := eta σ e) using 1
    funext x
    rfl
  have hp : ∀ p : ℝ[X],
      (∫ x : J,p.eval (x:ℝ) ∂eta ν e) = ∫ x : J,p.eval (x:ℝ) ∂eta ρ e := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q ihp ihq =>
      simp only [Polynomial.eval_add]
      rw [integral_add (hint p ν) (hint q ν),
        integral_add (hint p ρ) (hint q ρ),ihp,ihq]
    | monomial n a =>
      simp only [Polynomial.eval_monomial]
      rw [integral_const_mul,integral_const_mul,eta_moment,eta_moment,hm]
  have hη : eta ν e = eta ρ e := by
    apply ext_of_forall_mem_subalgebra_integral_eq_of_polish polynomial_separates
    intro g hg
    obtain ⟨p,rfl⟩ := hg
    exact hp p
  ext k
  have he := congrArg (fun m : Measure J => m {xiPoint k}) hη
  rw [eta_singleton,eta_singleton] at he
  have ha : 0 < alphaMass (rate k) := by
    rw [alphaMass,ENNReal.coe_pos,← NNReal.coe_pos]
    exact (ratio_interior k).1
  exact (ENNReal.mul_left_inj
    (ne_of_gt (ENNReal.pow_pos ha e))
    (ENNReal.pow_ne_top (by simp [alphaMass]))).mp he
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.CompactPosterior

set_option autoImplicit false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Residual
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Prefix D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.DepthLaw D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Tail
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Stopping D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.WordLaw D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Length
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Control

def transcript (c : AcquiredNativeState) (ω : Stream) : Transcript :=
  fun n => visible (nativeDrive c ω n)
def canonical (s : ActivePhase) : AcquiredNativeState :=
  ⟨⟨⟨.fourth (.active s),emptyRegisters⟩,0⟩,⟨0,0⟩⟩
def wordStream (w : List Letter) : Stream :=
  fun i => if h : i < w.length then w.get ⟨i,h⟩ else 0
def reconstructTranscript (s : ActivePhase) (t : RawTail) : Transcript :=
  transcript (canonical s) (match t with | none => infiniteTail s | some w => wordStream w)
def transcriptLaw (μ : PMF Depth) (h : List Operation) (c : AcquiredNativeState) :
    Measure Transcript :=
  (ProbabilityTheory.cond (jointLaw μ) (nativeEvent h c)).map
    (fun z => transcript c (rawTail z.2 (readLetters h).length))

theorem drive_prefix_input (c : AcquiredNativeState) (ω ω' : Stream) (n : ℕ)
    (hp : ∀ i : ℕ,i < n → ω i = ω' i) : nativeDrive c ω n = nativeDrive c ω' n := by
  induction n generalizing c ω ω' with
  | zero => rfl
  | succ n ih =>
    have h0 := hp 0 (by omega)
    have hn : nextNative c ω = nextNative c ω' := by
      unfold nextNative nextOperation
      rw [h0]
    rw [nativeDrive,nativeDrive,hn]
    cases hs : nextNative c ω' with
    | none => rfl
    | some z =>
      simp only [Option.bind_some]
      congr 1
      apply ih
      intro i hi
      change ω (i+readCost z.1) = ω' (i+readCost z.1)
      apply hp
      have hc : readCost z.1 ≤ 1 := by cases z.1 <;> simp [readCost]
      omega

theorem word_stream_prefix (w : List Letter) : Prefix (wordStream w) w := by
  unfold Prefix readPrefix
  simpa [wordStream] using List.ofFn_get w

theorem prefix_agrees (ω ω' : Stream) (w : List Letter)
    (hp : Prefix ω w) (hq : Prefix ω' w) (i : ℕ) (hi : i < w.length) : ω i = ω' i := by
  have he : readPrefix ω w.length = readPrefix ω' w.length := hp.trans hq.symm
  have hx := congrArg (fun v : List Letter => v[i]?) he
  simpa [readPrefix,List.getElem?_eq_getElem,hi] using hx

theorem stopped_transcript (c : AcquiredNativeState) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s)) (ω : Stream)
    (w : List Letter) (hw : stoppedReadWord s ω = some w) :
    transcript c ω = reconstructTranscript s (some w) := by
  have hp := (stopped_word_fiber s ω w).mp hw
  have hq := word_stream_prefix w
  have hw' : stoppedReadWord s (wordStream w) = some w :=
    (stopped_word_fiber s _ w).mpr ⟨hq,hp.2⟩
  have hlast : nativeDrive c ω (w.length+1) = nativeDrive c (wordStream w) (w.length+1) := by
    have hn := native_renderer_eq c s hs ω
    have hn' := native_renderer_eq c s hs (wordStream w)
    simp only [nativeStopped,hw,hw',Option.bind_some] at hn hn'
    exact hn.trans hn'.symm
  obtain ⟨b,d,hf,hd,hdel⟩ := (native_stopped_iff c s hs ω w).mp hw
  apply funext
  intro n
  change visible (nativeDrive c ω n) = visible (nativeDrive (canonical s) (wordStream w) n)
  rw [← drive_control c (canonical s) (wordStream w) n hs]
  by_cases hn : n ≤ w.length
  · rw [drive_prefix_input c ω (wordStream w) n (fun i hi => prefix_agrees ω _ w hp.1 hq i (by omega))]
  · by_cases he : n = w.length+1
    · rw [he,hlast]
    · have hn : w.length+1 < n := by omega
      have hh : n = w.length+1+(n-(w.length+1)) := by omega
      rw [hh,drive_append c ω (w.length+1),drive_append c (wordStream w) (w.length+1),hd,← hlast,hd]
      have hz (v : Stream) : nativeDrive d v (n-(w.length+1)) = none := by
        have hx : n-(w.length+1) = (n-(w.length+1)-1)+1 := by omega
        rw [hx]
        exact delivered_positive_none d hdel v _
      simp [hz]

theorem residual_renderer_all_paths (c : AcquiredNativeState) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s)) (ω : Stream) :
    transcript c ω = reconstructTranscript s (stoppedReadWord s ω) := by
  cases hw : stoppedReadWord s ω with
  | none =>
    have he := (noncompletion_fiber s ω).mp hw
    subst ω
    apply funext
    intro n
    exact drive_control c (canonical s) (infiniteTail s) n hs
  | some w => exact stopped_transcript c s hs ω w hw

private theorem transcript_measurable (c : AcquiredNativeState) : Measurable (transcript c) := by
  apply measurable_pi_lambda
  intro n
  exact (measurable_of_countable visible).comp (drive_measurable c n)

theorem residual_law_transport (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s)) :
    transcriptLaw μ h c = (wordMixture (posterior μ h c hc) s).map (reconstructTranscript s) := by
  have hr : Measurable (reconstructTranscript s) := measurable_of_countable _
  have hw : Measurable (fun z : Depth × Stream =>
      stoppedReadWord s (rawTail z.2 (readLetters h).length)) :=
    (measurable_stopped_read_word s).comp (by unfold rawTail; fun_prop)
  rw [← posterior_word_law μ h c hc s]
  unfold wordLaw transcriptLaw
  rw [Measure.map_map hr hw]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall (fun z => residual_renderer_all_paths c s hs _)

def deliveredAt (t : Transcript) (n : ℕ) : Prop :=
  ∃ ops : List Operation,t n = some (ops,.fourth .delivered)
def complete (t : Transcript) : Prop := ∃ n : ℕ,deliveredAt t n
def transcriptCount (t : Transcript) : Option ℕ := by
  classical
  exact if h : complete t then (t (Nat.find h)).map (fun r => (readLetters r.1).length) else none

private theorem delivered_at_measurable (n : ℕ) : MeasurableSet {t : Transcript | deliveredAt t n} :=
  (show MeasurableSet {v : Visible | ∃ ops : List Operation,v = some (ops,.fourth .delivered)} from trivial).preimage (measurable_pi_apply n)

private theorem transcript_count_measurable : Measurable transcriptCount := by
  classical
  let H : Set Transcript := {t | complete t}
  have hH : MeasurableSet H := by
    change MeasurableSet {t : Transcript | ∃ n : ℕ,deliveredAt t n}
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion delivered_at_measurable
  let f : H → Option ℕ := fun t =>
    (t.val (Nat.find t.property)).map (fun r => (readLetters r.1).length)
  have hf : Measurable f := by
    apply Measurable.find
      (fun n => (measurable_of_countable (fun v : Visible =>
        v.map (fun r => (readLetters r.1).length))).comp
        ((measurable_pi_apply n).comp measurable_subtype_coe))
      (fun n => (delivered_at_measurable n).preimage measurable_subtype_coe)
      (fun t : H => t.property)
  exact Measurable.dite hf measurable_const hH

theorem terminal_index (c : AcquiredNativeState) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s)) (ω : Stream)
    (w : List Letter) (hw : stoppedReadWord s ω = some w) (n : ℕ) :
    deliveredAt (transcript c ω) n ↔ n = w.length+1 := by
  obtain ⟨hp,b,hf⟩ := (stopped_word_fiber s ω w).mp hw
  obtain ⟨_,e,hread,hpending,_,hstop⟩ := native_first_pending c s hs ω w hp b hf
  constructor
  · rintro ⟨ops,hvis⟩
    obtain ⟨⟨ops',d',paid⟩,hdr,hproj⟩ := Option.map_eq_some_iff.mp hvis
    have hdel : d'.source.finiteFields.control = .fourth .delivered :=
      (Prod.mk.inj hproj).2
    by_cases hn : n < w.length
    · exact False.elim ((D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Boundary.native_no_earlier_terminal
        c e ω w hread n hn ops' d' paid hdr).2 hdel)
    · by_cases he : n = w.length
      · subst n
        have hh := Option.some.inj (hread.symm.trans hdr)
        have hd' : e = d' := (Prod.mk.inj (Prod.mk.inj hh).2).1
        rw [hd',hdel] at hpending
        simp at hpending
      · by_cases hh : n = w.length+1
        · exact hh
        · have hn : w.length+1 < n := by omega
          have ho := completion_overrun c (delivered e) ω _ _ _ hstop rfl (n-(w.length+1)-1)
          have hidx : w.length+1+(n-(w.length+1)-1+1) = n := by omega
          rw [hidx,hdr] at ho
          contradiction
  · intro hn
    subst n
    exact ⟨reads w ++ [.stop b],by simp [transcript,visible,hstop,delivered]⟩

private theorem actual_transcript_count (c : AcquiredNativeState) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s)) (ω : Stream)
    (w : List Letter) (hw : stoppedReadWord s ω = some w) :
    transcriptCount (transcript c ω) = some w.length := by
  classical
  have h : complete (transcript c ω) :=
    ⟨w.length+1,(terminal_index c s hs ω w hw _).mpr rfl⟩
  have hn : Nat.find h = w.length+1 :=
    (terminal_index c s hs ω w hw _).mp (Nat.find_spec h)
  obtain ⟨b,d,hf,hd,_⟩ := (native_stopped_iff c s hs ω w).mp hw
  simp [transcriptCount,h,hn,transcript,visible,hd,erase_reads,readLetters]

private theorem native_transcript_projection_all_paths (c : AcquiredNativeState) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s)) (ω : Stream) :
    transcriptCount (transcript c ω) = lengthProjection (stoppedReadWord s ω) := by
  classical
  cases hw : stoppedReadWord s ω with
  | some w => simpa [lengthProjection,hw] using actual_transcript_count c s hs ω w hw
  | none =>
    have hω := (noncompletion_fiber s ω).mp hw
    have hc : ¬complete (transcript c ω) := by
      rintro ⟨n,ops,hv⟩
      obtain ⟨⟨ops',d,paid⟩,hd,hp⟩ := Option.map_eq_some_iff.mp hv
      have ht := (D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Infinite.infinite_tail_native_noncompletion c s hs).2 n
      apply ht
      refine ⟨ops',d,paid,?_,(Prod.mk.inj hp).2⟩
      simpa [hω] using hd
    simp [lengthProjection,hw,transcriptCount,hc]

private theorem transcript_read_projection (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s)) :
    (transcriptLaw μ h c).map transcriptCount = lengthLaw μ h c s := by
  unfold transcriptLaw lengthLaw
  have hm : Measurable (fun z : Depth × Stream => transcript c (rawTail z.2 (readLetters h).length)) :=
    (transcript_measurable c).comp (by unfold rawTail; fun_prop)
  rw [Measure.map_map transcript_count_measurable hm]
  apply Measure.map_congr
  exact Filter.Eventually.of_forall (fun z => native_transcript_projection_all_paths c s hs _)

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Residual

set_option autoImplicit false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.DepthLaw D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.WordLaw D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Length
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Rates D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.RealAtoms D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.CompactPosterior
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery.Residual
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Control

private theorem length_determines_phase_posterior (ν ρ : PMF Depth) (s t : ActivePhase)
    (he : lengthMixture ν s = lengthMixture ρ t) : s = t ∧ ν = ρ := by
  have hs := phase_separation ν ρ s t he
  refine ⟨hs,?_⟩
  subst t
  cases s with
  | p =>
    apply all_moments_posterior ν ρ 1
    intro n
    have h := congrArg (fun m : Measure (Option ℕ) => (m {some (2*n+1)}).toReal) he
    rw [(real_five_atoms ν n).1,(real_five_atoms ρ n).1] at h
    simpa only [pow_one] using h
  | beta =>
    apply all_moments_posterior ν ρ 2
    intro n
    have h := congrArg (fun m : Measure (Option ℕ) => (m {some (2*n+2)}).toReal) he
    rw [(real_five_atoms ν n).2.2.2.1,(real_five_atoms ρ n).2.2.2.1] at h
    exact h

private theorem original_length_equivalence (μ ρ : PMF Depth)
    (h g : List Operation) (c d : AcquiredNativeState)
    (hc : run h = some c) (hd : run g = some d) (s t : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s))
    (ht : d.source.finiteFields.control = .fourth (.active t)) :
    lengthLaw μ h c s = lengthLaw ρ g d t ↔
      s = t ∧ posterior μ h c hc = posterior ρ g d hd := by
  rw [posterior_length_law μ h c hc,posterior_length_law ρ g d hd]
  constructor
  · exact length_determines_phase_posterior _ _ s t
  · rintro ⟨rfl,hν⟩; rw [hν]

theorem posterior_phase_determine_both (μ ρ : PMF Depth)
    (h g : List Operation) (c d : AcquiredNativeState)
    (hc : run h = some c) (hd : run g = some d) (s t : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s))
    (ht : d.source.finiteFields.control = .fourth (.active t))
    (hp : s = t ∧ posterior μ h c hc = posterior ρ g d hd) :
    lengthLaw μ h c s = lengthLaw ρ g d t ∧ transcriptLaw μ h c = transcriptLaw ρ g d := by
  refine ⟨(original_length_equivalence μ ρ h g c d hc hd s t hs ht).mpr hp,?_⟩
  rw [residual_law_transport μ h c hc s hs,residual_law_transport ρ g d hd t ht]
  rw [hp.1,hp.2]

theorem complete_original_recovery (μ ρ : PMF Depth)
    (h g : List Operation) (c d : AcquiredNativeState)
    (hc : run h = some c) (hd : run g = some d) (s t : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s))
    (ht : d.source.finiteFields.control = .fourth (.active t)) :
    (lengthLaw μ h c s = lengthLaw ρ g d t ↔
      s = t ∧ posterior μ h c hc = posterior ρ g d hd) ∧
    (lengthLaw μ h c s = lengthLaw ρ g d t ↔ transcriptLaw μ h c = transcriptLaw ρ g d) ∧
    (transcriptLaw μ h c = transcriptLaw ρ g d ↔
      s = t ∧ posterior μ h c hc = posterior ρ g d hd) := by
  have hD := original_length_equivalence μ ρ h g c d hc hd s t hs ht
  have hDL : lengthLaw μ h c s = lengthLaw ρ g d t ↔ transcriptLaw μ h c = transcriptLaw ρ g d := by
    constructor
    · intro he
      exact (posterior_phase_determine_both μ ρ h g c d hc hd s t hs ht (hD.mp he)).2
    · intro he
      have hm := congrArg (fun m : Measure Transcript => m.map transcriptCount) he
      rwa [transcript_read_projection μ h c hc s hs,transcript_read_projection ρ g d hd t ht] at hm
  exact ⟨hD,hDL,hDL.symm.trans hD⟩

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentLawRecovery
