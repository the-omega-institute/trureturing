/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeConditionalControl
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeConditionalControl
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native control determines every finite visible trace under same-depth conditional continuation. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeAcquiredPrefixCylinder
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Probability.Independence.Process.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Prefix
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder

def eraseOp : Operation → Option Letter
  | .read x => some x
  | .stop _ => none

theorem erasure_eq (h : List Operation) : readLetters h = h.filterMap eraseOp := by
  induction h with
  | nil => rfl
  | cons op h ih => cases op <;> simp [readLetters, List.filterMap, eraseOp, ih]

theorem erase_reads (w : List Letter) (v : List Operation) :
    readLetters (reads w ++ v) = w ++ readLetters v := by
  simp [erasure_eq, reads, List.filterMap_append, List.filterMap_map, Function.comp_def, eraseOp]

@[simp] private theorem erase_reads_only (w : List Letter) : readLetters (reads w) = w := by
  simpa only [List.append_nil, readLetters] using erase_reads w []

private theorem word_counts (r : unitInterval) (w : List Letter) :
    wordMass r w = alphaMass r ^ w.count 0 * betaMass r ^ w.count 1 := by
  have hm (x : Letter) : (bernoulliMeasure (0 : Letter) 1 r) {x} =
      (if x = 0 then alphaMass r else 1) * (if x = 1 then betaMass r else 1) := by
    fin_cases x <;> simp [alphaMass, betaMass]
  unfold wordMass
  simp_rw [hm]
  rw [List.prod_map_mul,
    List.prod_map_eq_pow_single 0 _ (by intro x hx _; simp [hx]),
    List.prod_map_eq_pow_single 1 _ (by intro x hx _; simp [hx])]
  simp

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Prefix

set_option autoImplicit false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.DepthLaw
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Prefix

abbrev Depth := ℕ+
instance : MeasurableSpace Depth := ⊤

theorem ratio_interior (k : Depth) :
    0 < (Nat.fib (k.val+1) : ℝ) / Nat.fib (k.val+3) ∧
    (Nat.fib (k.val+1) : ℝ) / Nat.fib (k.val+3) < 1 := by
  have hp : 0 < (Nat.fib (k.val+1) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < k.val+1)
  have hd : 0 < (Nat.fib (k.val+3) : ℝ) := by
    exact_mod_cast Nat.fib_pos.mpr (by omega : 0 < k.val+3)
  have hl : (Nat.fib (k.val+1) : ℝ) < Nat.fib (k.val+3) := by
    have h1 : 2 ≤ k.val + 1 := Nat.succ_le_succ k.property
    have h2 : 2 ≤ k.val + 3 := by omega
    exact_mod_cast Nat.fib_strictMonoOn (a := k.val+1) (b := k.val+3)
      h1 h2 (by omega : k.val+1 < k.val+3)
  exact ⟨div_pos hp hd, (div_lt_one hd).mpr hl⟩

def rate (k : Depth) : unitInterval :=
  ⟨(Nat.fib (k.val+1) : ℝ) / Nat.fib (k.val+3),
    (ratio_interior k).1.le, (ratio_interior k).2.le⟩

def jointLaw (μ : PMF Depth) : Measure (Depth × Stream) :=
  Measure.sum fun k => μ k • (rawReadLaw (rate k)).map (fun ω => (k,ω))

instance joint_probability (μ : PMF Depth) : IsProbabilityMeasure (jointLaw μ) := by
  constructor
  have ht (k : Depth) : ((rawReadLaw (rate k)).map (fun ω => (k,ω))) Set.univ = 1 := by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  simp [jointLaw, ht, μ.tsum_coe]

def nativeEvent (h : List Operation) (c : AcquiredNativeState) : Set (Depth × Stream) :=
  {z | nativeDrive initial z.2 h.length = some (h,c,(readLetters h).length)}

private theorem event_eq (h : List Operation) (c : AcquiredNativeState) (hc : run h = some c) :
    nativeEvent h c = Prod.snd ⁻¹' prefixCylinder (readLetters h) := by
  ext z
  exact (native_acquired_prefix_cylinder h c z.2 _).trans (by simp [hc, prefixCylinder])

private theorem event_measurable (h : List Operation) (c : AcquiredNativeState) :
    MeasurableSet (nativeEvent h c) := by
  by_cases hc : run h = some c
  · rw [event_eq h c hc]
    exact (measurable_cylinder _).preimage measurable_snd
  · have he : nativeEvent h c = ∅ := by
      ext z
      simp [nativeEvent, native_acquired_prefix_cylinder, hc]
    rw [he]; exact MeasurableSet.empty

def likelihood (h : List Operation) (k : Depth) : ℝ≥0∞ := wordMass (rate k) (readLetters h)
def normalizer (μ : PMF Depth) (h : List Operation) : ℝ≥0∞ := ∑' k, μ k * likelihood h k

private theorem history_mass (μ : PMF Depth) (h : List Operation) (c : AcquiredNativeState)
    (hc : run h = some c) : jointLaw μ (nativeEvent h c) = normalizer μ h := by
  rw [event_eq h c hc]
  simp only [jointLaw, Measure.sum_apply_of_countable, Measure.smul_apply, smul_eq_mul]
  apply tsum_congr
  intro k
  rw [Measure.map_apply (by fun_prop) ((measurable_cylinder _).preimage measurable_snd)]
  exact congrArg (μ k * ·) (cylinder_mass (rate k) (readLetters h))

private theorem likelihood_pos (h : List Operation) (k : Depth) : 0 < likelihood h k := by
  rw [likelihood, word_counts]
  rw [ENNReal.mul_pos_iff]
  constructor <;> apply ENNReal.pow_pos
  · rw [alphaMass, ENNReal.coe_pos, ← NNReal.coe_pos]
    exact (ratio_interior k).1
  · rw [betaMass, ENNReal.coe_pos, ← NNReal.coe_pos]
    change 0 < 1 - (rate k : ℝ)
    exact sub_pos.mpr (ratio_interior k).2

private theorem normalizer_bounds (μ : PMF Depth) (h : List Operation) (c : AcquiredNativeState)
    (hc : run h = some c) : 0 < normalizer μ h ∧ normalizer μ h ≤ 1 := by
  constructor
  · obtain ⟨k,hk⟩ := μ.support_nonempty
    apply lt_of_lt_of_le (ENNReal.mul_pos hk (ne_of_gt (likelihood_pos h k)))
    exact ENNReal.le_tsum (f := fun k => μ k * likelihood h k) k
  · rw [← history_mass μ h c hc]
    calc
      jointLaw μ (nativeEvent h c) ≤ jointLaw μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ

def posterior (μ : PMF Depth) (h : List Operation) (c : AcquiredNativeState)
    (hc : run h = some c) : PMF Depth :=
  PMF.normalize (fun k => μ k * likelihood h k)
    (ne_of_gt (normalizer_bounds μ h c hc).1)
    (ne_top_of_le_ne_top ENNReal.one_ne_top (normalizer_bounds μ h c hc).2)

set_option maxHeartbeats 2000000 in
private theorem raw_product (r : unitInterval) :
    rawReadLaw r = Measure.infinitePi (fun _ : ℕ => bernoulliMeasure (0 : Letter) 1 r) := by
  unfold rawReadLaw Kernel.trajMeasure
  have hi : (bernoulliMeasure (0 : Letter) 1 r).map
      (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => Letter)).symm =
      Measure.pi (fun _ : ↥(Finset.Iic 0) => bernoulliMeasure (0 : Letter) 1 r) := by
    exact ((MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => Letter)).map_apply_eq_iff_map_symm_apply_eq.mp
      (measurePreserving_piUnique (fun _ : ↥(Finset.Iic 0) => bernoulliMeasure (0 : Letter) 1 r)).map_eq).symm
  rw [hi]
  change Measure.infinitePiNat (fun _ : ℕ => bernoulliMeasure (0 : Letter) 1 r) = _
  exact (Measure.isProjectiveLimit_infinitePiNat _).unique (Measure.isProjectiveLimit_infinitePi _)

private theorem untouched_tail (r : unitInterval) (n : ℕ) :
    (rawReadLaw r).map (fun ω => rawTail ω n) = rawReadLaw r := by
  rw [raw_product]
  exact Measure.map_infinitePi_infinitePi_of_inj (fun i j h => Nat.add_right_cancel h)

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.DepthLaw

set_option autoImplicit false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Tail
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.DepthLaw

private theorem prefix_tail_factorization (r : unitInterval) (w : List Letter) (s : Set Stream)
    (hs : MeasurableSet s) :
    rawReadLaw r (prefixCylinder w ∩ (fun ω => rawTail ω w.length) ⁻¹' s) =
      wordMass r w * rawReadLaw r s := by
  let m : ℕ → MeasurableSpace Stream := fun i =>
    MeasurableSpace.comap (fun ω : Stream => ω i) inferInstance
  let below : MeasurableSpace Stream := ⨆ i ∈ {i : ℕ | i < w.length}, m i
  let above : MeasurableSpace Stream := ⨆ i ∈ {i : ℕ | w.length ≤ i}, m i
  have hind : iIndep m (rawReadLaw r) := by
    rw [raw_product]
    exact iIndepFun_infinitePi
      (P := fun _ : ℕ => bernoulliMeasure (0 : Letter) 1 r)
      (X := fun (_ : ℕ) (x : Letter) => x) (by fun_prop)
  have hdis : Disjoint {i : ℕ | i < w.length} {i : ℕ | w.length ≤ i} := by
    rw [Set.disjoint_left]
    intro i hi hj
    exact Nat.not_lt_of_ge hj hi
  have hi : Indep below above (rawReadLaw r) :=
    indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) hind hdis
  have hp : @Measurable Stream (List Letter) below inferInstance
      (fun ω => readPrefix ω w.length) := by
    apply (measurable_of_countable (fun v : Fin w.length → Letter => List.ofFn v)).comp
    apply (@measurable_pi_lambda Stream (Fin w.length) (fun _ => Letter) below
      (fun _ => inferInstance))
    intro i
    apply measurable_iff_comap_le.mpr
    change m i.val ≤ below
    exact le_iSup_of_le i.val (le_iSup_of_le i.isLt le_rfl)
  have ht : @Measurable Stream Stream above MeasurableSpace.pi
      (fun ω => rawTail ω w.length) := by
    apply (@measurable_pi_lambda Stream ℕ (fun _ => Letter) above
      (fun _ => inferInstance))
    intro i
    apply measurable_iff_comap_le.mpr
    change m (i + w.length) ≤ above
    exact le_iSup_of_le (i + w.length)
      (le_iSup_of_le (show w.length ≤ i + w.length from Nat.le_add_left _ _) le_rfl)
  have hf := (hi.indepSet_of_measurableSet (hp (measurableSet_singleton w)) (ht hs)).measure_inter_eq_mul
  change rawReadLaw r (prefixCylinder w ∩ (fun ω => rawTail ω w.length) ⁻¹' s) =
    rawReadLaw r (prefixCylinder w) * rawReadLaw r ((fun ω => rawTail ω w.length) ⁻¹' s) at hf
  rw [cylinder_mass] at hf
  have htail : rawReadLaw r ((fun ω => rawTail ω w.length) ⁻¹' s) = rawReadLaw r s := by
    rw [← Measure.map_apply (by unfold rawTail; fun_prop) hs, untouched_tail]
  exact hf.trans (congrArg (wordMass r w * ·) htail)

instance : Countable AcquiredNativeState :=
  Function.Injective.countable
    (f := fun c : AcquiredNativeState => (c.source.finiteFields, c.source.payloadReturns,
      c.counts.alpha, c.counts.beta)) (by
        rintro ⟨⟨f, j⟩, ⟨a, b⟩⟩ ⟨⟨g, k⟩, ⟨x, y⟩⟩ he
        simpa only [Prod.mk.injEq, AcquiredNativeState.mk.injEq,
          NativeSourceState.mk.injEq, Counts.mk.injEq, and_assoc] using he)

instance : MeasurableSpace (Option (List Operation × AcquiredNativeState × ℕ)) := ⊤
instance : MeasurableSingletonClass (Option (List Operation × AcquiredNativeState × ℕ)) :=
  ⟨fun _ => trivial⟩

theorem drive_measurable (c : AcquiredNativeState) (n : ℕ) :
    Measurable (fun ω : Stream => nativeDrive c ω n) := by
  classical
  apply measurable_to_countable'
  intro result
  change MeasurableSet {ω : Stream | nativeDrive c ω n = result}
  cases result with
  | none =>
    have he : {ω : Stream | nativeDrive c ω n = none} =
        (⋃ result : List Operation × AcquiredNativeState × ℕ,
          {ω : Stream | nativeDrive c ω n = some result})ᶜ := by
      ext ω
      cases hd : nativeDrive c ω n with
      | none => simp [hd]
      | some result => rcases result with ⟨h, d, k⟩; simp [hd]
    rw [he]
    apply MeasurableSet.compl
    apply MeasurableSet.iUnion
    rintro ⟨h, d, k⟩
    simp_rw [drive_spec]
    by_cases hv : h.length = n ∧ execute c h = some d ∧ k = (readLetters h).length
    · have he : {ω : Stream | h.length = n ∧ execute c h = some d ∧
          Prefix ω (readLetters h) ∧ k = (readLetters h).length} = prefixCylinder (readLetters h) := by
        ext ω; simp [hv.1, hv.2.1, hv.2.2, prefixCylinder]
      rw [he]
      exact measurable_cylinder _
    · have he : {ω : Stream | h.length = n ∧ execute c h = some d ∧
          Prefix ω (readLetters h) ∧ k = (readLetters h).length} = ∅ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hh => hv ⟨hh.1, hh.2.1, hh.2.2.2⟩
      rw [he]
      exact MeasurableSet.empty
  | some result =>
    rcases result with ⟨h, d, k⟩
    simp_rw [drive_spec]
    by_cases hv : h.length = n ∧ execute c h = some d ∧ k = (readLetters h).length
    · have he : {ω : Stream | h.length = n ∧ execute c h = some d ∧
          Prefix ω (readLetters h) ∧ k = (readLetters h).length} = prefixCylinder (readLetters h) := by
        ext ω; simp [hv.1, hv.2.1, hv.2.2, prefixCylinder]
      rw [he]
      exact measurable_cylinder _
    · have he : {ω : Stream | h.length = n ∧ execute c h = some d ∧
          Prefix ω (readLetters h) ∧ k = (readLetters h).length} = ∅ := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hh => hv ⟨hh.1, hh.2.1, hh.2.2.2⟩
      rw [he]
      exact MeasurableSet.empty

theorem sameK_conditional_tail (μ : PMF Depth) (h : List Operation)
    (c : AcquiredNativeState) (hc : run h = some c) :
    (ProbabilityTheory.cond (jointLaw μ) (nativeEvent h c)).map
      (fun z : Depth × Stream => (z.1, rawTail z.2 (readLetters h).length)) =
      jointLaw (posterior μ h c hc) := by
  classical
  have hm : Measurable (fun z : Depth × Stream =>
      (z.1, rawTail z.2 (readLetters h).length)) := by
    unfold rawTail
    fun_prop
  ext s hs
  rw [Measure.map_apply hm hs, ProbabilityTheory.cond, Measure.smul_apply,
    Measure.restrict_apply (hs.preimage hm), history_mass μ h c hc]
  simp only [jointLaw, Measure.sum_apply_of_countable, Measure.smul_apply, smul_eq_mul]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro k
  have htag : Measurable (fun ω : Stream => (k, ω)) := by fun_prop
  rw [Measure.map_apply htag ((hs.preimage hm).inter (event_measurable h c)),
    Measure.map_apply htag hs]
  have he : (fun ω : Stream => (k, ω)) ⁻¹'
      ((fun z : Depth × Stream => (z.1, rawTail z.2 (readLetters h).length)) ⁻¹' s ∩
        nativeEvent h c) =
      prefixCylinder (readLetters h) ∩
        (fun ω => rawTail ω (readLetters h).length) ⁻¹'
          ((fun ω : Stream => (k, ω)) ⁻¹' s) := by
    rw [event_eq h c hc]
    ext ω
    exact and_comm
  rw [he, prefix_tail_factorization _ _ _ (hs.preimage htag)]
  simp [posterior, PMF.normalize_apply, likelihood, normalizer, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Tail

set_option autoImplicit false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Stopping
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Prefix D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.DepthLaw D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Tail
open D5.S3.Arith.FibonacciAtomic.TriangularSharedImplementation (trace FirstStop)

def pPending (r : Registers) (S : ℕ) (C : Counts) (j : ℕ) (b : Letter) :
    AcquiredNativeState :=
  ⟨⟨⟨.fourth (.pending b), writeMarker r 3 b⟩, S+j⟩,
    ⟨C.alpha+j+(1-b.val), C.beta+j+2*b.val⟩⟩
def delivered (e : AcquiredNativeState) : AcquiredNativeState :=
  {e with source := {e.source with finiteFields :=
    {e.source.finiteFields with control := .fourth .delivered}}}

private theorem p_pending_execute (r : Registers) (S : ℕ) (C : Counts) (j : ℕ) (b : Letter) :
    execute (atPhase 3 r S C .p) (reads (pWord j b)) = some (pPending r S C j b) := by
  simpa [freshPayload, reconstructPayload, renderPayload, atPhase, payloadControl,
    pPending] using execute_payload
      (.segment (last := (0 : Letter)) j b (.pending : PayloadForm 0 b)) 3 r S C (by omega)

private theorem p_delivered_execute (r : Registers) (S : ℕ) (C : Counts) (j : ℕ) (b : Letter) :
    execute (atPhase 3 r S C .p) (reads (pWord j b) ++ [.stop b]) =
      some (delivered (pPending r S C j b)) := by
  simpa [freshPayload, reconstructPayload, renderPayload, atPhase, payloadControl,
    pPending, delivered] using execute_payload
      (.segment (last := (0 : Letter)) j b (.delivered : PayloadForm 0 b)) 3 r S C (by omega)

theorem beta_return (r : Registers) (S : ℕ) (C : Counts) (ops : List Operation) :
    execute (atPhase 3 r S C .beta) (.read 0 :: ops) =
      execute (atPhase 3 r (S+1) ⟨C.alpha+1,C.beta⟩ .p) ops := by
  simp [atPhase, execute, nativeStep, nativeRead, finiteRead, payloadRead,
    payloadControl, isReturn, countRead]

private theorem beta_one_pending (r : Registers) (S : ℕ) (C : Counts) :
    execute (atPhase 3 r S C .beta) (reads [1]) =
      some ⟨⟨⟨.fourth (.pending 1),writeMarker r 3 1⟩,S⟩,⟨C.alpha,C.beta+1⟩⟩ := by
  simp [atPhase, execute, reads, nativeStep, nativeRead, finiteRead, payloadRead,
    payloadControl, completionControl, isReturn, countRead]

private theorem beta_one_delivered (r : Registers) (S : ℕ) (C : Counts) :
    execute (atPhase 3 r S C .beta) (reads [1] ++ [.stop 1]) =
      some (delivered ⟨⟨⟨.fourth (.pending 1),writeMarker r 3 1⟩,S⟩,
        ⟨C.alpha,C.beta+1⟩⟩) := by
  simp [atPhase, execute, reads, nativeStep, nativeRead, finiteRead, payloadRead,
    payloadControl, completionControl, isReturn, countRead, nativeStop, finiteStop, delivered]

private theorem family_execute (c : AcquiredNativeState) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s))
    (w : List Letter) (b : Letter) (hf : WordFamily s b w) :
    ∃ e : AcquiredNativeState,
      execute c (reads w) = some e ∧ e.source.finiteFields.control = .fourth (.pending b) ∧
      execute c (reads w ++ [.stop b]) = some (delivered e) := by
  rcases c with ⟨⟨⟨ctrl,r⟩,S⟩,C⟩
  dsimp at hs
  subst ctrl
  cases s with
  | p =>
    obtain ⟨j,rfl⟩ := hf
    exact ⟨pPending r S C j b,p_pending_execute r S C j b,rfl,p_delivered_execute r S C j b⟩
  | beta =>
    rcases hf with ⟨rfl,rfl⟩ | ⟨j,rfl⟩
    · exact ⟨_,beta_one_pending r S C,rfl,beta_one_delivered r S C⟩
    · refine ⟨pPending r (S+1) ⟨C.alpha+1,C.beta⟩ j b,?_,rfl,?_⟩
      · simpa only [reads, List.map_cons, atPhase, payloadControl, show ¬(3:ℕ)<3 from by omega, dite_false] using
          (beta_return r S C (reads (pWord j b))).trans
            (p_pending_execute r (S+1) ⟨C.alpha+1,C.beta⟩ j b)
      · simpa only [reads, List.map_cons, List.cons_append, atPhase, payloadControl, show ¬(3:ℕ)<3 from by omega, dite_false] using
          (beta_return r S C (reads (pWord j b) ++ [.stop b])).trans
            (p_delivered_execute r (S+1) ⟨C.alpha+1,C.beta⟩ j b)

theorem native_stopped_iff (c : AcquiredNativeState) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s))
    (ω : Stream) (w : List Letter) :
    stoppedReadWord s ω = some w ↔
      ∃ (b : Letter) (d : AcquiredNativeState), WordFamily s b w ∧
        nativeDrive c ω (w.length+1) = some (reads w ++ [.stop b],d,w.length) ∧
        d.source.finiteFields.control = .fourth .delivered := by
  rw [stopped_word_fiber]
  constructor
  · rintro ⟨hp,b,hf⟩
    obtain ⟨e,he,hpending,hd⟩ := family_execute c s hs w b hf
    refine ⟨b,delivered e,hf,?_,rfl⟩
    apply (drive_spec _ _ _ _ _ _).mpr
    exact ⟨by simp [reads],hd,by simpa [erase_reads,readLetters] using hp,
      by simp [erase_reads,readLetters]⟩
  · rintro ⟨b,d,hf,hd,_⟩
    have hp := ((drive_spec _ _ _ _ _ _).mp hd).2.2.1
    exact ⟨by simpa [erase_reads,readLetters] using hp,b,hf⟩

theorem native_first_pending (c : AcquiredNativeState) (s : ActivePhase)
    (hs : c.source.finiteFields.control = .fourth (.active s))
    (ω : Stream) (w : List Letter) (hp : Prefix ω w) (b : Letter)
    (hf : WordFamily s b w) :
    FirstStop totalRead pendingColor (.active s) ω b w.length ∧
    ∃ e : AcquiredNativeState,
      nativeDrive c ω w.length = some (reads w,e,w.length) ∧
      e.source.finiteFields.control = .fourth (.pending b) ∧
      nativeStop e b = some (delivered e) ∧
      nativeDrive c ω (w.length+1) = some (reads w ++ [.stop b],delivered e,w.length) := by
  obtain ⟨e,he,hpending,hd⟩ := family_execute c s hs w b hf
  refine ⟨(first_completion_normal_form _ _ _ _).mpr ⟨w,rfl,hp,hf⟩,e,?_,hpending,?_,?_⟩
  · exact (drive_spec _ _ _ _ _ _).mpr
      ⟨by simp [reads],he,by simpa using hp,by simp⟩
  · simp [nativeStop,finiteStop,hpending,delivered]
  · exact (drive_spec _ _ _ _ _ _).mpr
      ⟨by simp [reads],hd,by simpa [erase_reads,readLetters] using hp,
        by simp [erase_reads,readLetters]⟩

theorem delivered_positive_none (c : AcquiredNativeState)
    (hc : c.source.finiteFields.control = .fourth .delivered) (ω : Stream) (n : ℕ) :
    nativeDrive c ω (n+1) = none := by
  simp [nativeDrive,nextNative,nextOperation,hc]

theorem completion_overrun (c d : AcquiredNativeState) (ω : Stream)
    (ops : List Operation) (N paid : ℕ)
    (hd : nativeDrive c ω N = some (ops,d,paid))
    (hc : d.source.finiteFields.control = .fourth .delivered) (extra : ℕ) :
    nativeDrive c ω (N+(extra+1)) = none := by
  rw [drive_append,hd]
  simp [delivered_positive_none d hc]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Stopping

set_option autoImplicit false
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Control
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
abbrev Visible := Option (List Operation × NativeControl)
instance : MeasurableSpace Visible := ⊤
instance : MeasurableSingletonClass Visible := ⟨fun _ => trivial⟩
abbrev Transcript := ℕ → Visible

abbrev NativeOutput := Option (List Operation × AcquiredNativeState × ℕ)

def visible (t : NativeOutput) : Visible := t.map fun r => (r.1,r.2.1.source.finiteFields.control)
private theorem next_control (c d : AcquiredNativeState) (ω : Stream)
    (he : c.source.finiteFields.control = d.source.finiteFields.control) :
    (nextNative c ω).map (fun z => (z.1,z.2.source.finiteFields.control)) =
    (nextNative d ω).map (fun z => (z.1,z.2.source.finiteFields.control)) := by
  rcases c with ⟨⟨⟨ctrl,r⟩,j⟩,C⟩
  rcases d with ⟨⟨⟨ctrl',r'⟩,j'⟩,C'⟩
  dsimp only at he
  subst ctrl'
  cases ctrl with
  | seed first =>
    cases first <;> simp [nextNative,nextOperation,nativeStep,nativeRead,finiteRead]
    split_ifs <;> rfl
  | early t s =>
    cases s <;> simp [nextNative,nextOperation,nativeStep,nativeRead,finiteRead,payloadRead]
    all_goals split_ifs <;> rfl
  | fourth q =>
    cases q with
    | active s =>
      cases s <;> simp [nextNative,nextOperation,nativeStep,nativeRead,finiteRead,payloadRead]
      all_goals split_ifs <;> rfl
    | pending b => simp [nextNative,nextOperation,nativeStep,nativeStop,finiteStop]
    | delivered => rfl

theorem drive_control (c d : AcquiredNativeState) (ω : Stream) (n : ℕ)
    (he : c.source.finiteFields.control = d.source.finiteFields.control) :
    visible (nativeDrive c ω n) = visible (nativeDrive d ω n) := by
  induction n generalizing c d ω with
  | zero => simp [visible,nativeDrive,he]
  | succ n ih =>
    have hn := next_control c d ω he
    cases hc : nextNative c ω with
    | none =>
      cases hd : nextNative d ω with
      | none => simp [nativeDrive,hc,hd]
      | some z => simp [hc,hd] at hn
    | some z =>
      cases hd : nextNative d ω with
      | none => simp [hc,hd] at hn
      | some z' =>
        have hz : z.1 = z'.1 ∧ z.2.source.finiteFields.control = z'.2.source.finiteFields.control := by
          simpa [hc,hd] using hn
        have hop : z.1 = z'.1 := hz.1
        have hctrl : z.2.source.finiteFields.control = z'.2.source.finiteFields.control := hz.2
        have hi := ih z.2 z'.2 (rawTail ω (readCost z.1)) hctrl
        simpa [visible,nativeDrive,hc,hd,← hop,Option.map_map,Function.comp_def] using
          congrArg (Option.map (fun r : List Operation × NativeControl => (z.1 :: r.1,r.2))) hi

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativeConditionalControl.Control
