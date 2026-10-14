/- GID: D5/S3/Arith/FibonacciAtomic/Observer/BoundedPreorderTrial
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Bounded preorder trials and licensed stationary original-read acquisition. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeFullSourceProducer
import D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
import D5.S3.Arith.FibonacciAtomic.SourceCoordinates.NativeRotationDepthGap

/-! The trial bounds are symbolic over arbitrary source sizes and epochs.
They do not enumerate a bounded family or certify a fixed finite instance.
The source-indexed traversal is proof data; decoder execution is on the
stationary current source. Reduced trial control requires a separate realization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.BoundedPreorderTrial

open GenealogicalFiberTransport (Source substitution composition)
open ActualTreeReadoutAcquisition (Address Reply readout acquisitionTrace)
open DelayedOriginalReadout

abbrev Report := Sigma (fun _ : Address => Reply)
abbrev History := List Report

/-- Number of branch replies, without removing repeated reports. -/
def branches (s : History) : Nat := s.countP (fun a => a.2 == .branch)

/-- Number of beta leaf replies. Alpha is the zero bit. -/
def betas (s : History) : Nat := s.countP (fun a => a.2 == .beta)

/-- Number of actual labelled leaf replies. -/
def leafVisits (s : History) : Nat :=
  s.countP (fun a => a.2 == .alpha || a.2 == .beta)

/-- XOR of the labelled leaf replies, represented by its residue modulo two. -/
def parity (s : History) : Nat := betas s % 2

/-- Inclusive position of the h-th branch, or the full length if it is absent. -/
def cutLength (h : Nat) : History → Nat
  | [] => 0
  | a :: s => if a.2 = .branch ∧ h ≤ 1 then 1 else
      1 + cutLength (if a.2 = .branch then h-1 else h) s

/-- The bounded trial retains a prefix of the source producer's actual preorder. -/
def trial (h : Nat) (v : Source) : History :=
  let s := acquisitionTrace [] v
  s.take (cutLength h s)

/-- Completion is detected before the cutoff branch. -/
def Completes (h : Nat) (v : Source) : Prop :=
  branches (acquisitionTrace [] v) < h

/-- Every decoder query is charged, including coincident physical literals. -/
def physicalQueries (N : Nat) (s : History) : List Address :=
  s.flatMap (fun a => originalQueries N a.1)

private theorem branches_cons (a : Report) (s : History) :
    branches (a :: s) = branches s + if a.2 = .branch then 1 else 0 := by
  simp [branches, List.countP_cons, beq_iff_eq]

private theorem branches_append (s t : History) :
    branches (s ++ t) = branches s + branches t := by
  simp [branches]

private theorem trace_counts (v : Source) (p : Address) :
    (acquisitionTrace p v).length + 1 = 2 * v.length ∧
    branches (acquisitionTrace p v) + 1 = v.length ∧
    betas (acquisitionTrace p v) = (composition v).2 ∧
    ∀ a ∈ acquisitionTrace p v, a.2 ≠ .absent := by
  induction v generalizing p with
  | of b => cases b <;> simp [acquisitionTrace, branches, betas, composition,
      FreeMagma.length]
  | mul s t ihs iht =>
    obtain ⟨ls, bs, cs, ns⟩ := ihs (p ++ [false])
    obtain ⟨lt, bt, ct, nt⟩ := iht (p ++ [true])
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [acquisitionTrace, List.length_cons, List.length_append, FreeMagma.length]
      omega
    · simp only [acquisitionTrace, branches_cons, branches_append, ite_true]
      change _ + 1 = s.length + t.length
      omega
    · simp only [betas] at cs ct ⊢
      simp [acquisitionTrace, composition, cs, ct]
    · intro a ha
      simp only [acquisitionTrace, List.mem_cons, List.mem_append] at ha
      rcases ha with rfl | ha | ha
      · exact Reply.noConfusion
      · exact ns a ha
      · exact nt a ha

/-- A proper preorder prefix has more pending slots than zero, and every
ancestor of the next query has already contributed a branch. -/
private theorem prefix_geometry (v : Source) (p : Address) (i : Nat)
    (hi : i < (acquisitionTrace p v).length) :
    i ≤ 2 * branches ((acquisitionTrace p v).take i) ∧
    ((acquisitionTrace p v)[i]).1.length ≤
      p.length + branches ((acquisitionTrace p v).take i) := by
  induction v generalizing p i with
  | of b =>
    have : i = 0 := by simpa [acquisitionTrace] using hi
    subst i
    simp [acquisitionTrace, branches]
  | mul s t ihs iht =>
    cases i with
    | zero => simp [acquisitionTrace, branches]
    | succ i =>
      let l := acquisitionTrace (p ++ [false]) s
      let r := acquisitionTrace (p ++ [true]) t
      have hi' : i < l.length + r.length := by
        simpa [acquisitionTrace, l, r] using hi
      have hi'' : i < (l ++ r).length := by simpa using hi'
      change i+1 ≤ 2 * branches (⟨p, .branch⟩ :: (l ++ r).take i) ∧
        ((l ++ r)[i]).1.length ≤
          p.length + branches (⟨p, .branch⟩ :: (l ++ r).take i)
      rw [branches_cons]
      simp only [ite_true]
      by_cases hl : i < l.length
      · have hs := ihs (p ++ [false]) i hl
        rw [List.take_append_of_le_length (Nat.le_of_lt hl),
          List.getElem_append_left hl]
        simp only [List.length_append, List.length_singleton] at hs
        dsimp only [l] at *
        omega
      · have hle : l.length ≤ i := by omega
        have hr : i-l.length < r.length := by omega
        have ht := iht (p ++ [true]) (i-l.length) hr
        have counts := trace_counts s (p ++ [false])
        rw [List.take_append, List.take_of_length_le hle, branches_append,
          List.getElem_append_right hle]
        simp only [List.length_append, List.length_singleton] at ht
        change l.length + 1 = 2 * s.length ∧ branches l + 1 = s.length ∧ _ at counts
        dsimp only [r] at *
        omega

private theorem cut_properties (s : History) (h : Nat) (hh : 0 < h) :
    cutLength h s ≤ s.length ∧
    (∀ i, i < cutLength h s → branches (s.take i) < h) ∧
    (branches s < h → cutLength h s = s.length) ∧
    (h ≤ branches s →
      0 < cutLength h s ∧ branches (s.take (cutLength h s)) = h ∧
      (s[cutLength h s - 1]?).map Sigma.snd = some .branch) := by
  induction s generalizing h with
  | nil => simp [cutLength, branches, hh, Nat.not_le.mpr hh]
  | cons a s ih =>
    by_cases ha : a.2 = .branch
    · by_cases h1 : h ≤ 1
      · have he : h = 1 := by omega
        subst h
        simp only [cutLength, ha, and_self, le_refl, if_true]
        refine ⟨by simp, ?_, ?_, ?_⟩
        · intro i hi
          have : i = 0 := by omega
          subst i
          simp [branches]
        · simp [branches_cons, ha]
        · intro _
          refine ⟨by decide, ?_, ?_⟩
          · simp [branches, ha]
          · simp [ha]
      · have hp : 0 < h-1 := by omega
        obtain ⟨bound, before, full, last⟩ := ih (h-1) hp
        simp only [cutLength, ha, true_and, h1, if_false, if_true]
        refine ⟨by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
        · intro i hi
          cases i with
          | zero => simpa [branches] using hh
          | succ i =>
            have hb := before i (by omega)
            simp only [List.take_succ_cons, branches_cons, ha, if_true]
            omega
        · intro hs
          have hb : branches s < h-1 := by rw [branches_cons, if_pos ha] at hs; omega
          rw [full hb, List.length_cons]
          omega
        · intro hs
          have hb : h-1 ≤ branches s := by rw [branches_cons, if_pos ha] at hs; omega
          obtain ⟨pos, counted, last'⟩ := last hb
          refine ⟨by omega, ?_, ?_⟩
          · simp only [Nat.add_comm 1, List.take_succ_cons, branches_cons, ha, if_true,
              counted]
            omega
          · have he : 1 + cutLength (h-1) s - 1 = (cutLength (h-1) s - 1)+1 := by omega
            rw [he, List.getElem?_cons_succ]
            exact last'
    · obtain ⟨bound, before, full, last⟩ := ih h hh
      simp only [cutLength, ha, false_and, if_false]
      refine ⟨by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => simpa [branches] using hh
        | succ i =>
          simpa only [List.take_succ_cons, branches_cons, if_neg ha, Nat.add_zero]
            using before i (by omega)
      · intro hs
        have hb : branches s < h := by simpa [branches_cons, ha] using hs
        rw [full hb, List.length_cons]
        omega
      · intro hs
        have hb : h ≤ branches s := by simpa [branches_cons, ha] using hs
        obtain ⟨pos, counted, last'⟩ := last hb
        refine ⟨by omega, ?_, ?_⟩
        · simpa only [Nat.add_comm 1, List.take_succ_cons, branches_cons, if_neg ha,
            Nat.add_zero] using counted
        · have he : 1 + cutLength h s - 1 = (cutLength h s - 1)+1 := by omega
          rw [he, List.getElem?_cons_succ]
          exact last'

private theorem trial_properties (h : Nat) (v : Source) (hh : 0 < h)
    (hg : h ≤ v.length) :
    (trial h v).IsPrefix (acquisitionTrace [] v) ∧
    (trial h v).length ≤ 2*h-1 ∧
    (∀ a ∈ trial h v, a.1.length ≤ h-1 ∧ a.2 ≠ .absent) ∧
    (Completes h v → trial h v = acquisitionTrace [] v ∧ v.length = h) ∧
    (¬ Completes h v → branches (trial h v) = h ∧
      ((trial h v).getLast?).map Sigma.snd = some .branch) := by
  let s := acquisitionTrace [] v
  let k := cutLength h s
  have cp := cut_properties s h hh
  have len : (trial h v).length = k := by
    simp [trial, s, k, List.length_take, Nat.min_eq_left cp.1]
  have bounds : k ≤ 2*h-1 := by
    by_cases hk : k = 0
    · omega
    · have hi : k-1 < s.length := by have hb := cp.1; change k ≤ s.length at hb; omega
      have geom := prefix_geometry v [] (k-1) hi
      have before := cp.2.1 (k-1) (by omega)
      change k-1 ≤ 2 * branches (s.take (k-1)) ∧ _ at geom
      omega
  refine ⟨List.take_prefix _ _, by omega, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp ha
    have hik : i < k := by omega
    have his : i < s.length := lt_of_lt_of_le hik cp.1
    have geom := prefix_geometry v [] i his
    have before := cp.2.1 i hik
    have he' : s[i] = a := by
      simpa only [trial, List.getElem_take] using he
    have honest := (trace_counts v []).2.2.2 a ((List.take_subset _ _) ha)
    refine ⟨?_, honest⟩
    rw [← he']
    have geom := geom.2
    change (s[i]).1.length ≤ List.length ([] : Address) + branches (s.take i) at geom
    simp only [List.length_nil, Nat.zero_add] at geom
    omega
  · intro hc
    have hk := cp.2.2.1 hc
    have counts := (trace_counts v []).2.1
    refine ⟨?_, by change branches s < h at hc; change branches s + 1 = _ at counts; omega⟩
    change s.take k = s
    rw [show k = s.length from hk, List.take_length]
  · intro hc
    have hb : h ≤ branches s := Nat.le_of_not_gt hc
    obtain ⟨pos, counted, last⟩ := cp.2.2.2 hb
    refine ⟨counted, ?_⟩
    rw [List.getLast?_eq_getElem?, len]
    change ((s.take k)[k-1]?).map Sigma.snd = some .branch
    rw [List.getElem?_take_of_lt (by omega)]
    exact last

private theorem iterate_growth (u : Source) (k : Nat) :
    u.length ≤ (substitution^[k] u).length := by
  have total := ActualObserverAbsorbingNormalization.composition_total u
  have h₁ : 1 ≤ Nat.fib (k+1) := Nat.succ_le_of_lt (Nat.fib_pos.mpr (by omega))
  have h₂ : 1 ≤ Nat.fib (k+2) := Nat.succ_le_of_lt (Nat.fib_pos.mpr (by omega))
  rw [SourceCoordinates.NativeRotationDepthGap.iterate_length]
  nlinarith

private theorem equal_size_parity (u : Source) (k : Nat)
    (he : (substitution^[k] u).length = u.length) (even : u.length % 2 = 0) :
    (composition (substitution^[k] u)).2 % 2 = (composition u).2 % 2 := by
  have total := ActualObserverAbsorbingNormalization.composition_total u
  have pos := u.length_pos
  have bound : k ≤ 1 := by
    by_contra hk
    have h₁ : 2 ≤ Nat.fib (k+1) := by
      exact Nat.fib_mono (show 3 ≤ k+1 by omega)
    have h₂ : 2 ≤ Nat.fib (k+2) := by
      exact Nat.fib_mono (show 3 ≤ k+2 by omega)
    rw [SourceCoordinates.NativeRotationDepthGap.iterate_length] at he
    nlinarith
  interval_cases k
  · rfl
  · have counts := (GenealogicalFiberTransport.fiberMap (composition u) 1 ⟨u, rfl⟩).property
    change composition (substitution u) = GraftAffineClosure.step (composition u) at counts
    have zero : (composition u).2 = 0 := by
      rw [SourceCoordinates.NativeRotationDepthGap.iterate_length] at he
      norm_num at he
      omega
    simp only [Function.iterate_one, counts, GraftAffineClosure.step]
    rw [zero, Nat.zero_mod]
    have ha : (composition u).1 = u.length := by omega
    simpa only [ha, Nat.add_zero] using even

private theorem physical_bounds (N : Nat) (v : Source) (s : History) :
    (physicalQueries N s).length ≤ 2 * s.length ∧
    ∀ a ∈ s, (originalQueries N a.1).length ≤ 2 ∧
      ∀ q ∈ originalQueries N a.1, q.length ≤ a.1.length + halfCeil N := by
  have service (a : Report) := original_decoder_service N a.1 v
  have each (a : Report) : (originalQueries N a.1).length ≤ 2 := by
    simpa [listTrace] using (service a).2.1
  constructor
  · induction s with
    | nil => simp [physicalQueries]
    | cons a s ih =>
      have bound := each a
      simp only [physicalQueries, List.flatMap_cons, List.length_append,
        List.length_cons] at *
      omega
  · intro a _
    exact ⟨each a, (service a).2.2.1⟩

private theorem trace_leaf_visits (v : Source) (p : Address) :
    leafVisits (acquisitionTrace p v) = v.length := by
  induction v generalizing p with
  | of b => cases b <;> rfl
  | mul s t ihs iht =>
    have hs := ihs (p ++ [false])
    have ht := iht (p ++ [true])
    simp only [leafVisits] at hs ht ⊢
    simpa [acquisitionTrace, FreeMagma.length] using congrArg₂ (· + ·) hs ht

/-- The predecessor used as proof data for a trial at candidate offset N. -/
def virtualSource (u : Source) (τ N : Nat) : Source := substitution^[τ-N] u

/-- Successive offsets increase only after a rejected trial. -/
inductive Attempts (start : Nat) (success : Nat → Prop) : Nat → Prop
  | first : Attempts start success start
  | next {N : Nat} : Attempts start success N → ¬ success N → Attempts start success (N+1)

/-- The per-trial contract retains the source producer's order and all paid
stationary decoder calls, without assigning its subtree workspace to the trial. -/
structure TrialSpec (h τ N : Nat) (u y : Source) : Prop where
  image : y = substitution^[N] (virtualSource u τ N)
  producer_prefix :
    ((trial h (virtualSource u τ N)).map (fun a => (0, a.1, a.2))).IsPrefix
      (NativeSerialMachine.reads
        (NativeFullSourceProducer.productionTrace [] (virtualSource u τ N)))
  before_cutoff : ∀ i, i < (trial h (virtualSource u τ N)).length →
    branches ((acquisitionTrace [] (virtualSource u τ N)).take i) < h
  nodes_bound : (trial h (virtualSource u τ N)).length ≤ 2*h-1
  reached : ∀ a ∈ trial h (virtualSource u τ N), a.1.length ≤ h-1 ∧ a.2 ≠ .absent
  decoded : ∀ a ∈ trial h (virtualSource u τ N),
    originalDecode N a.1 ((originalQueries N a.1).map (fun q => readout q y)) = a.2
  decoder_run : ∀ a ∈ trial h (virtualSource u τ N),
    D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.execute readout
      (listController (originalQueries N a.1)
        (fun s => originalDecode N a.1 (s.map Sigma.snd)))
      ((originalQueries N a.1).length+1) [] y =
        some (listTrace (originalQueries N a.1) y, a.2)
  guard_accept : ∀ a ∈ trial h (virtualSource u τ N), a.1 ≠ [] →
    guardAccept N (readout (a.1.dropLast ++ rights (N/2+1)) y) = true
  even_value_present : ∀ a ∈ trial h (virtualSource u τ N), N%2 = 0 →
    readout (a.1 ++ rights (halfCeil N)) y ≠ .absent
  decoder_calls : ∀ a ∈ trial h (virtualSource u τ N),
    (originalQueries N a.1).length ≤ 2
  reads_bound : (physicalQueries N (trial h (virtualSource u τ N))).length ≤ 4*h-2
  literal_bound : ∀ q ∈ physicalQueries N (trial h (virtualSource u τ N)),
    q.length ≤ h-1 + halfCeil N
  completion : Completes h (virtualSource u τ N) →
    trial h (virtualSource u τ N) = acquisitionTrace [] (virtualSource u τ N) ∧
    (virtualSource u τ N).length = h ∧
    (h % 2 = 0 → parity (trial h (virtualSource u τ N)) = (composition u).2 % 2)
  completed_counts : Completes h (virtualSource u τ N) →
    leafVisits (trial h (virtualSource u τ N)) = h ∧
    branches (trial h (virtualSource u τ N)) = h-1 ∧
    (trial h (virtualSource u τ N)).length = 2*h-1
  endpoint_parity : N = τ →
    parity (trial h (virtualSource u τ N)) = (composition u).2 % 2
  direct_queries : N = 0 → physicalQueries N (trial h (virtualSource u τ N)) =
    (trial h (virtualSource u τ N)).map Sigma.fst
  rejection : ¬ Completes h (virtualSource u τ N) →
    branches (trial h (virtualSource u τ N)) = h ∧
    ((trial h (virtualSource u τ N)).getLast?).map Sigma.snd = some .branch ∧ N < τ
  endpoint : N = τ → Completes h (virtualSource u τ N)

private theorem single_trial (h τ N : Nat) (u y : Source) (hu : u.length = h)
    (hy : y = substitution^[τ] u) (hN : N ≤ τ) : TrialSpec h τ N u y := by
  have hh : 0 < h := by rw [← hu]; exact u.length_pos
  let v := virtualSource u τ N
  have image : y = substitution^[N] v := by
    dsimp [v, virtualSource]
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le hN]
    exact hy
  have hg : h ≤ v.length := by simpa [← hu, v, virtualSource] using iterate_growth u (τ-N)
  obtain ⟨pre, bound, reached, complete, reject⟩ := trial_properties h v hh hg
  have cp := cut_properties (acquisitionTrace [] v) h hh
  have phys := physical_bounds N v (trial h v)
  have endpt : N = τ → Completes h v := by
    intro he
    have hv : v = u := by simp [v, virtualSource, he]
    have count := (trace_counts u []).2.1
    unfold Completes
    rw [hv]
    omega
  have truth := (D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization.execute_transfer
    readout ActualTreeReadoutAcquisition.acquisitionPolicy _ [] v _ _
      (ActualTreeReadoutAcquisition.acquisition_foundation.2 v)).1
  have decoded : ∀ a ∈ trial h v,
      originalDecode N a.1 ((originalQueries N a.1).map (fun q => readout q y)) = a.2 := by
    intro a ha
    rw [image, original_decoder_correct]
    exact truth a (pre.subset ha)
  have guard : ∀ a ∈ trial h v, a.1 ≠ [] →
      guardAccept N (readout (a.1.dropLast ++ rights (N/2+1)) y) = true := by
    intro a ha hp
    have eqp := List.dropLast_concat_getLast hp
    have hg := original_presence_guard N a.1.dropLast (a.1.getLast hp) v
    rw [eqp] at hg
    rw [image]
    apply hg.mpr
    rw [truth a (pre.subset ha)]
    exact (reached a ha).2
  refine {
    image := image
    producer_prefix := ?_
    before_cutoff := ?_
    nodes_bound := bound
    reached := reached
    decoded := decoded
    decoder_run := ?_
    guard_accept := guard
    even_value_present := ?_
    decoder_calls := fun a ha => (phys.2 a ha).1
    reads_bound := by
      change (physicalQueries N (trial h v)).length ≤ 4*h-2
      have hp := phys.1
      omega
    literal_bound := ?_
    completion := ?_
    completed_counts := ?_
    endpoint_parity := ?_
    direct_queries := ?_
    rejection := ?_
    endpoint := endpt }
  · rw [(NativeFullSourceProducer.native_source_producer v).2.2.2.1]
    exact pre.map _
  · intro i hi
    apply cp.2.1 i
    change i < (trial h v).length at hi
    simpa only [trial, List.length_take, Nat.min_eq_left cp.1] using hi
  · intro a ha
    rw [image]
    have run := (original_decoder_service N a.1 v).1
    rw [truth a (pre.subset ha)] at run
    exact run
  · intro a ha even
    have hd := decoded a ha
    have pres := (reached a ha).2
    by_cases hz : N = 0
    · subst N
      simpa [originalQueries, originalDecode, halfCeil, rights] using
        (fun he => pres (hd.symm.trans he))
    · by_cases hp : a.1 = []
      · simp [originalDecode, originalQueries, hz, hp, decodeLabel, even] at hd
        simpa [hp] using (fun he => pres (hd.symm.trans he))
      · have hg := guard a ha hp
        simp [originalDecode, originalQueries, hz, hp, decodeLabel, even, hg] at hd
        exact fun he => pres (hd.symm.trans he)
  · intro q hq
    obtain ⟨a, ha, hq⟩ := List.mem_flatMap.mp hq
    have hp := (phys.2 a ha).2 q hq
    have hd := (reached a ha).1
    omega
  · intro hc
    obtain ⟨full, size⟩ := complete hc
    refine ⟨full, size, ?_⟩
    intro even
    rw [full, parity, (trace_counts v []).2.2.1]
    exact equal_size_parity u (τ-N) (by simpa [v, virtualSource, hu] using size)
      (by simpa [hu] using even)
  · intro hc
    obtain ⟨full, size⟩ := complete hc
    have counts := trace_counts v []
    rw [full]
    exact ⟨by rw [trace_leaf_visits, size], by omega, by omega⟩
  · intro he
    have hv : v = u := by simp [v, virtualSource, he]
    have full := (complete (endpt he)).1
    change parity (trial h v) = _
    rw [full, hv, parity, (trace_counts u []).2.2.1]
  · intro hz
    subst N
    simp [physicalQueries, originalQueries, ← List.map_eq_flatMap]
  · intro hr
    obtain ⟨count, last⟩ := reject hr
    exact ⟨count, last, lt_of_le_of_ne hN (fun he => hr (endpt he))⟩

/-- Every candidate reached by increasing after rejection is an actual image
candidate. The first completion occurs no later than the true epoch, including
zero; each trial has the cutoff, parity and stationary Read bounds above. -/
theorem bounded_preorder_trial (h τ start : Nat) (u y : Source)
    (hu : u.length = h) (hy : y = substitution^[τ] u) (hstart : start ≤ τ) :
    (∀ N, N ≤ τ → TrialSpec h τ N u y) ∧
    (∀ N, Attempts start (fun k => Completes h (virtualSource u τ k)) N → N ≤ τ) ∧
    ∃ K, start ≤ K ∧ K ≤ τ ∧ Completes h (virtualSource u τ K) ∧
      (∀ N, start ≤ N → N < K → ¬ Completes h (virtualSource u τ N)) ∧
      K-start+1 ≤ τ-start+1 ∧
      (∀ T, τ ≤ T → K-start+1 ≤ T+1) ∧
      (∀ N, start ≤ N → N ≤ K →
        Attempts start (fun k => Completes h (virtualSource u τ k)) N ∧
        TrialSpec h τ N u y) := by
  have single := fun N hN => single_trial h τ N u y hu hy hN
  have licensed : ∀ N,
      Attempts start (fun k => Completes h (virtualSource u τ k)) N → N ≤ τ := by
    intro N run
    induction run with
    | first => exact hstart
    | @next N run reject ih =>
      have strict := ((single N ih).rejection reject).2.2
      omega
  have exists_finish : ∃ K, start ≤ K ∧ K ≤ τ ∧ Completes h (virtualSource u τ K) :=
    ⟨τ, hstart, le_rfl, (single τ le_rfl).endpoint rfl⟩
  classical
  let K := Nat.find exists_finish
  have hk := Nat.find_spec exists_finish
  have minimal : ∀ N, start ≤ N → N < K → ¬ Completes h (virtualSource u τ N) := by
    intro N hn hnk hc
    have small := Nat.find_min' exists_finish ⟨hn, by omega, hc⟩
    omega
  have run : ∀ d, start+d ≤ K →
      Attempts start (fun k => Completes h (virtualSource u τ k)) (start+d) := by
    intro d
    induction d with
    | zero => intro _; exact Attempts.first
    | succ d ih =>
      intro hd
      have hr := minimal (start+d) (by omega) (by omega)
      exact Attempts.next (ih (by omega)) hr
  refine ⟨single, licensed, K, hk.1, hk.2.1, hk.2.2, minimal, by omega,
    by intro T hT; omega, ?_⟩
  intro N hn hNK
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact ⟨run d hNK, single (start+d) (hNK.trans hk.2.1)⟩

end D5.S3.Arith.FibonacciAtomic.Observer.BoundedPreorderTrial
