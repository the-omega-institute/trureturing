/- GID: D5/S3/Arith/FibonacciAtomic/LocalWiring/NativePastAcquisitionBarrier
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LocalWiring/NativePastAcquisitionBarrier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite native observation traces and the class-uniform mature-bit barrier. -/

import D5.S3.Arith.FibonacciAtomic.LocalWiring.LawfulSourceReadiness
import Mathlib.Order.Filter.Defs

namespace D5.S3.Arith.FibonacciAtomic.LocalWiring.NativePastAcquisitionBarrier

open LocalTwoStepRecognizer KnownSeedCurrentFibers PhysicalBirthClock
open OrderedBirthPrefix PublicRowSeedReadiness
open LawfulSourceReadiness

/-- An observer's choice receives no source input. Local allocations and retained data can
be arbitrarily rich, but are computed from the accessible inputs. -/
inductive Move (Local : Type)
  | service (action : Action)
  | compute (next : Local)
  | retain (value : Local)
  | stop

/-- Each actual observable step logs the request, reply, or source-free local action. -/
inductive Event (Local : Type)
  | service (action : Action) (answer : Reply)
  | compute (next : Local)
  | retain (value : Local)
  | stop

/-- Complete accessible record at a finite prefix of the serial run. The true labelled
tree is not a record field and is never available to the observer through update. -/
structure Record (Local : Type) where
  cut : Nat
  log : List (Event Local)
  register : Local
  retained : List Local
  stopped : Bool

/-- Public inputs and a common source-independent tape parameterize all decisions.
Access to the whole transcript makes loss of data unnecessary for the lower bound. -/
structure Observer (Public Tape Local : Type) where
  startState : Public → Tape → Local
  choose : Public → Tape → Record Local → Move Local

/-- The alpha-initialized observer has only its source-free initial state. -/
def initial {Public Tape Local : Type} (A : Observer Public Tape Local)
    (u : Public) (tape : Tape) : Record Local :=
  ⟨0, [], A.startState u tape, [], false⟩

/-- One accessible step. Read and Update call the frozen actual service, which replies
with literal incidence or a common acknowledgement respectively. -/
def advance {Public Tape Local : Type} (A : Observer Public Tape Local)
    (u : Public) (tape : Tape) (s : OutputStream) (r : Record Local) :
    Record Local :=
  if r.stopped then r else
    match A.choose u tape r with
    | .service a => { r with cut := nextEpoch r.cut a, log := r.log ++ [.service a (reply (birthOf s) r.cut a)] }
    | .compute x => { r with register := x, log := r.log ++ [.compute x] }
    | .retain x => { r with retained := r.retained ++ [x], log := r.log ++ [.retain x] }
    | .stop => { r with stopped := true, log := r.log ++ [.stop] }

/-- Every finite prefix is represented, including nonterminal ones. A stopped record
remains fixed when indexed later; this does not append any fictitious events. -/
def run {Public Tape Local : Type} (A : Observer Public Tape Local)
    (u : Public) (tape : Tape) (s : OutputStream) : Nat → Record Local
  | 0 => initial A u tape
  | k+1 => advance A u tape s (run A u tape s k)

private theorem cut_le_advance {Public Tape Local : Type}
    (A : Observer Public Tape Local) (u : Public) (tape : Tape)
    (s : OutputStream) (r : Record Local) : r.cut ≤ (advance A u tape s r).cut := by
  unfold advance
  split
  · exact Nat.le_refl _
  · split
    next a ha => cases a <;> simp [nextEpoch]
    all_goals exact Nat.le_refl _

private theorem agree_advance {Public Tape Local : Type}
    (A : Observer Public Tape Local) (u : Public) (tape : Tape)
    {s t : OutputStream} {r : Record Local}
    (h : ∀ a, reply (birthOf s) r.cut a = reply (birthOf t) r.cut a) :
    advance A u tape s r = advance A u tape t r := by
  unfold advance
  split
  · rfl
  · split
    next a ha => rw [h a]
    all_goals rfl

private theorem agree_run {Public Tape Local : Type}
    (A : Observer Public Tape Local) (u : Public) (tape : Tape)
    {s t : OutputStream} {n : Nat}
    (h : ∀ e ≤ n, ∀ a, reply (birthOf s) e a = reply (birthOf t) e a)
    (k : Nat) (hk : (run A u tape s k).cut ≤ n) :
    run A u tape s k = run A u tape t k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (advance A u tape s (run A u tape s k)).cut ≤ n at hk
    have hcut := (cut_le_advance A u tape s (run A u tape s k)).trans hk
    simp only [run]
    rw [← ih hcut]
    exact agree_advance A u tape (h _ hcut)

private theorem run_after_stop {Public Tape Local : Type}
    (A : Observer Public Tape Local) (u : Public) (tape : Tape)
    (s : OutputStream) {i j : Nat} (hij : i ≤ j)
    (hst : (run A u tape s i).stopped = true) :
    run A u tape s j = run A u tape s i := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j _ ih => simp [run, ih, advance, hst]

/-- Any two terminal records of the same serial run coincide, without a step cap. -/
private theorem unique_terminal_record {Public Tape Local : Type}
    (A : Observer Public Tape Local) (u : Public) (tape : Tape)
    (s : OutputStream) {i j : Nat}
    (hi : (run A u tape s i).stopped = true)
    (hj : (run A u tape s j).stopped = true) :
    run A u tape s i = run A u tape s j := by
  rcases Nat.le_total i j with h | h
  · exact (run_after_stop A u tape s h hi).symm
  · exact run_after_stop A u tape s h hj

private theorem matureSize_mono : Monotone matureSize := by
  have clock_mono : Monotone clockSum := by
    apply monotone_nat_of_le_succ
    intro k
    simp [clockSum, List.range_succ]
  intro e n h
  exact clock_mono (Nat.sub_le_sub_right h 1)

private theorem matureWord_take (s : OutputStream) {e n : Nat} (h : e ≤ n) :
    (matureWord n s).take (matureSize e) = matureWord e s := by
  rw [matureWord, matureWord, prefixBits, prefixBits, ← List.map_take, List.take_range,
    Nat.min_eq_left (matureSize_mono h)]

private theorem matureWord_past {s t : OutputStream} {e n : Nat} (hen : e ≤ n)
    (heq : matureWord n s = matureWord n t) : matureWord e s = matureWord e t := by
  rw [← matureWord_take s hen, ← matureWord_take t hen, heq]

-- The public §28.2 decoder exports erased geometry. The actual native reply reads
-- the labelled tree instead; only this structural address bridge is needed.
private theorem present_erase (t : Labelled) (p : Address) :
    present t p = present (shape t) p := by
  induction p generalizing t with
  | nil => simp [present, atTree]
  | cons b p ih =>
    cases t with
    | of x => cases b <;> rfl
    | mul l r => cases b
                 · exact ih l
                 · exact ih r

private theorem shape_of_matureWord (e : Nat) (s : OutputStream) (he : 2 ≤ e) :
    shapeOfPrefix e (matureWord e s) = shape (physicalTree e s) := by
  exact (exact_ordered_birth_prefix (birthOf s) e he).2.2.2.2.2.2.2.2.2.1

private theorem shape_eq_of_matureWord {s t : OutputStream} {e : Nat}
    (heq : matureWord e s = matureWord e t) :
    shape (physicalTree e s) = shape (physicalTree e t) := by
  by_cases he : 2 ≤ e
  · rw [← shape_of_matureWord e s he, ← shape_of_matureWord e t he, heq]
  · have he' : e = 0 ∨ e = 1 := by omega
    rcases he' with rfl | rfl <;> rfl

private theorem reply_agrees_past {s t : OutputStream} {e n : Nat} (hen : e ≤ n)
    (heq : matureWord n s = matureWord n t) (a : Action) :
    reply (birthOf s) e a = reply (birthOf t) e a := by
  cases a with
  | update => rfl
  | read p =>
    change Reply.answer (present (physicalTree e s) p) =
      Reply.answer (present (physicalTree e t) p)
    rw [present_erase (physicalTree e s), present_erase (physicalTree e t),
      shape_eq_of_matureWord (matureWord_past hen heq)]

private theorem attained_collision {O : Type} (C : LawfulClass) (hC : ValidClass C)
    (n : Nat) (hn : 2 ≤ n) (task : OutputStream → O)
    (h : ¬ UniformReady C .incidence n task) :
    ∃ s t, ClassLegal C s ∧ ClassLegal C t ∧
      matureWord n s = matureWord n t ∧ task s ≠ task t := by
  classical
  by_contra! hpair
  let recover (xs : List _) : Option O :=
    if he : ∃ t, ClassLegal C t ∧ acquired .incidence n t = xs then
      some (task (Classical.choose he))
    else none
  apply h
  refine ⟨recover, ?_⟩
  intro s hs
  unfold recover
  split
  next he =>
    obtain ⟨ht, heq⟩ := Classical.choose_spec he
    exact congrArg some (hpair _ _ ht hs
      ((lawful_source_readiness C hC n hn).2.2.2.1 .incidence _ _ |>.mp heq))
  next he => exact False.elim (he ⟨s, hs, rfl⟩)

private theorem disjoint_not_both_eventual {Tape : Type} (F : Filter Tape) [Filter.NeBot F]
    (A B : Tape → Prop) (ha : ∀ᶠ x in F, A x) (hb : ∀ᶠ x in F, B x)
    (hd : ∀ x, ¬ (A x ∧ B x)) : False := by
  have hzero : (∅ : Set Tape) ∈ F :=
    Filter.mem_of_superset (Filter.inter_mem ha hb) fun x hx =>
      (hd x hx).elim
  have heq : F = ⊥ := Filter.ext fun S =>
    ⟨fun _ => Filter.mem_bot,
      fun _ => Filter.mem_of_superset hzero (Set.empty_subset S)⟩
  exact Filter.NeBot.ne' heq

/-- For a fixed common tape, the event of seeing any prescribed accessible record
at a given cut, at any finite prefix, is expressed as a tape preimage. -/
def cutEvent {Public Tape Local : Type} (A : Observer Public Tape Local)
    (u : Public) (s : OutputStream) (n : Nat) (E : Set (Record Local)) : Set Tape :=
  { tape | ∃ k, (run A u tape s k).cut = n ∧ run A u tape s k ∈ E }

/-- An exact answer is decoded solely from accessible data when the observer
actually stops at the specified cut. The finite step count need not be shared or bounded. -/
def ZeroErrorAt {Public Tape Local O : Type} (F : Filter Tape)
    (A : Observer Public Tape Local) (u : Public) (C : LawfulClass) (n : Nat)
    (out : Public → Tape → Record Local → Option O) (task : OutputStream → O) : Prop :=
  ∀ s, ClassLegal C s → ∀ᶠ tape in F, ∃ k,
    let r := run A u tape s k
    r.cut = n ∧ r.stopped = true ∧ out u tape r = some (task s)

private theorem record_agrees {Public Tape Local : Type}
    (A : Observer Public Tape Local) (u : Public) (tape : Tape)
    {s t : OutputStream} {n : Nat} (heq : matureWord n s = matureWord n t)
    (k : Nat) (hk : (run A u tape s k).cut ≤ n) :
    run A u tape s k = run A u tape t k :=
  agree_run A u tape (fun _ he a => reply_agrees_past he heq a) k hk

/-- Replay a finite observation prefix with a fixed padding outside the known word. -/
def replay {Public Tape Local : Type} (A : Observer Public Tape Local)
    (u : Public) (tape : Tape) (word : List Bool) (k : Nat) : Record Local :=
  run A u tape (fun i => word[i]?.getD false) k

private theorem matureWord_pad (n : Nat) (s : OutputStream) :
    matureWord n (fun i => (matureWord n s)[i]?.getD false) = matureWord n s := by
  unfold matureWord
  apply List.ext_getElem
  · simp [prefixBits]
  · intro i h₁ h₂
    have hi : i < matureSize n := by simpa [prefixBits] using h₂
    simp [prefixBits, consume, birthOf, hi]

private theorem replay_exact {Public Tape Local : Type}
    (A : Observer Public Tape Local) (u : Public) (tape : Tape) (s : OutputStream)
    (n k : Nat) (hk : (run A u tape s k).cut ≤ n) :
    run A u tape s k = replay A u tape (matureWord n s) k :=
  record_agrees A u tape (matureWord_pad n s).symm k hk

private theorem cutEvent_eq {Public Tape Local : Type}
    (A : Observer Public Tape Local) (u : Public) {s t : OutputStream} {n : Nat}
    (heq : matureWord n s = matureWord n t) (E : Set (Record Local)) :
    cutEvent A u s n E = cutEvent A u t n E := by
  ext tape
  change (∃ k, (run A u tape s k).cut = n ∧ run A u tape s k ∈ E) ↔
    (∃ k, (run A u tape t k).cut = n ∧ run A u tape t k ∈ E)
  constructor
  · rintro ⟨k,hcut,hE⟩
    exact ⟨k, record_agrees A u tape heq k hcut.le ▸ hcut,
      record_agrees A u tape heq k hcut.le ▸ hE⟩
  · rintro ⟨k,hcut,hE⟩
    exact ⟨k, record_agrees A u tape heq.symm k hcut.le ▸ hcut,
      record_agrees A u tape heq.symm k hcut.le ▸ hE⟩

private theorem not_zeroErrorAt {Public Tape Local O : Type} (F : Filter Tape)
    [Filter.NeBot F] (A : Observer Public Tape Local) (u : Public) (C : LawfulClass)
    (n : Nat) (out : Public → Tape → Record Local → Option O) (task : OutputStream → O)
    (s t : OutputStream) (hs : ClassLegal C s) (ht : ClassLegal C t)
    (heq : matureWord n s = matureWord n t) (hd : task s ≠ task t) :
    ¬ ZeroErrorAt F A u C n out task := by
  intro h
  apply disjoint_not_both_eventual F _ _ (h s hs) (h t ht)
  intro tape both
  rcases both with ⟨⟨i,hcut,hsStop,hsOut⟩,⟨j,_,htStop,htOut⟩⟩
  have he := record_agrees A u tape heq i hcut.le
  have hst : (run A u tape t i).stopped = true := he ▸ hsStop
  rw [he, unique_terminal_record A u tape t hst htStop, htOut] at hsOut
  exact hd (Option.some.inj hsOut).symm

/-- Actual finite native observations at a cut depend only on the allowed
inputs and the mature word. A common tape law cannot make either lawful class
uniformly zero-error for any of the three tasks below its mature-bit threshold. -/
theorem native_past_acquisition_barrier
    (n : Nat) (s t : OutputStream)
    {Public Tape Local : Type} (A : Observer Public Tape Local) (u : Public) :
    (∀ (e : Nat) (a : Action), e ≤ n → matureWord n s = matureWord n t →
      reply (birthOf s) e a = reply (birthOf t) e a) ∧
    (∀ (tape : Tape) (k : Nat), (run A u tape s k).cut ≤ n →
      run A u tape s k = replay A u tape (matureWord n s) k) ∧
    (matureWord n s = matureWord n t →
      (∀ (tape : Tape) (k : Nat), (run A u tape s k).cut ≤ n →
        run A u tape s k = run A u tape t k) ∧
      ∀ E : Set (Record Local), cutEvent A u s n E = cutEvent A u t n E) ∧
    (∀ (C : LawfulClass), ValidClass C → 2 ≤ n → matureSize n < requiredBits C →
      ∀ (F : Filter Tape) [Filter.NeBot F]
        (labels : Public → Tape → Record Local → Option Labelled)
        (next : Public → Tape → Record Local → Option (Address → Bool))
        (behavior : Public → Tape → Record Local → Option FutureBehavior),
      (¬ ZeroErrorAt F A u C n labels (physicalTree n)) ∧
      (¬ ZeroErrorAt F A u C n next (fun w p => queryNext n p w)) ∧
      (¬ ZeroErrorAt F A u C n behavior (future n))) := by
  refine ⟨fun _ a he hm => reply_agrees_past he hm a, fun tape k => replay_exact A u tape s n k,
    fun hm => ⟨fun tape k => record_agrees A u tape hm k, cutEvent_eq A u hm⟩, ?_⟩
  intro C hC hn hshort F _ labels next behavior
  have hready := (lawful_source_readiness C hC n hn).2.1 .incidence
  have reject {O : Type} (out : Public → Tape → Record Local → Option O)
      (task : OutputStream → O) (h : ¬ UniformReady C .incidence n task) :
      ¬ ZeroErrorAt F A u C n out task := by
    obtain ⟨a,b,ha,hb,heq,hd⟩ := attained_collision C hC n hn task h
    exact not_zeroErrorAt F A u C n out task a b ha hb heq hd
  exact ⟨reject labels _ (fun h => (Nat.not_le.mpr hshort) (hready.1.mp h)),
    reject next _ (fun h => (Nat.not_le.mpr hshort) (hready.2.1.mp h)),
    reject behavior _ (fun h => (Nat.not_le.mpr hshort) (hready.2.2.mp h))⟩

#print axioms native_past_acquisition_barrier

end D5.S3.Arith.FibonacciAtomic.LocalWiring.NativePastAcquisitionBarrier
