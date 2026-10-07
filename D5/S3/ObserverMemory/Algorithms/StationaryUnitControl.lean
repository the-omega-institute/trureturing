/- GID: D5/S3/ObserverMemory/Algorithms/StationaryUnitControl
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/StationaryUnitControl
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stationary unit tables separate initialized configurations and charge literal tails. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.StationaryUnitControl

attribute [local instance] Classical.propDecidable

universe u

/-- The table can inspect only its nominal control state. -/
inductive UnitInstruction (P : Nat) (Q : Type u) where
  | wait : Q → UnitInstruction P Q
  | read : (Fin 3 → Q) → UnitInstruction P Q
  | halt : ZMod (3 * P) → UnitInstruction P Q

/-- One common initial state and one total, stationary instruction table. -/
structure Controller (P : Nat) (Q : Type u) where
  initial : Q
  instruction : Q → UnitInstruction P Q

abbrev Configuration (P : Nat) (Q : Type u) := ZMod (3 * P) × Q

variable {P : Nat} {Q : Type u}

/-- The physical digit, with no relabeling of the three absolute blocks. -/
def digit (hP : 1 < P) (s : ZMod (3 * P)) : Fin 3 := by
  letI : NeZero (3 * P) := ⟨by omega⟩
  exact ⟨s.val / P, (Nat.div_lt_iff_lt_mul (by omega)).2 (by
    simpa [Nat.mul_comm] using s.val_lt)⟩

/-- Halt has no successor and contributes no action to an execution word. -/
def Controller.step (C : Controller P Q) (hP : 1 < P)
    (c : Configuration P Q) : Option (Configuration P Q) :=
  match C.instruction c.2 with
  | .wait q => some (c.1 + 1, q)
  | .read row => some (c.1, row (digit hP c.1))
  | .halt _ => none

/-- A total extension used only to index a trajectory; halt is absorbing. -/
def Controller.next (C : Controller P Q) (hP : 1 < P)
    (c : Configuration P Q) : Configuration P Q :=
  (C.step hP c).getD c

def Controller.run (C : Controller P Q) (hP : 1 < P)
    (c : Configuration P Q) (t : Nat) : Configuration P Q :=
  (C.next hP)^[t] c

def IsRead (C : Controller P Q) (q : Q) : Prop :=
  ∃ row, C.instruction q = .read row

def IsWait (C : Controller P Q) (q : Q) : Prop :=
  ∃ next, C.instruction q = .wait next

/-- A finite run stops at n, with no earlier halt, and emits the stored label.
The natural n is a proof index, never an input to the instruction table. -/
structure FiniteRun (C : Controller P Q) (hP : 1 < P)
    (c : Configuration P Q) (n : Nat) (label : ZMod (3 * P)) : Prop where
  halt : C.instruction (C.run hP c n).2 = .halt label
  live : ∀ t, t < n → ∀ z, C.instruction (C.run hP c t).2 ≠ .halt z

/-- Exact semantic word conditions for W^ell R(W^+R)*, stopping after its
last read. Singleton continuations and control cycles are unrestricted. -/
structure WordShape (C : Controller P Q) (hP : 1 < P)
    (c : Configuration P Q) (n ell h : Nat) : Prop where
  first_before_stop : ell < n
  prefix_wait : ∀ t, t < ell → IsWait C (C.run hP c t).2
  first_read : IsRead C (C.run hP c ell).2
  after_read_wait : ∀ t, t + 1 < n → IsRead C (C.run hP c t).2 →
    IsWait C (C.run hP c (t + 1)).2
  last_read : IsRead C (C.run hP c (n - 1)).2
  read_bound : ((Finset.range n).filter (fun t =>
    IsRead C (C.run hP c t).2)).card ≤ h

/-- Every original label has its own exact initialized premise. No reachable
subtype replaces the nominal Q, and no resource inequality is assumed. -/
structure Initialized (C : Controller P Q) (hP : 1 < P) (ell h : Nat) where
  length : ZMod (3 * P) → Nat
  finite : ∀ x, FiniteRun C hP (x, C.initial) (length x) x
  shape : ∀ x, WordShape C hP (x, C.initial) (length x) ell h

theorem finite_run_unique (C : Controller P Q) (hP : 1 < P)
    {c : Configuration P Q} {n m : Nat} {x y : ZMod (3 * P)}
    (a : FiniteRun C hP c n x) (b : FiniteRun C hP c m y) :
    n = m ∧ x = y := by
  have hn : n = m := by
    rcases lt_trichotomy n m with hlt | heq | hgt
    · exact False.elim (b.live n hlt x a.halt)
    · exact heq
    · exact False.elim (a.live m hgt y b.halt)
  refine ⟨hn, ?_⟩
  rw [hn] at a
  exact UnitInstruction.halt.inj (a.halt.symm.trans b.halt)

private theorem finite_run_suffix (C : Controller P Q) (hP : 1 < P)
    {c : Configuration P Q} {n : Nat} {x : ZMod (3 * P)}
    (a : FiniteRun C hP c n x) {t : Nat} (ht : t ≤ n) :
    FiniteRun C hP (C.run hP c t) (n - t) x := by
  have shift (k : Nat) : C.run hP (C.run hP c t) k = C.run hP c (t + k) := by
    change (C.next hP)^[k] ((C.next hP)^[t] c) = (C.next hP)^[t + k] c
    rw [← Function.iterate_add_apply, Nat.add_comm]
  constructor
  · rw [shift, Nat.add_sub_of_le ht]
    exact a.halt
  · intro k hk z
    rw [shift]
    exact a.live (t + k) (by omega) z

/-- Equal physical configurations force the same original input and time.
Correctness and finite termination, rather than control-graph acyclicity,
exclude repeats, even when two histories contain the same original label. -/
theorem initialized_configuration_unique (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h)
    {x y : ZMod (3 * P)} {t v : Nat}
    (ht : t ≤ I.length x) (hv : v ≤ I.length y)
    (he : C.run hP (x, C.initial) t = C.run hP (y, C.initial) v) :
    x = y ∧ t = v := by
  have a := finite_run_suffix C hP (I.finite x) ht
  have b := finite_run_suffix C hP (I.finite y) hv
  rw [he] at a
  obtain ⟨hn, hxy⟩ := finite_run_unique C hP a b
  refine ⟨hxy, ?_⟩
  subst y
  omega

/-- A literal sequence of unit waits. Its length is not reduced modulo P. -/
inductive Waits (C : Controller P Q) : Nat → Q → Q → Prop where
  | zero (q : Q) : Waits C 0 q q
  | succ {n : Nat} {q next target : Q}
      (instruction : C.instruction q = .wait next)
      (rest : Waits C n next target) : Waits C (n + 1) q target

/-- The deterministic successor of a wait state; other instructions are fixed
only for this proof-level iteration, never for operational execution. -/
def Controller.waitNext (C : Controller P Q) (q : Q) : Q :=
  match C.instruction q with
  | .wait next => next
  | _ => q

private theorem waits_endpoint (C : Controller P Q) {d : Nat} {q target : Q}
    (w : Waits C d q target) : (C.waitNext)^[d] q = target := by
  induction w with
  | zero q => rfl
  | @succ n q next target hi hw ih =>
    simpa [Function.iterate_succ_apply, Controller.waitNext, hi] using ih

private theorem waits_drop (C : Controller P Q) {d : Nat} {q target : Q}
    (w : Waits C d q target) {i : Nat} (hi : i ≤ d) :
    Waits C (d - i) ((C.waitNext)^[i] q) target := by
  induction i generalizing d q with
  | zero => simpa using w
  | succ i ih =>
    cases w with
    | zero => omega
    | @succ n q next target ins rest =>
      simpa [Function.iterate_succ_apply, Controller.waitNext, ins,
        Nat.succ_sub_succ_eq_sub] using ih rest (by omega)

/-- A wait chain reaches exactly the translated physical phase. -/
theorem waits_physical_execution (C : Controller P Q) (hP : 1 < P)
    {d : Nat} {q target : Q} (w : Waits C d q target)
    (s : ZMod (3 * P)) : C.run hP (s, q) d = (s + (d : ZMod (3 * P)), target) := by
  induction w generalizing s with
  | zero q => simp [Controller.run]
  | @succ n q next target ins rest ih =>
    change (C.next hP)^[n + 1] (s, q) = _
    rw [Function.iterate_succ_apply]
    have hs : C.next hP (s, q) = (s + 1, next) := by
      simp [Controller.next, Controller.step, ins]
    rw [hs]
    simpa [Controller.run, Nat.cast_add, add_assoc, add_comm, add_left_comm] using ih (s + 1)

/-- Intersecting pure waits have the same first future read and remaining
literal length. A deterministic wait cycle cannot reach a read. -/
theorem waits_to_read_unique (C : Controller P Q)
    {d e : Nat} {q target other : Q}
    (a : Waits C d q target) (b : Waits C e q other)
    (ha : IsRead C target) (hb : IsRead C other) : d = e ∧ target = other := by
  induction a generalizing e other with
  | zero q =>
    cases b with
    | zero => exact ⟨rfl, rfl⟩
    | succ ins rest =>
      obtain ⟨row, hr⟩ := ha
      rw [hr] at ins
      cases ins
  | @succ n q next target ins rest ih =>
    cases b with
    | zero =>
      obtain ⟨row, hr⟩ := hb
      rw [hr] at ins
      cases ins
    | @succ m q next' other ins' rest' =>
      have he : next = next' := UnitInstruction.wait.inj (ins.symm.trans ins')
      subst next'
      obtain ⟨hn, ht⟩ := ih rest' ha hb
      exact ⟨congrArg (· + 1) hn, ht⟩

private theorem waits_at_is_wait (C : Controller P Q)
    {d : Nat} {q target : Q} (w : Waits C d q target)
    {i : Nat} (hi : i < d) : IsWait C ((C.waitNext)^[i] q) := by
  have wd := waits_drop C w (Nat.le_of_lt hi)
  cases he : d - i with
  | zero => omega
  | succ k =>
    rw [he] at wd
    cases wd with
    | succ ins rest => exact ⟨_, ins⟩

/-- Every unit position of a literal incoming tail is a distinct nominal state. -/
theorem waits_chain_injective (C : Controller P Q)
    {d : Nat} {q target : Q} (w : Waits C d q target) (hr : IsRead C target) :
    Function.Injective (fun i : Fin d => (C.waitNext)^[i.val] q) := by
  intro i j he
  change (C.waitNext)^[i.val] q = (C.waitNext)^[j.val] q at he
  have a := waits_drop C w (Nat.le_of_lt i.isLt)
  have b := waits_drop C w (Nat.le_of_lt j.isLt)
  rw [he] at a
  have hn := (waits_to_read_unique C a b hr hr).1
  apply Fin.ext
  omega

def prefixState (C : Controller P Q) (hP : 1 < P) (t : Nat) : Q :=
  (C.run hP (0, C.initial) t).2

/-- At every common prefix position, the original labels cover every phase. -/
theorem initialized_prefix (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h) (x : ZMod (3 * P))
    {t : Nat} (ht : t ≤ ell) :
    C.run hP (x, C.initial) t = (x + (t : ZMod (3 * P)), prefixState C hP t) := by
  induction t generalizing x with
  | zero => simp [Controller.run, prefixState]
  | succ t ih =>
    have hit : t ≤ ell := by omega
    have hx := ih x hit
    obtain ⟨next, hn⟩ := (I.shape 0).prefix_wait t (by omega)
    have hz : C.run hP (0, C.initial) t = ((t : ZMod (3 * P)), prefixState C hP t) := by
      simpa using ih 0 hit
    have step (s : ZMod (3 * P)) : C.next hP (s, prefixState C hP t) =
        (s + 1, next) := by
      change C.instruction (prefixState C hP t) = .wait next at hn
      simp only [Controller.next, Controller.step, hn, Option.getD_some]
    have advance (y : ZMod (3 * P)) : C.run hP (y, C.initial) (t + 1) =
        C.next hP (C.run hP (y, C.initial) t) :=
      Function.iterate_succ_apply' _ _ _
    rw [advance, hx, step]
    have hnext : prefixState C hP (t + 1) = next := by
      unfold prefixState
      rw [advance, hz, step]
    simp [Nat.cast_add, add_assoc, hnext]

/-- No original input can return later to a common-prefix state or first-read
state. The proof invokes the indexed premise for the matching original y. -/
theorem prefix_first_read_no_return (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h)
    (x : ZMod (3 * P)) {i t : Nat} (hi : i ≤ ell)
    (hit : i < t) (ht : t ≤ I.length x) :
    (C.run hP (x, C.initial) t).2 ≠ prefixState C hP i := by
  intro he
  let s := (C.run hP (x, C.initial) t).1
  let y : ZMod (3 * P) := s - (i : ZMod (3 * P))
  have hy := initialized_prefix C hP I y hi
  have hc : C.run hP (x, C.initial) t = C.run hP (y, C.initial) i := by
    rw [hy]
    apply Prod.ext
    · simp [y, s]
    · exact he
  have hi' : i ≤ I.length y := le_trans hi (Nat.le_of_lt (I.shape y).first_before_stop)
  have same := initialized_configuration_unique C hP I ht hi' hc
  omega

private theorem trajectory_waits (C : Controller P Q) (hP : 1 < P)
    (c : Configuration P Q) {d t : Nat}
    (hw : ∀ i, i < d → IsWait C (C.run hP c (t + i)).2) :
    Waits C d (C.run hP c t).2 (C.run hP c (t + d)).2 := by
  induction d generalizing t with
  | zero => simpa using Waits.zero (C.run hP c t).2
  | succ d ih =>
    obtain ⟨next, hn⟩ := hw 0 (by omega)
    simp only [Nat.add_zero] at hn
    have hs : (C.run hP c (t + 1)).2 = next := by
      change ((C.next hP)^[t + 1] c).2 = next
      rw [Function.iterate_succ_apply']
      change (C.next hP (C.run hP c t)).2 = next
      simp only [Controller.next, Controller.step, hn, Option.getD_some]
    have rest : Waits C d (C.run hP c (t + 1)).2
        (C.run hP c (t + 1 + d)).2 := ih (fun i hi => by
      have hh := hw (i + 1) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh)
    rw [hs] at rest
    convert Waits.succ hn rest using 1
    congr 2
    omega

abbrev ActualRead (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h) :=
  {q : Q // IsRead C q ∧ ∃ x t, t < I.length x ∧ (C.run hP (x, C.initial) t).2 = q}

abbrev NonrootRead (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h) :=
  {q : ActualRead C hP I // q.val ≠ prefixState C hP ell}

/-- An actual read followed by d literal unit waits and a further actual read.
This records the original input and event time, not a supplied state bound. -/
structure Arrival (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h) (target : Q) (d : Nat) where
  input : ZMod (3 * P)
  time : Nat
  positive : 0 < d
  source_read : IsRead C (C.run hP (input, C.initial) time).2
  within : time + 1 + d < I.length input
  waits : Waits C d (C.run hP (input, C.initial) (time + 1)).2 target
  endpoint : (C.run hP (input, C.initial) (time + 1 + d)).2 = target

private theorem wait_read_false (C : Controller P Q) {q : Q}
    (hw : IsWait C q) (hr : IsRead C q) : False := by
  obtain ⟨next, hn⟩ := hw
  obtain ⟨row, hi⟩ := hr
  rw [hn] at hi
  cases hi

/-- Every actual read target other than the common first read has a realized
positive incoming wait, with its exact original input retained. -/
theorem nonroot_has_arrival (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h) (q : NonrootRead C hP I) :
    ∃ d, Nonempty (Arrival C hP I q.val.val d) := by
  obtain ⟨x, t, ht, he⟩ := q.val.property.2
  have hr : IsRead C (C.run hP (x, C.initial) t).2 := he ▸ q.val.property.1
  have hlt : ell < t := by
    rcases lt_trichotomy t ell with hpre | heq | hlater
    · exact False.elim (wait_read_false C ((I.shape x).prefix_wait t hpre) hr)
    · subst t
      have hp := congrArg Prod.snd (initialized_prefix C hP I x (le_refl ell))
      exact False.elim (q.property (he.symm.trans hp))
    · exact hlater
  let reads := (Finset.range t).filter (fun j => IsRead C (C.run hP (x, C.initial) j).2)
  have nonempty : reads.Nonempty := ⟨ell, by
    simp only [reads, Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt, (I.shape x).first_read⟩⟩
  let v := reads.max' nonempty
  have hv : v ∈ reads := Finset.max'_mem reads nonempty
  have hvt : v < t := (Finset.mem_filter.mp hv).1 |> Finset.mem_range.mp
  have hvr : IsRead C (C.run hP (x, C.initial) v).2 := (Finset.mem_filter.mp hv).2
  have gap : v + 1 < t := by
    by_contra hh
    have eq : t = v + 1 := by omega
    have hw := (I.shape x).after_read_wait v (by omega) hvr
    rw [← eq] at hw
    exact wait_read_false C hw hr
  let d := t - (v + 1)
  have hd : 0 < d := by omega
  have endtime : v + 1 + d = t := by omega
  have between (i : Nat) (hi : i < d) :
      IsWait C (C.run hP (x, C.initial) (v + 1 + i)).2 := by
    have hj : v + 1 + i < t := by omega
    cases ins : C.instruction (C.run hP (x, C.initial) (v + 1 + i)).2 with
    | wait next => exact ⟨next, ins⟩
    | read row =>
      have mem : v + 1 + i ∈ reads := by
        simp only [reads, Finset.mem_filter, Finset.mem_range]
        exact ⟨hj, ⟨row, ins⟩⟩
      have hm : v + 1 + i ≤ v := Finset.le_max' reads _ mem
      omega
    | halt z => exact False.elim ((I.finite x).live _ (by omega) z ins)
  have hw := trajectory_waits C hP (x, C.initial) between
  rw [endtime, he] at hw
  exact ⟨d, ⟨⟨x, v, hd, hvr, by omega, hw, by rw [endtime]; exact he⟩⟩⟩

/-- The finite set contains every realized literal incoming length. -/
noncomputable def arrivalLengths (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h) (q : Q) : Finset Nat := by
  letI : NeZero (3 * P) := ⟨by omega⟩
  exact Finset.univ.biUnion (fun x : ZMod (3 * P) =>
    (Finset.range (I.length x)).filter (fun d => Nonempty (Arrival C hP I q d)))

theorem mem_arrival_lengths (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h) (q : Q) (d : Nat) :
    d ∈ arrivalLengths C hP I q ↔ Nonempty (Arrival C hP I q d) := by
  have : NeZero (3 * P) := ⟨by omega⟩
  constructor
  · intro hd
    obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp hd
    exact (Finset.mem_filter.mp hx).2
  · rintro ⟨a⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨a.input, Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have hh := a.within; omega), ⟨a⟩⟩

private theorem arrival_lengths_nonempty (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h) (q : NonrootRead C hP I) :
    (arrivalLengths C hP I q.val.val).Nonempty := by
  obtain ⟨d, hd⟩ := nonroot_has_arrival C hP I q
  exact ⟨d, (mem_arrival_lengths C hP I _ d).2 hd⟩

/-- The actual maximum is derived from realized requests, including wraps. -/
noncomputable def actualL (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h) (q : NonrootRead C hP I) : Nat :=
  (arrivalLengths C hP I q.val.val).max' (arrival_lengths_nonempty C hP I q)

private theorem longest_arrival_exists (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h) (q : NonrootRead C hP I) :
    Nonempty (Arrival C hP I q.val.val (actualL C hP I q)) :=
  (mem_arrival_lengths C hP I _ _).1 (Finset.max'_mem _ _)

noncomputable def longestArrival (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h) (q : NonrootRead C hP I) :
    Arrival C hP I q.val.val (actualL C hP I q) :=
  Classical.choice (longest_arrival_exists C hP I q)

private theorem prefix_waits (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h) :
    Waits C ell C.initial (prefixState C hP ell) := by
  have hw := trajectory_waits C hP (0, C.initial) (t := 0)
    (fun i hi => by simpa only [Nat.zero_add] using (I.shape 0).prefix_wait i hi)
  simpa [Controller.run, prefixState] using hw

private theorem prefix_iteration (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h) {i : Nat} (hi : i ≤ ell) :
    (C.waitNext)^[i] C.initial = prefixState C hP i := by
  have hw := trajectory_waits C hP (0, C.initial) (t := 0) (d := i)
    (fun j hj => by simpa only [Nat.zero_add] using (I.shape 0).prefix_wait j (by omega))
  have he := waits_endpoint C hw
  simpa [Controller.run, prefixState] using he

noncomputable def tailState (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h)
    (q : NonrootRead C hP I) (i : Fin (actualL C hP I q)) : Q :=
  (C.waitNext)^[i.val]
    (C.run hP ((longestArrival C hP I q).input, C.initial)
      ((longestArrival C hP I q).time + 1)).2

private theorem tail_suffix (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h)
    (q : NonrootRead C hP I) (i : Fin (actualL C hP I q)) :
    Waits C (actualL C hP I q - i.val) (tailState C hP I q i) q.val.val :=
  waits_drop C (longestArrival C hP I q).waits (Nat.le_of_lt i.isLt)

private theorem tail_is_wait (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h)
    (q : NonrootRead C hP I) (i : Fin (actualL C hP I q)) :
    IsWait C (tailState C hP I q i) :=
  waits_at_is_wait C (longestArrival C hP I q).waits i.isLt

/-- A disjoint tagged inventory; the codomain will be the original full Q. -/
abbrev Resource (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h) :=
  ZMod (3 * P) ⊕ (ActualRead C hP I ⊕
    (Fin ell ⊕ (Σ q : NonrootRead C hP I, Fin (actualL C hP I q))))

noncomputable def resourceMap (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h) : Resource C hP I → Q
  | .inl x => (C.run hP (x, C.initial) (I.length x)).2
  | .inr (.inl q) => q.val
  | .inr (.inr (.inl i)) => prefixState C hP i.val
  | .inr (.inr (.inr p)) => tailState C hP I p.1 p.2

private theorem halt_wait_false (C : Controller P Q) {q : Q} {x : ZMod (3 * P)}
    (hh : C.instruction q = .halt x) (hw : IsWait C q) : False := by
  obtain ⟨next, hn⟩ := hw
  rw [hh] at hn
  cases hn

private theorem halt_read_false (C : Controller P Q) {q : Q} {x : ZMod (3 * P)}
    (hh : C.instruction q = .halt x) (hr : IsRead C q) : False := by
  obtain ⟨row, hn⟩ := hr
  rw [hh] at hn
  cases hn

/-- The M original terminals, all actual reads, ell common-prefix positions
and each longest incoming literal tail embed disjointly into the full nominal
carrier, retaining every unused nominal state in the charged codomain. -/
theorem full_nominal_resource_embedding (C : Controller P Q) (hP : 1 < P)
    {ell h : Nat} (I : Initialized C hP ell h) :
    Nonempty (Resource C hP I ↪ Q) := by
  have preRead : IsRead C (prefixState C hP ell) := (I.shape 0).first_read
  have preWait (i : Fin ell) : IsWait C (prefixState C hP i.val) :=
    (I.shape 0).prefix_wait i.val i.isLt
  have preSuffix (i : Fin ell) :
      Waits C (ell - i.val) (prefixState C hP i.val) (prefixState C hP ell) := by
    have hw := waits_drop C (prefix_waits C hP I) (Nat.le_of_lt i.isLt)
    rw [prefix_iteration C hP I (Nat.le_of_lt i.isLt)] at hw
    exact hw
  have preTail (i : Fin ell) (q : NonrootRead C hP I)
      (j : Fin (actualL C hP I q)) : prefixState C hP i.val ≠ tailState C hP I q j := by
    intro he
    have hw := preSuffix i
    rw [he] at hw
    have ht := (waits_to_read_unique C hw (tail_suffix C hP I q j)
      preRead q.val.property.1).2
    exact q.property ht.symm
  refine ⟨⟨resourceMap C hP I, ?_⟩⟩
  intro a b he
  rcases a with x | (q | (i | ⟨q, i⟩)) <;>
    rcases b with y | (r | (j | ⟨r, j⟩)) <;>
    simp only [resourceMap] at he
  · have hx := (I.finite x).halt
    have hy := (I.finite y).halt
    rw [he] at hx
    exact congrArg Sum.inl (UnitInstruction.halt.inj (hx.symm.trans hy))
  · have hx := (I.finite x).halt
    rw [he] at hx
    exact False.elim (halt_read_false C hx r.property.1)
  · have hx := (I.finite x).halt
    rw [he] at hx
    exact False.elim (halt_wait_false C hx (preWait j))
  · have hx := (I.finite x).halt
    rw [he] at hx
    exact False.elim (halt_wait_false C hx (tail_is_wait C hP I r j))
  · have hy := (I.finite y).halt
    rw [← he] at hy
    exact False.elim (halt_read_false C hy q.property.1)
  · exact congrArg (fun z => Sum.inr (Sum.inl z)) (Subtype.ext he)
  · have hw := preWait j
    rw [← he] at hw
    exact False.elim (wait_read_false C hw q.property.1)
  · have hw := tail_is_wait C hP I r j
    rw [← he] at hw
    exact False.elim (wait_read_false C hw q.property.1)
  · have hy := (I.finite y).halt
    rw [← he] at hy
    exact False.elim (halt_wait_false C hy (preWait i))
  · have hw := preWait i
    rw [he] at hw
    exact False.elim (wait_read_false C hw r.property.1)
  · have hw := preSuffix i
    rw [he] at hw
    have hn := (waits_to_read_unique C hw (preSuffix j) preRead preRead).1
    have hij : i = j := Fin.ext (by omega)
    exact congrArg (fun z => Sum.inr (Sum.inr (Sum.inl z))) hij
  · exact False.elim (preTail i r j he)
  · have hy := (I.finite y).halt
    rw [← he] at hy
    exact False.elim (halt_wait_false C hy (tail_is_wait C hP I q i))
  · have hw := tail_is_wait C hP I q i
    rw [he] at hw
    exact False.elim (wait_read_false C hw r.property.1)
  · exact False.elim (preTail j q i he.symm)
  · have hw := tail_suffix C hP I q i
    rw [he] at hw
    have hq := (waits_to_read_unique C hw (tail_suffix C hP I r j)
      q.val.property.1 r.val.property.1).2
    have hqr : q = r := Subtype.ext (Subtype.ext hq)
    subst r
    have hij : i = j := waits_chain_injective C (longestArrival C hP I q).waits
      q.val.property.1 he
    subst j
    rfl

end D5.S3.ObserverMemory.Algorithms.StationaryUnitControl
