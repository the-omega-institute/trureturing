/- GID: D5/S3/ObserverMemory/Algorithms/FixedForestPhysicalExecution
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/FixedForestPhysicalExecution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical complete histories determine literal stationary realizations. -/

import D5.S3.ObserverMemory.Algorithms.FixedForestSlotGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.FixedForestUnitCapacity

open StationaryUnitControl FixedForestTargetInventory FixedForestSlotGraph
attribute [local instance] Classical.propDecidable
universe u

variable {P h ell e : Nat} {Node : Type} [Fintype Node] [DecidableEq Node]
variable {hP : 1 < P} (F : PhysicalForest P h ell Node hP) (R : Prescribed F)

/-- Original bounded labelled events and supported history incidences retain
exactly the same labels, history nodes and read indices. -/
noncomputable def eventIncidenceEquiv :
    {a : Label P × Fin h // a.2.val < F.reads a.1} ≃
      {a : Label P × Node // a.1 ∈ F.support a.2} := by
  let forward : {a : Label P × Fin h // a.2.val < F.reads a.1} →
      {a : Label P × Node // a.1 ∈ F.support a.2} := fun a =>
    ⟨(a.val.1, F.event a.val.1 a.val.2.val), F.event_support _ _ a.property⟩
  apply Equiv.ofBijective forward
  constructor
  · intro a b he
    have pair := congrArg Subtype.val he
    have labels : a.val.1 = b.val.1 := by simpa [forward] using congrArg Prod.fst pair
    have histories : F.event a.val.1 a.val.2.val = F.event b.val.1 b.val.2.val :=
      congrArg Prod.snd pair
    have indices : a.val.2.val = b.val.2.val := by
      rw [← F.event_level _ _ a.property, ← F.event_level _ _ b.property, histories]
    exact Subtype.ext (Prod.ext labels (Fin.ext indices))
  · intro a
    obtain ⟨i, hi, he⟩ := F.support_events a.val.2 a.val.1 a.property
    refine ⟨⟨(a.val.1, ⟨i, lt_of_lt_of_le hi (F.reads_bound _)⟩), hi⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl he

/-- Every charged tag is independent of original input, time and phase. -/
abbrev State (α : Assignment (e := e) F R) :=
  Label P ⊕ (ReadTarget (e := e) F R ⊕
    (Fin ell ⊕ (Σ q : Target (e := e) F R, Fin (L F R α q))))

noncomputable instance stateFintype (α : Assignment (e := e) F R) : Fintype (State F R α) := by
  letI : NeZero (3 * P) := ⟨by omega⟩
  unfold State
  infer_instance

noncomputable instance stateDecidableEq (α : Assignment (e := e) F R) :
    DecidableEq (State F R α) := Classical.decEq _

def terminal (α : Assignment (e := e) F R) (x : Label P) : State F R α := .inl x
def readState (α : Assignment (e := e) F R) (q : ReadTarget (e := e) F R) : State F R α :=
  .inr (.inl q)
def prefixTag (α : Assignment (e := e) F R) (i : Fin ell) : State F R α := .inr (.inr (.inl i))
noncomputable def tail (α : Assignment (e := e) F R)
    (q : Target (e := e) F R) (i : Fin (L F R α q)) : State F R α :=
  .inr (.inr (.inr ⟨q, i⟩))

noncomputable def requestState (α : Assignment (e := e) F R) (n : Node) : State F R α :=
  if hn : F.Internal n then tail F R α (nextTarget F R α n)
    ⟨F.delay n - 1, by have := request_bound F R α hn; have := internal_positive F hn; omega⟩
  else terminal F R α (F.leafLabel n)

private theorem request_equal (α : Assignment (e := e) F R) {n m : Node}
    (hn : F.Internal n) (hm : F.Internal m)
    (ht : nextTarget F R α n = nextTarget F R α m) (hd : F.delay n = F.delay m) :
    requestState F R α n = requestState F R α m := by
  simp only [requestState, dif_pos hn, dif_pos hm, tail]
  apply congrArg (fun p : Σ q : Target (e := e) F R, Fin (L F R α q) =>
    (Sum.inr (Sum.inr (Sum.inr p)) : State F R α))
  apply Sigma.ext ht
  exact (Fin.heq_ext_iff (congrArg (L F R α) ht)).mpr (by simp [hd])

private theorem marked_requests (α : Assignment (e := e) F R) {n m : Node}
    (hs : Shared F R n m) : requestState F R α n = requestState F R α m := by
  have hiH : F.Internal R.H := Finset.card_pos.mp (by rw [R.H_binary]; omega)
  have hiK : F.Internal R.K := Finset.card_pos.mp (by rw [R.K_unary]; omega)
  have hiH1 : F.Internal R.H1 := Finset.card_pos.mp (by rw [R.H1_unary]; omega)
  have hiK1 : F.Internal R.K1 := Finset.card_pos.mp (by rw [R.K1_unary]; omega)
  have nbK : ¬ F.Binary R.K := fun hb => binary_not_unary F hb R.K_unary
  have nbH1 : ¬ F.Binary R.H1 := fun hb => binary_not_unary F hb R.H1_unary
  have nbK1 : ¬ F.Binary R.K1 := fun hb => binary_not_unary F hb R.K1_unary
  have dist : R.K ≠ R.H1 ∧ R.K ≠ R.K1 := by
    have hs := (List.pairwise_cons.mp R.marked_distinct).2
    have hs := (List.pairwise_cons.mp hs).1
    exact ⟨hs R.H1 (by simp), hs R.K1 (by simp)⟩
  have hp : requestState F R α R.H = requestState F R α R.K :=
    request_equal F R α hiH hiK (by simp [nextTarget, R.H_binary, nbK])
      R.production_wait.symm
  have hr : requestState F R α R.H1 = requestState F R α R.K1 :=
    request_equal F R α hiH1 hiK1 (by
      simp [nextTarget, nbH1, nbK1, Ne.symm dist.1, Ne.symm dist.2])
      R.resolving_wait.symm
  rcases hs with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact hp
  · exact hp.symm
  · exact hr
  · exact hr.symm

noncomputable def readRow (α : Assignment (e := e) F R)
    (row : Row (e := e) F R) : State F R α :=
  if hrow : ∃ n, placement F R α n = row then
    requestState F R α (Classical.choose hrow)
  else terminal F R α 0

theorem read_row_at (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) (n : Node) :
    readRow F R α (placement F R α n) = requestState F R α n := by
  have hx : ∃ m, placement F R α m = placement F R α n := ⟨n, rfl⟩
  simp only [readRow, dif_pos hx]
  exact marked_requests F R α (placement_fibers F R hc α (Classical.choose_spec hx))

noncomputable def initial (α : Assignment (e := e) F R) : State F R α :=
  if he : 0 < ell then prefixTag F R α ⟨0, he⟩ else readState F R α (.inl ())

/-- One total stationary table. Unoccupied digits halt at the existing H_0. -/
noncomputable def controller (α : Assignment (e := e) F R) : Controller P (State F R α) where
  initial := initial F R α
  instruction
    | .inl x => .halt x
    | .inr (.inl q) => .read (fun c => readRow F R α (q, c))
    | .inr (.inr (.inl i)) => .wait (
      if hn : i.val + 1 < ell then prefixTag F R α ⟨i.val + 1, hn⟩
      else readState F R α (.inl ()))
    | .inr (.inr (.inr ⟨q, j⟩)) => .wait (
      if hz : j.val = 0 then readState F R α (.inr q)
      else tail F R α q ⟨j.val - 1, by omega⟩)

private theorem run_add {Q : Type} (C : Controller P Q) (a b : Nat)
    (c : Configuration P Q) : C.run hP c (a + b) = C.run hP (C.run hP c a) b := by
  change (C.next hP)^[a + b] c = (C.next hP)^[b] ((C.next hP)^[a] c)
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem tail_chain (α : Assignment (e := e) F R) (q : Target (e := e) F R)
    (j : Nat) (hj : j < L F R α q) :
    Waits (controller F R α) (j + 1) (tail F R α q ⟨j, hj⟩)
      (readState F R α (.inr q)) := by
  induction j with
  | zero =>
    exact Waits.succ (by simp [controller, tail, readState]) (Waits.zero _)
  | succ j ih =>
    apply Waits.succ (next := tail F R α q ⟨j, by omega⟩)
    · simp [controller, tail, readState]
    · exact ih (by omega)

/-- Partial tails preserve every literal unit position, including wraps. -/
private theorem tail_partial (α : Assignment (e := e) F R)
    (q : Target (e := e) F R) (j : Fin (L F R α q)) (s : Label P)
    (k : Nat) (hk : k ≤ j.val) :
    (controller F R α).run hP (s, tail F R α q j) k =
      (s + (k : Label P), tail F R α q ⟨j.val - k, by omega⟩) := by
  induction k with
  | zero => simp [Controller.run]
  | succ k ih =>
    have hk' : k ≤ j.val := by omega
    rw [run_add, ih hk']
    have hn : j.val - k ≠ 0 := by omega
    simp [Controller.run, Controller.next, Controller.step, controller, tail, hn,
      Nat.cast_add, add_assoc, Nat.sub_sub]

noncomputable def prefixAt (α : Assignment (e := e) F R) (t : Nat) : State F R α :=
  if ht : t < ell then prefixTag F R α ⟨t, ht⟩ else readState F R α (.inl ())

theorem prefix_run (α : Assignment (e := e) F R) (x : Label P)
    (t : Nat) (ht : t ≤ ell) :
    (controller F R α).run hP (x, (controller F R α).initial) t =
      (x + (t : Label P), prefixAt F R α t) := by
  induction t with
  | zero => simp [Controller.run, controller, initial, prefixAt]
  | succ t ih =>
    have hlt : t < ell := by omega
    rw [run_add, ih (by omega)]
    simp [Controller.run, Controller.next, Controller.step, prefixAt, hlt,
      controller, prefixTag, Nat.cast_add, add_assoc]

theorem support_digit {n : Node} {x : Label P} (hx : x ∈ F.support n) :
    digit hP (x + (F.shift n : Label P)) = F.color n := by
  have bounds := (F.interval n x).mp hx
  have upper := (F.interval_bounds n).2
  apply Fin.ext
  change (x + (F.shift n : Label P)).val / P = (F.color n).val
  apply Nat.div_eq_of_lt_le
  · omega
  · have hl : (F.color n).val * P + F.upper n ≤ ((F.color n).val + 1) * P := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    exact lt_of_lt_of_le bounds.2 hl

/-- Absolute event times count the preceding waits and reads. -/
def readTime (n : Node) : Nat := F.shift n + F.level n

def stopTime (x : Label P) : Nat := readTime F (F.event x (F.reads x - 1)) + 1

theorem event_time_step (x : Label P) (i : Nat) (hi : i + 1 < F.reads x) :
    readTime F (F.event x (i + 1)) =
      readTime F (F.event x i) + 1 + F.delay (F.event x i) := by
  have hp := F.successor x i hi
  simp only [readTime, F.child_shift _ _ hp, F.child_level _ _ hp]
  omega

private theorem read_step (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) {n : Node} {x : Label P} (hx : x ∈ F.support n) :
    (controller F R α).next hP
      (x + (F.shift n : Label P), readState F R α (placement F R α n).1) =
    (x + (F.shift n : Label P), requestState F R α n) := by
  have hd := support_digit F hx
  have row : ((placement F R α n).1, F.color n) = placement F R α n := by
    cases hp : F.parent n <;> simp [placement, hp]
  simp only [Controller.next, Controller.step, controller, readState, hd, Option.getD_some]
  rw [row, read_row_at F R hc α]

/-- Every original indexed read is reached at its exact original phase and
absolute deadline, by induction on that input's finite physical history. -/
theorem physical_event_run (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) (x : Label P) (i : Nat) (hi : i < F.reads x) :
    (controller F R α).run hP (x, (controller F R α).initial)
      (readTime F (F.event x i)) =
    (x + (F.shift (F.event x i) : Label P),
      readState F R α (placement F R α (F.event x i)).1) := by
  induction i with
  | zero =>
    rw [F.first]
    simp only [readTime, F.root_shift, F.root_level, Nat.add_zero]
    have hp := prefix_run F R α x ell (le_refl ell)
    simpa [prefixAt, placement, F.root_parent] using hp
  | succ i ih =>
    have hp := F.successor x i hi
    have hn := child_internal F hp
    have pos := internal_positive F hn
    have hr := read_step F R hc α (F.event_support x i (by omega))
    have he := ih (by omega)
    rw [event_time_step F x i hi, run_add, run_add, he]
    change (controller F R α).run hP
      ((controller F R α).next hP
        (x + (F.shift (F.event x i) : Label P),
          readState F R α (placement F R α (F.event x i)).1))
      (F.delay (F.event x i)) = _
    rw [hr]
    simp only [requestState, dif_pos hn]
    have hw := waits_physical_execution (controller F R α) hP
      (tail_chain F R α (nextTarget F R α (F.event x i))
        (F.delay (F.event x i) - 1) (by have := request_bound F R α hn; omega))
      (x + (F.shift (F.event x i) : Label P))
    have eq : F.delay (F.event x i) - 1 + 1 = F.delay (F.event x i) := by omega
    rw [eq] at hw
    rw [hw]
    simp [placement, hp, F.child_shift _ _ hp, Nat.cast_add, add_assoc]

/-- The last original read immediately selects its fixed original H_x. -/
theorem physical_terminal_run (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) (x : Label P) :
    (controller F R α).run hP (x, (controller F R α).initial) (stopTime F x) =
    (x + (F.shift (F.event x (F.reads x - 1)) : Label P), terminal F R α x) := by
  have hi : F.reads x - 1 < F.reads x := by have := F.reads_pos x; omega
  have hr := physical_event_run F R hc α x _ hi
  have hn : ¬ F.Internal (F.event x (F.reads x - 1)) := by
    rintro ⟨m, hm⟩
    exact F.last x m (Finset.mem_filter.mp hm).2
  have hout := F.leaf_original _ x (F.event_support x _ hi) (F.last x)
  rw [stopTime, run_add, hr]
  simp only [Controller.run, Function.iterate_one]
  rw [read_step F R hc α (F.event_support x _ hi)]
  simp [requestState, hn, hout]

/-- Every unit wait of every original request retains its literal position. -/
theorem physical_wait_run (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) (x : Label P) (i k : Nat)
    (hi : i + 1 < F.reads x) (hk : k < F.delay (F.event x i)) :
    (controller F R α).run hP (x, (controller F R α).initial)
      (readTime F (F.event x i) + 1 + k) =
    (x + (F.shift (F.event x i) : Label P) + (k : Label P),
      tail F R α (nextTarget F R α (F.event x i))
        ⟨F.delay (F.event x i) - 1 - k, by
          have hn := child_internal F (F.successor x i hi)
          have := request_bound F R α hn; omega⟩) := by
  have hn := child_internal F (F.successor x i hi)
  rw [run_add, run_add, physical_event_run F R hc α x i (by omega)]
  simp only [Controller.run, Function.iterate_one]
  rw [read_step F R hc α (F.event_support x i (by omega))]
  simp only [requestState, dif_pos hn]
  exact tail_partial F R α _ _ _ k (by change k ≤ F.delay (F.event x i) - 1; omega)

theorem event_time_mono (x : Label P) {i j : Nat}
    (hij : i ≤ j) (hj : j < F.reads x) :
    readTime F (F.event x i) ≤ readTime F (F.event x j) := by
  induction j with
  | zero =>
    have he : i = 0 := by omega
    subst i
    exact le_refl _
  | succ j ih =>
    by_cases he : i = j + 1
    · rw [he]
    · have hle := ih (by omega) (by omega)
      rw [event_time_step F x j hj]
      omega

theorem event_time_zero (x : Label P) : readTime F (F.event x 0) = ell := by
  simp [F.first, readTime, F.root_shift, F.root_level]

private theorem positions (x : Label P) {t : Nat} (ht : ell ≤ t)
    (hstop : t < stopTime F x) :
    ∃ i, i < F.reads x ∧ (t = readTime F (F.event x i) ∨
      (i + 1 < F.reads x ∧ ∃ k, k < F.delay (F.event x i) ∧
        t = readTime F (F.event x i) + 1 + k)) := by
  let earlier := (Finset.range (F.reads x)).filter
    (fun i => readTime F (F.event x i) ≤ t)
  have nonempty : earlier.Nonempty := ⟨0, by
    simp only [earlier, Finset.mem_filter, Finset.mem_range, event_time_zero F x]
    exact ⟨F.reads_pos x, ht⟩⟩
  let i := earlier.max' nonempty
  have mem := Finset.max'_mem earlier nonempty
  have hi : i < F.reads x := (Finset.mem_filter.mp mem).1 |> Finset.mem_range.mp
  have htime : readTime F (F.event x i) ≤ t := (Finset.mem_filter.mp mem).2
  refine ⟨i, hi, ?_⟩
  by_cases he : t = readTime F (F.event x i)
  · exact Or.inl he
  have more : i + 1 < F.reads x := by
    by_contra hh
    have hl : i = F.reads x - 1 := by omega
    rw [hl] at htime he
    unfold stopTime at hstop
    omega
  have next : t < readTime F (F.event x (i + 1)) := by
    by_contra hh
    have hn : i + 1 ∈ earlier := by
      simp only [earlier, Finset.mem_filter, Finset.mem_range]
      exact ⟨more, by omega⟩
    have hm := Finset.le_max' earlier (i + 1) hn
    change i + 1 ≤ i at hm
    omega
  rw [event_time_step F x i more] at next
  exact Or.inr ⟨more, t - (readTime F (F.event x i) + 1), by omega, by omega⟩

theorem prefix_is_wait (α : Assignment (e := e) F R) (x : Label P)
    {t : Nat} (ht : t < ell) :
    IsWait (controller F R α)
      ((controller F R α).run hP (x, (controller F R α).initial) t).2 := by
  rw [prefix_run F R α x t (by omega)]
  simp only [prefixAt, dif_pos ht, prefixTag, controller, IsWait]
  exact ⟨_, rfl⟩

theorem event_is_read (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) (x : Label P) {i : Nat} (hi : i < F.reads x) :
    IsRead (controller F R α)
      ((controller F R α).run hP (x, (controller F R α).initial)
        (readTime F (F.event x i))).2 := by
  rw [physical_event_run F R hc α x i hi]
  exact ⟨_, rfl⟩

theorem event_is_wait (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) (x : Label P) {i k : Nat}
    (hi : i + 1 < F.reads x) (hk : k < F.delay (F.event x i)) :
    IsWait (controller F R α)
      ((controller F R α).run hP (x, (controller F R α).initial)
        (readTime F (F.event x i) + 1 + k)).2 := by
  rw [physical_wait_run F R hc α x i k hi hk]
  exact ⟨_, rfl⟩

private theorem wait_not_read {Q : Type u} (C : Controller P Q) {q : Q}
    (hw : IsWait C q) : ¬ IsRead C q := by
  rintro ⟨row, hr⟩
  obtain ⟨next, hn⟩ := hw
  rw [hn] at hr
  cases hr

private theorem live_instruction {Q : Type u} (C : Controller P Q) {q : Q}
    (hl : IsWait C q ∨ IsRead C q) (x : Label P) : C.instruction q ≠ .halt x := by
  intro he
  rcases hl with ⟨next, hn⟩ | ⟨row, hn⟩ <;> rw [he] at hn <;> cases hn

/-- The instruction facts of a faithful original finite word. This interface
is used for arbitrary nominal controllers only in the converse; construction
below proves all four fields from the original physical source. -/
structure OriginalWordData {Q : Type u} (C : Controller P Q) : Prop where
  prefix_wait : ∀ x t, t < ell →
    IsWait C (C.run hP (x, C.initial) t).2
  read_event : ∀ x i, i < F.reads x →
    IsRead C (C.run hP (x, C.initial) (readTime F (F.event x i))).2
  wait_event : ∀ x i k, i + 1 < F.reads x → k < F.delay (F.event x i) →
    IsWait C (C.run hP (x, C.initial) (readTime F (F.event x i) + 1 + k)).2
  final_halt : ∀ x, C.instruction (C.run hP (x, C.initial) (stopTime F x)).2 = .halt x

theorem original_reads_exact {Q : Type u} (C : Controller P Q)
    (O : OriginalWordData F C) (x : Label P) {t : Nat} (ht : t < stopTime F x) :
    IsRead C (C.run hP (x, C.initial) t).2 ↔
      ∃ i, i < F.reads x ∧ t = readTime F (F.event x i) := by
  constructor
  · intro hr
    by_cases hp : t < ell
    · exact False.elim (wait_not_read _ (O.prefix_wait x t hp) hr)
    obtain ⟨i, hi, he | ⟨more, k, hk, he⟩⟩ := positions F x (by omega) ht
    · exact ⟨i, hi, he⟩
    · rw [he] at hr
      exact False.elim (wait_not_read _ (O.wait_event x i k more hk) hr)
  · rintro ⟨i, hi, rfl⟩
    exact O.read_event x i hi

/-- Reconstruct U1 Initialized from the original all-input word and fixed
labels, without assuming an Initialized witness or any capacity bound. -/
noncomputable def initialize_original_paths {Q : Type u} (C : Controller P Q)
    (O : OriginalWordData F C) : Initialized C hP ell h where
  length := stopTime F
  finite x := by
    constructor
    · exact O.final_halt x
    · intro t ht z
      by_cases hp : t < ell
      · exact live_instruction _ (Or.inl (O.prefix_wait x t hp)) z
      obtain ⟨i, hi, he | ⟨more, k, hk, he⟩⟩ := positions F x (by omega) ht
      · rw [he]; exact live_instruction _ (Or.inr (O.read_event x i hi)) z
      · rw [he]; exact live_instruction _ (Or.inl (O.wait_event x i k more hk)) z
  shape x := by
    have hl : F.reads x - 1 < F.reads x := by have := F.reads_pos x; omega
    have hfirst : ell < stopTime F x := by
      have hm := event_time_mono F x (i := 0) (j := F.reads x - 1) (by omega) hl
      rw [event_time_zero F x] at hm
      unfold stopTime; omega
    constructor
    · exact hfirst
    · intro t ht; exact O.prefix_wait x t ht
    · simpa only [event_time_zero F x] using
        O.read_event x 0 (F.reads_pos x)
    · intro t ht hr
      obtain ⟨i, hi, he⟩ := (original_reads_exact F C O x (by omega)).mp hr
      have more : i + 1 < F.reads x := by
        by_contra hh
        have hl' : i = F.reads x - 1 := by omega
        rw [he, hl'] at ht
        unfold stopTime at ht
        omega
      have hd := internal_positive F (child_internal F (F.successor x i more))
      rw [he]
      simpa using O.wait_event x i 0 more hd
    · unfold stopTime
      simp only [Nat.add_sub_cancel]
      exact O.read_event x (F.reads x - 1) hl
    · let times := (Finset.range (F.reads x)).image (fun i => readTime F (F.event x i))
      have sub : ((Finset.range (stopTime F x)).filter (fun t =>
          IsRead C
            (C.run hP (x, C.initial) t).2)) ⊆ times := by
        intro t ht
        obtain ⟨i, hi, he⟩ := (original_reads_exact F C O x
          (Finset.mem_range.mp (Finset.mem_filter.mp ht).1)).mp (Finset.mem_filter.mp ht).2
        exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, he.symm⟩
      exact le_trans (Finset.card_le_card sub)
        (le_trans (Finset.card_image_le) (by simpa using F.reads_bound x))



end D5.S3.ObserverMemory.Algorithms.FixedForestUnitCapacity
