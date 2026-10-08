/- GID: D5/S3/ObserverMemory/Algorithms/SaturatedActualHistories
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/SaturatedActualHistories
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Read budgets and saturated supports construct complete actual binary histories. -/

import D5.S3.ObserverMemory.Algorithms.SaturatedSlotUnfolding
import D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories

open ActualControlSlots SaturatedSlotUnfolding
open D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound
open scoped BigOperators

variable {p P : Nat} {Q : Type}
variable (hp : 2 ≤ p) (hP : 0 < P) (C : Controller p P Q)
variable (I : C.Correct hp hP)

attribute [local instance] Classical.propDecidable
local notation "Source" => ZMod (p * P)
local notation "Slot" => {q : Q // ∃ b, C.Used I q b} × Fin p

/-- The later reads on the original physical trajectory. -/
noncomputable def laterReads (x : Source) (t : Nat) : Finset Nat :=
  (Finset.range (I.length x)).filter
    (fun k => t < k ∧ C.action (C.run hp hP x k).2 = .read)

/-- An actual binary history with a remaining read budget. Empty branches
and early terminal leaves are allowed until saturation is established. -/
private inductive ActualHistoryTree : Nat → Slot → Finset Source → (Source → Nat) → Type where
  | empty {n : Nat} {u : Slot} {a : Source → Nat} : ActualHistoryTree n u ∅ a
  | leaf {n : Nat} {a : Source → Nat} (u : Slot) (x : Source)
      (occurs : C.Occurs I x (a x) u) (last : a x + 1 = I.length x) :
      ActualHistoryTree n u {x} a
  | fork {n : Nat} {u v w : Slot} {S T : Finset Source} {a b c : Source → Nat}
      (different : S.Nonempty → T.Nonempty → v ≠ w) (separate : Disjoint S T)
      (left : ActualHistoryTree n v S b) (right : ActualHistoryTree n w T c)
      (parent : ∀ x ∈ S ∪ T, C.Occurs I x (a x) u)
      (left_next : ∀ x ∈ S, a x < b x ∧
        ∀ t, a x < t → t < b x → C.action (C.run hp hP x t).2 = .wait)
      (right_next : ∀ x ∈ T, a x < c x ∧
        ∀ t, a x < t → t < c x → C.action (C.run hp hP x t).2 = .wait) :
      ActualHistoryTree (n + 1) u (S ∪ T) a

private noncomputable def skeleton {n : Nat} {u : Slot} {S : Finset Source} {a : Source → Nat}
    (H : ActualHistoryTree hp hP C I n u S a) : AdaptiveProtocol Source 2 n := by
  induction H with
  | empty => exact .leaf
  | leaf => exact .leaf
  | @fork n u v w S T a b c different separate left right parent ln rn ihl ihr =>
    exact .query (fun x => if x ∈ S then 0 else 1)
      (fun b => if b = 0 then ihl else ihr)

private theorem query_leaf_card {n : Nat} (question : Source → Fin 2)
    (left right : AdaptiveProtocol Source 2 n) :
    (adaptiveLeaves (.query question (fun b => if b = 0 then left else right))).card =
      (adaptiveLeaves left).card + (adaptiveLeaves right).card := by
  classical
  rw [adaptiveLeaves, Finset.card_biUnion]
  · simp only [Finset.card_image_of_injective _ List.cons_injective]
    simp [Fin.sum_univ_two]
  · intro b hb c hc ne
    apply Finset.disjoint_left.mpr
    intro word hw hv
    obtain ⟨v, _, eq⟩ := Finset.mem_image.mp hw
    obtain ⟨w, _, eq'⟩ := Finset.mem_image.mp hv
    exact ne (List.cons.inj (eq.trans eq'.symm)).1

private theorem tree_card_bound {n : Nat} {u : Slot} {S : Finset Source}
    {a : Source → Nat} (H : ActualHistoryTree hp hP C I n u S a) : S.card ≤ 2 ^ n := by
  have lower : S.card ≤ (adaptiveLeaves (skeleton hp hP C I H)).card := by
    induction H with
    | empty => simp
    | leaf => simp [skeleton, adaptiveLeaves]
    | fork different separate left right parent ln rn ihl ihr =>
      rw [Finset.card_union_of_disjoint separate]
      simpa only [skeleton, query_leaf_card] using Nat.add_le_add ihl ihr
  exact lower.trans (adaptive_leaf_count_le_pow _ (by decide))

private theorem saturated_tree {n : Nat} {u : Slot} {S : Finset Source}
    {a : Source → Nat} (H : ActualHistoryTree hp hP C I n u S a)
    (full : S.card = 2 ^ n) : Nonempty (SaturatedHistory hp hP C I n u S a) := by
  induction H with
  | @empty n u a =>
    have positive : 0 < 2 ^ n := by positivity
    simp only [Finset.card_empty] at full
    omega
  | @leaf n a u x occurs last =>
    have one : 1 = 2 ^ n := by simpa using full
    have zero : n = 0 := by simpa using one.symm
    subst n
    exact ⟨.leaf u x occurs last⟩
  | @fork n u v w S T a b c different separate left right parent ln rn ihl ihr =>
    have lb := tree_card_bound hp hP C I left
    have rb := tree_card_bound hp hP C I right
    rw [Finset.card_union_of_disjoint separate, pow_succ] at full
    have ls : S.card = 2 ^ n := by omega
    have rs : T.card = 2 ^ n := by omega
    have sn : S.Nonempty := Finset.card_pos.mp (ls ▸ (by positivity))
    have tn : T.Nonempty := Finset.card_pos.mp (rs ▸ (by positivity))
    obtain ⟨L⟩ := ihl ls
    obtain ⟨R⟩ := ihr rs
    exact ⟨.fork (different sn tn) separate L R parent ln rn⟩

private theorem terminal {x : Source} {t : Nat} {u : Slot}
    (h : C.Occurs I x t u) (halt : C.action (C.readNext u.1.val u.2) = .halt) :
    t + 1 = I.length x ∧ C.output (C.readNext u.1.val u.2) = x := by
  have st := occurrence_advance hp hP C I h
  have live := I.live x
  have last : t + 1 = I.length x := by
    have before := h.1
    by_contra ne
    exact live (t + 1) (by omega) (st ▸ halt)
  refine ⟨last, ?_⟩
  rw [← st, last]
  exact I.output x

private theorem next_event {x : Source} {t : Nat} {u : Slot}
    (h : C.Occurs I x t u) (active : C.action (C.readNext u.1.val u.2) ≠ .halt) :
    ∃ k v, C.Occurs I x k v ∧ t < k ∧
      (∀ i, t < i → i < k → C.action (C.run hp hP x i).2 = .wait) ∧
      (laterReads hp hP C I x k).card + 1 = (laterReads hp hP C I x t).card := by
  classical
  have before := h.1
  have st := occurrence_advance hp hP C I h
  have notlast : t + 1 < I.length x := by
    by_contra bad
    have eq : t + 1 = I.length x := by omega
    exact active (by rw [← st, eq]; exact I.halt x)
  have memlast : I.length x - 1 ∈ laterReads hp hP C I x t := by
    simp only [laterReads, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by omega, I.last_read x⟩
  let A := laterReads hp hP C I x t
  have ne : A.Nonempty := ⟨_, memlast⟩
  let k := A.min' ne
  have hk := Finset.min'_mem A ne
  obtain ⟨kl, tk, kr⟩ := Finset.mem_filter.mp hk
  have kl' : k < I.length x := Finset.mem_range.mp kl
  let v : Slot := (⟨(C.run hp hP x k).2,
    ⟨digit hp hP (C.run hp hP x k).1, x, k, kl', rfl, kr, rfl⟩⟩,
    digit hp hP (C.run hp hP x k).1)
  have minimum : ∀ i ∈ A, k ≤ i := fun i hi => Finset.min'_le A i hi
  have waits (i : Nat) (ti : t < i) (ik : i < k) :
      C.action (C.run hp hP x i).2 = .wait := by
    have notread : C.action (C.run hp hP x i).2 ≠ .read := by
      have absent : i ∉ A := Finset.notMem_of_lt_min ik (Finset.coe_min' ne).symm
      simpa only [A, laterReads, Finset.mem_filter, Finset.mem_range,
        show i < I.length x by omega, ti, true_and] using absent
    cases ha : C.action (C.run hp hP x i).2 with
    | wait => rfl
    | read => exact False.elim (notread ha)
    | halt => exact False.elim (I.live x i (by omega) ha)
  have split : A = insert k (laterReads hp hP C I x k) := by
    ext i
    constructor
    · intro hi
      have le := minimum i hi
      by_cases eq : i = k
      · exact Finset.mem_insert.mpr (Or.inl eq)
      · apply Finset.mem_insert.mpr
        right
        obtain ⟨ir, it, read⟩ := Finset.mem_filter.mp hi
        simp only [laterReads, Finset.mem_filter]
        exact ⟨ir, by omega, read⟩
    · intro hi
      rcases Finset.mem_insert.mp hi with eq | hi
      · exact eq ▸ hk
      · obtain ⟨ir, ki, read⟩ := Finset.mem_filter.mp hi
        simp only [A, laterReads, Finset.mem_filter]
        exact ⟨ir, by omega, read⟩
  have nk : k ∉ laterReads hp hP C I x k := by simp [laterReads]
  refine ⟨k, v, ⟨kl', rfl, rfl⟩, tk, waits, ?_⟩
  change _ = A.card
  rw [split, Finset.card_insert_of_notMem nk]

private theorem terminal_tree {n : Nat} {u : Slot} {S : Finset Source}
    {a : Source → Nat} (realized : ∀ x ∈ S, C.Occurs I x (a x) u)
    (halt : C.action (C.readNext u.1.val u.2) = .halt) :
    Nonempty (ActualHistoryTree hp hP C I n u S a) := by
  classical
  by_cases empty : S = ∅
  · subst S
    exact ⟨.empty⟩
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  have singleton : S = {x} := by
    ext y
    simp only [Finset.mem_singleton]
    constructor
    · intro hy
      exact (terminal hp hP C I (realized y hy) halt).2.symm.trans
        (terminal hp hP C I (realized x hx) halt).2
    · intro eq
      exact eq ▸ hx
  rw [singleton]
  exact ⟨.leaf u x (realized x hx) (terminal hp hP C I (realized x hx) halt).1⟩

private theorem tree_exists [Finite Q] {n : Nat} {u : Slot} {S : Finset Source}
    {a : Source → Nat} (realized : ∀ x ∈ S, C.Occurs I x (a x) u)
    (budget : ∀ x ∈ S, (laterReads hp hP C I x (a x)).card ≤ n) :
    Nonempty (ActualHistoryTree hp hP C I n u S a) := by
  classical
  induction n generalizing u S a with
  | zero =>
    by_cases empty : S = ∅
    · subst S
      exact ⟨.empty⟩
    by_cases halt : C.action (C.readNext u.1.val u.2) = .halt
    · exact terminal_tree hp hP C I realized halt
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    obtain ⟨t, v, occurs, before, waits, count⟩ :=
      next_event hp hP C I (realized x hx) halt
    have bound := budget x hx
    omega
  | succ n ih =>
    by_cases empty : S = ∅
    · subst S
      exact ⟨.empty⟩
    by_cases halt : C.action (C.readNext u.1.val u.2) = .halt
    · exact terminal_tree hp hP C I realized halt
    let E (x : Source) (hx : x ∈ S) := next_event hp hP C I (realized x hx) halt
    let time (x : Source) := if hx : x ∈ S then (E x hx).choose else 0
    let dest (x : Source) : Slot :=
      if hx : x ∈ S then (E x hx).choose_spec.choose else u
    have event (x : Source) (hx : x ∈ S) :
        C.Occurs I x (time x) (dest x) ∧ a x < time x ∧
        (∀ i, a x < i → i < time x → C.action (C.run hp hP x i).2 = .wait) ∧
        (laterReads hp hP C I x (time x)).card + 1 =
          (laterReads hp hP C I x (a x)).card := by
      simpa only [time, dest, dif_pos hx] using (E x hx).choose_spec.choose_spec
    have edge (x : Source) (hx : x ∈ S) : C.Edge I u (dest x) :=
      ⟨x, a x, time x, realized x hx, (event x hx).1,
        (event x hx).2.1, (event x hx).2.2.1⟩
    let _ := Fintype.ofFinite Q
    obtain ⟨G, root, used, edges, adjacent, rest⟩ := C.result I
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    obtain ⟨q, b, c, cover, neighbor⟩ := adjacent u
      ⟨dest x, (edges u (dest x)).mpr (edge x hx)⟩
    let v : Slot := (q, b)
    let w : Slot := (q, c)
    have covered (x : Source) (hx : x ∈ S) : dest x = v ∨ dest x = w := by
      have mem := cover ((edges u (dest x)).mpr (edge x hx))
      simpa only [Finset.mem_insert, Finset.mem_singleton, v, w] using mem
    let L := S.filter (fun x => dest x = v)
    let R := S.filter (fun x => dest x ≠ v)
    have partition : L ∪ R = S := Finset.filter_union_filter_not_eq _ _
    have disjoint : Disjoint L R := Finset.disjoint_filter_filter_not _ _ _
    have left_event (x : Source) (hx : x ∈ L) : C.Occurs I x (time x) v := by
      have hs := (Finset.mem_filter.mp hx).1
      have eq := (Finset.mem_filter.mp hx).2
      exact eq ▸ (event x hs).1
    have right_dest (x : Source) (hx : x ∈ R) : dest x = w := by
      have hs := (Finset.mem_filter.mp hx).1
      exact (covered x hs).resolve_left (Finset.mem_filter.mp hx).2
    have right_event (x : Source) (hx : x ∈ R) : C.Occurs I x (time x) w :=
      right_dest x hx ▸ (event x (Finset.mem_filter.mp hx).1).1
    have left_budget (x : Source) (hx : x ∈ L) :
        (laterReads hp hP C I x (time x)).card ≤ n := by
      have hs := (Finset.mem_filter.mp hx).1
      have old := budget x hs
      have count := (event x hs).2.2.2
      omega
    have right_budget (x : Source) (hx : x ∈ R) :
        (laterReads hp hP C I x (time x)).card ≤ n := by
      have hs := (Finset.mem_filter.mp hx).1
      have old := budget x hs
      have count := (event x hs).2.2.2
      omega
    obtain ⟨left⟩ := ih left_event left_budget
    obtain ⟨right⟩ := ih right_event right_budget
    have different : L.Nonempty → R.Nonempty → v ≠ w := by
      intro hl hr eq
      obtain ⟨y, hy⟩ := hr
      exact (Finset.mem_filter.mp hy).2 ((right_dest y hy).trans eq.symm)
    have parent : ∀ x ∈ L ∪ R, C.Occurs I x (a x) u := by
      simpa only [partition] using realized
    have ln : ∀ x ∈ L, a x < time x ∧
        ∀ t, a x < t → t < time x → C.action (C.run hp hP x t).2 = .wait := by
      intro x hx
      have e := event x (Finset.mem_filter.mp hx).1
      exact ⟨e.2.1, e.2.2.1⟩
    have rn : ∀ x ∈ R, a x < time x ∧
        ∀ t, a x < t → t < time x → C.action (C.run hp hP x t).2 = .wait := by
      intro x hx
      have e := event x (Finset.mem_filter.mp hx).1
      exact ⟨e.2.1, e.2.2.1⟩
    rw [← partition]
    exact ⟨.fork different disjoint left right parent ln rn⟩

/-- Saturation of the physical original-input support produces a complete
actual binary expansion with the original support and event times. -/
private theorem saturated_support [Finite Q] {n : Nat} {u : Slot} {S : Finset Source}
    {a : Source → Nat} (realized : ∀ x ∈ S, C.Occurs I x (a x) u)
    (budget : ∀ x ∈ S, (laterReads hp hP C I x (a x)).card ≤ n)
    (full : S.card = 2 ^ n) :
    Nonempty (SaturatedHistory hp hP C I n u S a) := by
  obtain ⟨tree⟩ := tree_exists hp hP C I realized budget
  exact saturated_tree hp hP C I tree full

private theorem later_read_step {x : Source} {t k : Nat} {u v : Slot}
    (_ht : C.Occurs I x t u) (hk : C.Occurs I x k v) (tk : t < k)
    (waits : ∀ i, t < i → i < k → C.action (C.run hp hP x i).2 = .wait) :
    (laterReads hp hP C I x t).card = (laterReads hp hP C I x k).card + 1 := by
  classical
  obtain ⟨d, y, j, hj, hq, read, hd⟩ := v.1.property
  have kr : C.action (C.run hp hP x k).2 = .read := hk.2.1 ▸ read
  have split : laterReads hp hP C I x t = insert k (laterReads hp hP C I x k) := by
    ext i
    simp only [laterReads, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    constructor
    · rintro ⟨il, ti, ir⟩
      by_cases eq : i = k
      · exact Or.inl eq
      · right
        refine ⟨il, ?_, ir⟩
        by_contra bad
        have clash := waits i ti (by omega)
        rw [ir] at clash
        cases clash
    · rintro (eq | ⟨il, ki, ir⟩)
      · subst i
        exact ⟨hk.1, tk, kr⟩
      · exact ⟨il, by omega, ir⟩
  rw [split, Finset.card_insert_of_notMem (by simp [laterReads])]

private theorem saturated_read_count {n : Nat} {u : Slot} {S : Finset Source}
    {a : Source → Nat} (H : SaturatedHistory hp hP C I n u S a) :
    ∀ x ∈ S, (laterReads hp hP C I x (a x)).card = n := by
  induction H with
  | @leaf a u x occurs last =>
    intro y hy
    have eq : y = x := Finset.mem_singleton.mp hy
    subst y
    have empty : laterReads hp hP C I x (a x) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨hl, ha, hr⟩ := Finset.mem_filter.mp ht
      have before := Finset.mem_range.mp hl
      omega
    simp [empty]
  | @fork n u v w S T a b c different separate left right parent ln rn ihl ihr =>
    intro x hx
    rcases Finset.mem_union.mp hx with hs | ht
    · have step := later_read_step hp hP C I
        (parent x (Finset.mem_union_left T hs)) ((history_data hp hP C I left).2.2 x hs)
      have next := ln x hs
      rw [step next.1 next.2, ihl x hs]
    · have step := later_read_step hp hP C I
        (parent x (Finset.mem_union_right S ht)) ((history_data hp hP C I right).2.2 x ht)
      have next := rn x ht
      rw [step next.1 next.2, ihr x ht]

/-- Actual read-event times, including the first read. -/
noncomputable def readEvents (x : Source) : Finset Nat :=
  (Finset.range (I.length x)).filter (fun t => C.action (C.run hp hP x t).2 = .read)

private theorem first_read_count (x : Source) :
    (readEvents hp hP C I x).card = (laterReads hp hP C I x 0).card + 1 := by
  classical
  have positive : 0 < I.length x := by
    apply Nat.pos_of_ne_zero
    intro zero
    simpa [Controller.run, zero, I.first_read] using I.halt x
  have split : readEvents hp hP C I x = insert 0 (laterReads hp hP C I x 0) := by
    ext t
    simp only [readEvents, laterReads, Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
    by_cases zero : t = 0
    · subst t
      simp [positive, Controller.run, I.first_read]
    · simp only [zero, false_or]
      exact ⟨fun h => ⟨h.1, by omega, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [split, Finset.card_insert_of_notMem (by simp [laterReads])]

/-- The first-read fiber consists of original physical inputs, not an
extra digit register in the controller. -/
noncomputable def firstFiber (b : Fin p) : Finset Source := by
  letI : NeZero (p * P) := ⟨by positivity⟩
  exact Finset.univ.filter (fun x => digit hp hP x = b)

private theorem fin_equiv_val (m : Nat) [NeZero m] (x : Fin m) :
    (ZMod.finEquiv m x).val = x.val := by
  cases m with
  | zero => exact Fin.elim0 x
  | succ m => rfl

private theorem first_fiber_card (b : Fin p) : (firstFiber hp hP b).card = P := by
  classical
  have : NeZero (p * P) := ⟨by positivity⟩
  let e : Fin p × Fin P ≃ Source := finProdFinEquiv.trans (ZMod.finEquiv (p * P)).toEquiv
  have digits (z : Fin p × Fin P) : digit hp hP (e z) = z.1 := by
    apply Fin.ext
    change (e z).val / P = z.1.val
    simp only [e, Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
      fin_equiv_val]
    change (z.2.val + P * z.1.val) / P = z.1.val
    rw [Nat.add_mul_div_left _ _ hP, Nat.div_eq_of_lt z.2.isLt, Nat.zero_add]
  let f : Fin P → {x : Source // x ∈ firstFiber hp hP b} := fun v =>
    ⟨e (b,v), by simp [firstFiber, digits]⟩
  have inj : Function.Injective f := by
    intro v w eq
    exact (Prod.mk.inj (e.injective (congrArg Subtype.val eq))).2
  have surj : Function.Surjective f := by
    intro x
    let z := e.symm x.val
    have first : z.1 = b := by
      rw [← digits z, Equiv.apply_symm_apply]
      simpa only [firstFiber, Finset.mem_filter, Finset.mem_univ, true_and] using x.property
    refine ⟨z.2, Subtype.ext ?_⟩
    change e (b, z.2) = x.val
    have pair : (b, z.2) = z := Prod.ext first.symm rfl
    exact (congrArg e pair).trans (e.apply_symm_apply x.val)
  have card := Fintype.card_congr (Equiv.ofBijective f ⟨inj, surj⟩)
  simpa using card.symm


local notation "Entry" => Σ n : Nat, Σ u : Slot, Σ S : Finset Source,
  Σ a : Source → Nat, SaturatedHistory hp hP C I n u S a
local notation "entrySlot" => (fun e : Entry => Sigma.fst (Sigma.snd e))
local notation "entrySupport" => (fun e : Entry => Sigma.fst (Sigma.snd (Sigma.snd e)))
local notation "entryTime" => (fun e : Entry =>
  Sigma.fst (Sigma.snd (Sigma.snd (Sigma.snd e))))
local notation "entryTree" => (fun e : Entry =>
  Sigma.snd (Sigma.snd (Sigma.snd (Sigma.snd e))))

/-- The nonempty post-read histories in a complete actual tree, including
its root and terminal histories. Their order is depth-first. -/
noncomputable def historyEntries {n : Nat} {u : Slot} {S : Finset Source}
    {a : Source → Nat} (H : SaturatedHistory hp hP C I n u S a) : List Entry := by
  induction H with
  | @leaf a u x occurs last => exact [⟨0, u, {x}, a, .leaf u x occurs last⟩]
  | @fork n u v w S T a b c different separate left right parent ln rn ihl ihr =>
    exact ⟨n+1, u, S∪T, a, .fork different separate left right parent ln rn⟩ :: (ihl ++ ihr)

private theorem entry_support {n : Nat} {u : Slot} {S : Finset Source}
    {a : Source → Nat} (H : SaturatedHistory hp hP C I n u S a) :
    ∀ e ∈ historyEntries hp hP C I H, e.1 ≤ n ∧ entrySupport e ⊆ S := by
  induction H with
  | leaf =>
    intro e he
    simp only [historyEntries, List.mem_singleton] at he
    subst e
    exact ⟨le_rfl, Finset.Subset.refl _⟩
  | @fork n u v w S T a b c different separate left right parent ln rn ihl ihr =>
    intro e he
    simp only [historyEntries, List.mem_cons, List.mem_append] at he
    rcases he with eq | he | he
    · subst e
      exact ⟨le_rfl, Finset.Subset.refl _⟩
    · exact ⟨(ihl e he).1.trans (by omega),
        (ihl e he).2.trans Finset.subset_union_left⟩
    · exact ⟨(ihr e he).1.trans (by omega),
        (ihr e he).2.trans Finset.subset_union_right⟩

private theorem entry_lists_disjoint [Finite Q] {n k : Nat} {u v : Slot}
    {S T : Finset Source} {a b : Source → Nat}
    (H : SaturatedHistory hp hP C I n u S a)
    (K : SaturatedHistory hp hP C I k v T b) (separate : Disjoint S T) :
    List.Disjoint ((historyEntries hp hP C I H).map entrySlot)
      ((historyEntries hp hP C I K).map entrySlot) := by
  apply List.disjoint_left.mpr
  intro slot hs ht
  obtain ⟨e, he, es⟩ := List.mem_map.mp hs
  obtain ⟨f, hf, fs⟩ := List.mem_map.mp ht
  have same := (SaturatedSlotUnfolding.result hp hP C I (entryTree e) (entryTree f)).2.2
    (es.trans fs.symm)
  obtain ⟨x, hx⟩ := (history_data hp hP C I (entryTree e)).2.1
  have hy : x ∈ entrySupport f := by
    change x ∈ f.2.2.1
    rw [← same.2]
    exact hx
  exact Finset.disjoint_left.mp separate ((entry_support hp hP C I H e he).2 hx)
    ((entry_support hp hP C I K f hf).2 hy)

private theorem entry_slots_nodup [Finite Q] {n : Nat} {u : Slot} {S : Finset Source}
    {a : Source → Nat} (H : SaturatedHistory hp hP C I n u S a) :
    ((historyEntries hp hP C I H).map entrySlot).Nodup := by
  induction H with
  | leaf => simp [historyEntries]
  | @fork n u v w S T a b c different separate left right parent ln rn ihl ihr =>
    simp only [historyEntries, List.map_cons, List.map_append]
    apply List.nodup_cons.mpr
    constructor
    · intro mem
      rcases List.mem_append.mp mem with hl | hr
      · obtain ⟨e, he, eq⟩ := List.mem_map.mp hl
        have same := (SaturatedSlotUnfolding.result hp hP C I
          (.fork different separate left right parent ln rn) (entryTree e)).2.2 eq.symm
        have bound := (entry_support hp hP C I left e he).1
        omega
      · obtain ⟨e, he, eq⟩ := List.mem_map.mp hr
        have same := (SaturatedSlotUnfolding.result hp hP C I
          (.fork different separate left right parent ln rn) (entryTree e)).2.2 eq.symm
        have bound := (entry_support hp hP C I right e he).1
        omega
    · exact List.nodup_append'.mpr
        ⟨ihl, ihr, entry_lists_disjoint hp hP C I left right separate⟩

private theorem entry_event_cover {n : Nat} {u : Slot} {S : Finset Source}
    {a : Source → Nat} (H : SaturatedHistory hp hP C I n u S a) :
    ∀ x ∈ S, ∀ t, a x ≤ t → t ∈ readEvents hp hP C I x →
      ∃ e ∈ historyEntries hp hP C I H, x ∈ entrySupport e ∧ entryTime e x = t := by
  induction H with
  | @leaf a u x occurs last =>
    intro y hy t after ht
    have eq : y = x := Finset.mem_singleton.mp hy
    subst y
    have before := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
    have time : a x = t := by omega
    exact ⟨⟨0, u, {x}, a, .leaf u x occurs last⟩,
      by simp [historyEntries], by simp, time⟩
  | @fork n u v w S T a b c different separate left right parent ln rn ihl ihr =>
    intro x hx t after ht
    by_cases eq : a x = t
    · exact ⟨⟨n+1, u, S∪T, a, .fork different separate left right parent ln rn⟩,
        by simp [historyEntries], hx, eq⟩
    have strict : a x < t := by omega
    have read := (Finset.mem_filter.mp ht).2
    rcases Finset.mem_union.mp hx with hs | hr
    · have child_before : b x ≤ t := by
        by_contra bad
        have clash := (ln x hs).2 t strict (by omega)
        rw [read] at clash
        cases clash
      obtain ⟨e, he, xe, time⟩ := ihl x hs t child_before ht
      exact ⟨e, List.mem_cons_of_mem _ (List.mem_append_left _ he), xe, time⟩
    · have child_before : c x ≤ t := by
        by_contra bad
        have clash := (rn x hr).2 t strict (by omega)
        rw [read] at clash
        cases clash
      obtain ⟨e, he, xe, time⟩ := ihr x hr t child_before ht
      exact ⟨e, List.mem_cons_of_mem _ (List.mem_append_right _ he), xe, time⟩

/-- All actual nonempty histories in the first-read forest, with original
supports and physical event times retained in each entry. -/
noncomputable def allHistories {D : Nat} {root : {q : Q // ∃ b, C.Used I q b}}
    (H : ∀ b : Fin p, SaturatedHistory hp hP C I D (root,b)
      (firstFiber hp hP b) (fun _ => 0)) : List Entry :=
  (List.ofFn (fun b => historyEntries hp hP C I (H b))).flatten

private theorem all_slots_nodup [Finite Q] {D : Nat}
    {root : {q : Q // ∃ b, C.Used I q b}}
    (H : ∀ b : Fin p, SaturatedHistory hp hP C I D (root,b)
      (firstFiber hp hP b) (fun _ => 0)) :
    ((allHistories hp hP C I H).map entrySlot).Nodup := by
  rw [allHistories, List.map_flatten, List.map_ofFn]
  apply List.nodup_flatten.mpr
  constructor
  · intro l hl
    obtain ⟨b, rfl⟩ := List.mem_ofFn.mp hl
    exact entry_slots_nodup hp hP C I (H b)
  · apply List.pairwise_ofFn.mpr
    intro b c bc
    apply entry_lists_disjoint hp hP C I (H b) (H c)
    apply Finset.disjoint_left.mpr
    intro x hb hc
    have xb : digit hp hP x = b := by simpa [firstFiber] using hb
    have xc : digit hp hP x = c := by simpa [firstFiber] using hc
    exact (ne_of_lt bc) (xb.symm.trans xc)

private theorem all_event_cover {D : Nat}
    {root : {q : Q // ∃ b, C.Used I q b}}
    (H : ∀ b : Fin p, SaturatedHistory hp hP C I D (root,b)
      (firstFiber hp hP b) (fun _ => 0)) :
    ∀ x t, t ∈ readEvents hp hP C I x →
      ∃ e ∈ allHistories hp hP C I H, x ∈ entrySupport e ∧ entryTime e x = t := by
  intro x t ht
  have hx : x ∈ firstFiber hp hP (digit hp hP x) := by simp [firstFiber]
  obtain ⟨e, he, xe, time⟩ := entry_event_cover hp hP C I (H (digit hp hP x)) x hx t
    (Nat.zero_le _) ht
  refine ⟨e, ?_, xe, time⟩
  exact List.mem_flatten.mpr ⟨historyEntries hp hP C I (H (digit hp hP x)),
    List.mem_ofFn.mpr ⟨digit hp hP x, rfl⟩, he⟩


/-- Each internal post-read history has one subsequent reading occurrence,
with its two distinct actual answer slots. -/
noncomputable def readingPositions {n : Nat} {u : Slot} {S : Finset Source}
    {a : Source → Nat} (H : SaturatedHistory hp hP C I n u S a) : List (Slot × Slot) := by
  induction H with
  | leaf => exact []
  | @fork n u v w S T a b c different separate left right parent ln rn ihl ihr =>
    exact (v,w) :: (ihl ++ ihr)

private theorem position_slots_perm {n : Nat} {u : Slot} {S : Finset Source}
    {a : Source → Nat} (H : SaturatedHistory hp hP C I n u S a) :
    (u :: (readingPositions hp hP C I H).flatMap (fun z => [z.1,z.2])).Perm
      ((historyEntries hp hP C I H).map entrySlot) := by
  induction H with
  | leaf => simp [readingPositions, historyEntries]
  | @fork n u v w S T a b c different separate left right parent ln rn ihl ihr =>
    simp only [readingPositions, historyEntries, List.flatMap_cons, List.flatMap_append,
      List.map_cons, List.map_append]
    let L := (readingPositions hp hP C I left).flatMap (fun z => [z.1,z.2])
    let R := (readingPositions hp hP C I right).flatMap (fun z => [z.1,z.2])
    have shuffle : (v :: w :: (L ++ R)).Perm ((v :: L) ++ (w :: R)) := by
      simpa only [List.singleton_append, List.cons_append, List.append_assoc, List.nil_append] using
        ((List.perm_append_comm (l₁ := [w]) (l₂ := L)).append_right R).cons v
    exact (shuffle.trans (ihl.append ihr)).cons u

private theorem position_controls [Finite Q] {n : Nat} {u : Slot} {S : Finset Source}
    {a : Source → Nat} (H : SaturatedHistory hp hP C I n u S a) :
    ∀ z ∈ readingPositions hp hP C I H, z.1.1 = z.2.1 ∧ z.1 ≠ z.2 := by
  induction H with
  | leaf => simp [readingPositions]
  | @fork n u v w S T a b c different separate left right parent ln rn ihl ihr =>
    intro z hz
    simp only [readingPositions, List.mem_cons, List.mem_append] at hz
    rcases hz with eq | hl | hr
    · subst z
      obtain ⟨x,hx⟩ := (history_data hp hP C I left).2.1
      obtain ⟨y,hy⟩ := (history_data hp hP C I right).2.1
      have ev : C.Edge I u v := ⟨x,a x,b x,parent x (Finset.mem_union_left T hx),
        (history_data hp hP C I left).2.2 x hx,(ln x hx).1,(ln x hx).2⟩
      have ew : C.Edge I u w := ⟨y,a y,c y,parent y (Finset.mem_union_right S hy),
        (history_data hp hP C I right).2.2 y hy,(rn y hy).1,(rn y hy).2⟩
      classical
      let _ := Fintype.ofFinite Q
      obtain ⟨G,root,used,edges,rest⟩ := C.result I
      exact ⟨(G.target_eq u v ((edges u v).mpr ev)).trans
        (G.target_eq u w ((edges u w).mpr ew)).symm, different⟩
    · exact ihl z hl
    · exact ihr z hr

/-- Subsequent reading occurrences across every first-read branch. -/
noncomputable def allReadingPositions {D : Nat}
    {root : {q : Q // ∃ b, C.Used I q b}}
    (H : ∀ b : Fin p, SaturatedHistory hp hP C I D (root,b)
      (firstFiber hp hP b) (fun _ => 0)) : List (Slot × Slot) :=
  (List.ofFn (fun b => readingPositions hp hP C I (H b))).flatten

private theorem all_position_controls [Finite Q] {D : Nat}
    {root : {q : Q // ∃ b, C.Used I q b}}
    (H : ∀ b : Fin p, SaturatedHistory hp hP C I D (root,b)
      (firstFiber hp hP b) (fun _ => 0)) :
    ∀ z ∈ allReadingPositions hp hP C I H, z.1.1 = z.2.1 ∧ z.1 ≠ z.2 := by
  intro z hz
  obtain ⟨l,hl,hz⟩ := List.mem_flatten.mp hz
  obtain ⟨b,eq⟩ := List.mem_ofFn.mp hl
  subst l
  exact position_controls hp hP C I (H b) z hz

private theorem all_position_slots_nodup [Finite Q] {D : Nat}
    {root : {q : Q // ∃ b, C.Used I q b}}
    (H : ∀ b : Fin p, SaturatedHistory hp hP C I D (root,b)
      (firstFiber hp hP b) (fun _ => 0)) :
    ((allReadingPositions hp hP C I H).flatMap (fun z => [z.1,z.2])).Nodup := by
  rw [allReadingPositions, ← List.flatMap_id, List.flatMap_assoc,
    List.flatMap_def, List.map_ofFn]
  apply List.nodup_flatten.mpr
  constructor
  · intro l hl
    obtain ⟨b, rfl⟩ := List.mem_ofFn.mp hl
    exact ((position_slots_perm hp hP C I (H b)).nodup_iff.mpr
      (entry_slots_nodup hp hP C I (H b))).of_cons
  · apply List.pairwise_ofFn.mpr
    intro b c bc
    have separate : Disjoint (firstFiber hp hP b) (firstFiber hp hP c) := by
      apply Finset.disjoint_left.mpr
      intro x hb hc
      have xb : digit hp hP x = b := by simpa [firstFiber] using hb
      have xc : digit hp hP x = c := by simpa [firstFiber] using hc
      exact (ne_of_lt bc) (xb.symm.trans xc)
    have disjoint := entry_lists_disjoint hp hP C I (H b) (H c) separate
    apply List.disjoint_left.mpr
    intro slot hb hc
    apply List.disjoint_left.mp disjoint
    · exact (position_slots_perm hp hP C I (H b)).mem_iff.mp (List.mem_cons_of_mem _ hb)
    · exact (position_slots_perm hp hP C I (H c)).mem_iff.mp (List.mem_cons_of_mem _ hc)

/-- The number of subsequent reading occurrences assigned to a control;
first reads are excluded, and repeated positions would be counted separately. -/
noncomputable def occurrenceCount {D : Nat}
    {root : {q : Q // ∃ b, C.Used I q b}}
    (H : ∀ b : Fin p, SaturatedHistory hp hP C I D (root,b)
      (firstFiber hp hP b) (fun _ => 0)) (q : Q) : Nat :=
  ((allReadingPositions hp hP C I H).filter (fun z => z.1.1.val = q)).length

private theorem occurrence_bound [Finite Q] {D : Nat}
    {root : {q : Q // ∃ b, C.Used I q b}}
    (H : ∀ b : Fin p, SaturatedHistory hp hP C I D (root,b)
      (firstFiber hp hP b) (fun _ => 0)) (q : Q) : occurrenceCount hp hP C I H q ≤ p / 2 := by
  classical
  let A := allReadingPositions hp hP C I H
  let L := A.filter (fun z => z.1.1.val = q)
  let slots := L.flatMap (fun z => [z.1,z.2])
  have controls (z : Slot × Slot) (hz : z ∈ A) : z.1.1 = z.2.1 := by
    exact (all_position_controls hp hP C I H z hz).1
  have row (s : Slot) (hs : s ∈ slots) : s.1.val = q := by
    obtain ⟨z,hz,hs⟩ := List.mem_flatMap.mp hs
    have zz := List.mem_filter.mp hz
    have eq := controls z zz.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact of_decide_eq_true zz.2
    · exact (congrArg Subtype.val eq).symm.trans (of_decide_eq_true zz.2)
  have sub : L.Sublist A := List.filter_sublist
  have nodup : slots.Nodup := (all_position_slots_nodup hp hP C I H).sublist
    (sub.flatMap (fun z => [z.1,z.2]))
  have digits : (slots.map (fun s => s.2)).Nodup := nodup.map_on (by
    intro s hs t ht eq
    exact Prod.ext (Subtype.ext ((row s hs).trans (row t ht).symm)) eq)
  have bound := digits.length_le_card
  have length : slots.length = 2 * L.length := by
    simp [slots, List.length_flatMap, Nat.mul_comm]
  simp only [List.length_map, Fintype.card_fin] at bound
  change L.length ≤ p / 2
  omega

private theorem no_zero_positions {root : {q : Q // ∃ b, C.Used I q b}}
    (H : ∀ b : Fin p, SaturatedHistory hp hP C I 0 (root,b)
      (firstFiber hp hP b) (fun _ => 0)) : allReadingPositions hp hP C I H = [] := by
  have zero (u : Slot) (S : Finset Source) (a : Source → Nat)
      (K : SaturatedHistory hp hP C I 0 u S a) : readingPositions hp hP C I K = [] := by
    cases K
    rfl
  simp [allReadingPositions, zero]

private theorem all_event_iff {D : Nat}
    {root : {q : Q // ∃ b, C.Used I q b}}
    (H : ∀ b : Fin p, SaturatedHistory hp hP C I D (root,b)
      (firstFiber hp hP b) (fun _ => 0)) :
    ∀ x t, t ∈ readEvents hp hP C I x ↔
      ∃ e ∈ allHistories hp hP C I H, x ∈ entrySupport e ∧ entryTime e x = t := by
  intro x t
  constructor
  · exact all_event_cover hp hP C I H x t
  · rintro ⟨e,he,hx,time⟩
    have actual := (history_data hp hP C I (entryTree e)).2.2 x hx
    change C.Occurs I x (e.2.2.2.1 x) e.2.1 at actual
    change e.2.2.2.1 x = t at time
    rw [time] at actual
    obtain ⟨b,y,k,hy,hq,read,hb⟩ := (entrySlot e).1.property
    simp only [readEvents, Finset.mem_filter, Finset.mem_range]
    exact ⟨actual.1, actual.2.1 ▸ read⟩

/-- Every first-read fiber has a complete actual binary history, and the
read budget is attained on every original input. -/
theorem result [Finite Q] (D : Nat) (power : P = 2 ^ D)
    (read_bound : ∀ x, (readEvents hp hP C I x).card ≤ D + 1) :
    ∃ root : {q : Q // ∃ b, C.Used I q b}, root.val = C.initial ∧
      ∃ H : ∀ b : Fin p, SaturatedHistory hp hP C I D (root,b)
        (firstFiber hp hP b) (fun _ => 0),
      (∀ x, (readEvents hp hP C I x).card = D + 1) ∧
      (∀ b k x, TerminatesIn hp hP C I k (root,b) x ↔
        k = D ∧ digit hp hP x = b) ∧
      Function.Injective (((allHistories hp hP C I H).map entrySlot).get) ∧
      (∀ x t, t ∈ readEvents hp hP C I x ↔
        ∃ e ∈ allHistories hp hP C I H, x ∈ entrySupport e ∧ entryTime e x = t) ∧
      (∀ z ∈ allReadingPositions hp hP C I H, z.1.1 = z.2.1 ∧ z.1 ≠ z.2) ∧
      (∀ q, occurrenceCount hp hP C I H q ≤ p / 2) ∧
      (P = 1 → allReadingPositions hp hP C I H = []) := by
  classical
  let _ := Fintype.ofFinite Q
  obtain ⟨G, root, used, edges, adjacent, rest⟩ := C.result I
  have realized (b : Fin p) : ∀ x ∈ firstFiber hp hP b, C.Occurs I x 0 (G.root,b) := by
    intro x hx
    have positive : 0 < I.length x := by
      apply Nat.pos_of_ne_zero
      intro zero
      simpa [Controller.run, zero, I.first_read] using I.halt x
    refine ⟨positive, ?_, ?_⟩
    · simpa only [Controller.run, Function.iterate_zero, id_eq] using root.symm
    · simpa only [Controller.run, Function.iterate_zero, id_eq] using
        (Finset.mem_filter.mp hx).2
  have budget (x : Source) : (laterReads hp hP C I x 0).card ≤ D := by
    have count := first_read_count hp hP C I x
    have upper := read_bound x
    omega
  have histories (b : Fin p) : Nonempty (SaturatedHistory hp hP C I D (G.root,b)
      (firstFiber hp hP b) (fun _ => 0)) :=
    saturated_support hp hP C I (realized b) (fun x _ => budget x)
      ((first_fiber_card hp hP b).trans power)
  let H (b : Fin p) := Classical.choice (histories b)
  refine ⟨G.root, root, H, ?_, ?_, (all_slots_nodup hp hP C I H).injective_get,
    all_event_iff hp hP C I H, all_position_controls hp hP C I H,
    occurrence_bound hp hP C I H, ?_⟩
  · intro x
    have hx : x ∈ firstFiber hp hP (digit hp hP x) := by simp [firstFiber]
    have count := saturated_read_count hp hP C I (H (digit hp hP x)) x hx
    rw [first_read_count hp hP C I x, count]
  · intro b k x
    have bound := (SaturatedSlotUnfolding.result hp hP C I (H b) (H b)).1 k x
    simpa only [firstFiber, Finset.mem_filter, Finset.mem_univ, true_and] using bound
  · intro unit
    have zero : D = 0 := by
      have one : 2 ^ D = 1 := power.symm.trans unit
      simpa using one
    subst D
    exact no_zero_positions hp hP C I H

end D5.S3.ObserverMemory.Algorithms.SaturatedActualHistories
