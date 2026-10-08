/- GID: D5/S3/ObserverMemory/Algorithms/ActualControlSlots
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/ActualControlSlots
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual stationary reading slots give exact accounting and odd-base capacity bounds. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.ActualControlSlots

open scoped BigOperators

section SlotIncidence

variable {p : Nat} {Q : Type} [Fintype Q] [DecidableEq Q]

/-- Directed incidence of used reading slots. No acyclicity or unique-parent
condition is imposed. Every nonempty successor set has one target control. -/
structure SlotGraph (p : Nat) (Q : Type) [Fintype Q] [DecidableEq Q] where
  root : Q
  used : Finset (Q × Fin p)
  next : Q × Fin p → Finset (Q × Fin p)
  target : Q × Fin p → Q
  target_eq : ∀ u v, v ∈ next u → v.1 = target u
  source_used : ∀ u, (next u).Nonempty → u ∈ used
  target_used : ∀ u v, v ∈ next u → v ∈ used
  root_used : ∀ b, (root, b) ∈ used
  root_no_incoming : ∀ u b, (root, b) ∉ next u
  nonroot_incoming : ∀ v ∈ used, v.1 ≠ root → ∃ u, v ∈ next u
  at_most_two : ∀ u, (next u).card ≤ 2

namespace SlotGraph

variable (G : SlotGraph p Q)

noncomputable def incoming (v : Q × Fin p) : Finset (Q × Fin p) :=
  Finset.univ.filter (fun u => v ∈ G.next u)

noncomputable def missing (q : Q) : Nat :=
  (Finset.univ.filter (fun b : Fin p => (q, b) ∉ G.used)).card

noncomputable def excess (q : Q) : Nat :=
  ∑ b : Fin p, ((G.incoming (q, b)).card - 1)

noncomputable def singles (q : Q) : Nat :=
  (Finset.univ.filter (fun u => G.target u = q ∧ (G.next u).card = 1)).card

private noncomputable def predecessors (q : Q) : Finset (Q × Fin p) :=
  Finset.univ.filter (fun u => G.target u = q ∧ (G.next u).Nonempty)

/-- A zero-deficit row is covered exactly once by two-slot successor sets.
The ownership field makes these sets lie in the same target row. -/
private theorem zero_deficit_even (q : Q) (hq : q ≠ G.root)
    (hz : G.missing q = 0) (hh : G.excess q = 0) (hn : G.singles q = 0) :
    Even p := by
  classical
  let rel (u : Q × Fin p) (b : Fin p) := (q,b) ∈ G.next u
  have all_used : ∀ b : Fin p, (q,b) ∈ G.used := by
    simpa only [SlotGraph.missing, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_univ, true_implies, not_not] using hz
  have no_single : ∀ u, G.target u = q → (G.next u).card ≠ 1 := by
    simpa only [SlotGraph.singles, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_univ, true_implies, not_and] using hn
  have indegree (b : Fin p) : (G.incoming (q,b)).card = 1 := by
    have hle := Finset.single_le_sum (fun b _ => Nat.zero_le
      ((G.incoming (q,b)).card-1)) (Finset.mem_univ b)
    change (G.incoming (q,b)).card-1 ≤ G.excess q at hle
    obtain ⟨u,hu⟩ := G.nonroot_incoming (q,b) (all_used b) hq
    have pos : 0 < (G.incoming (q,b)).card := Finset.card_pos.mpr ⟨u,by
      simp only [SlotGraph.incoming, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hu⟩
    omega
  have above (u : Q × Fin p) (hu : u ∈ G.predecessors q) :
      ((Finset.univ : Finset (Fin p)).bipartiteAbove rel u).card = 2 := by
    have owns := (Finset.mem_filter.mp hu).2.1
    have pos := Finset.card_pos.mpr (Finset.mem_filter.mp hu).2.2
    have bound := G.at_most_two u
    have notone := no_single u owns
    have two : (G.next u).card = 2 := by omega
    let f : Fin p → Q × Fin p := fun b => (q,b)
    have inj : Function.Injective f := fun a b h => Prod.mk.inj h |>.2
    have preimage : Finset.univ.bipartiteAbove rel u =
        (G.next u).preimage f inj.injOn := by
      ext b
      simp [Finset.bipartiteAbove, Finset.mem_preimage, rel, f]
    have allrange (v : Q × Fin p) (hv : v ∈ G.next u) : v ∈ Set.range f :=
      ⟨v.2, Prod.ext ((G.target_eq u v hv).trans owns).symm rfl⟩
    rw [preimage, Finset.card_preimage, Finset.filter_true_of_mem allrange, two]
  have below (b : Fin p) (hb : b ∈ (Finset.univ : Finset (Fin p))) :
      ((G.predecessors q).bipartiteBelow rel b).card = 1 := by
    have eq : (G.predecessors q).bipartiteBelow rel b = G.incoming (q,b) := by
      ext u
      simp only [Finset.bipartiteBelow, predecessors, SlotGraph.incoming, Finset.mem_filter,
        Finset.mem_univ, true_and, rel]
      have ownership (h : (q,b) ∈ G.next u) : G.target u = q ∧ (G.next u).Nonempty :=
        ⟨(G.target_eq u (q,b) h).symm, ⟨(q,b),h⟩⟩
      exact and_iff_right_of_imp ownership
    rw [eq, indegree]
  have count := Finset.card_mul_eq_card_mul rel above below
  simp only [Finset.card_univ, Fintype.card_fin, mul_one] at count
  exact ⟨(G.predecessors q).card,by omega⟩

/-- Every nonroot row over an odd alphabet has an unused slot, a repeated
incoming incidence, or a one-successor predecessor owned by that row. -/
private theorem target_deficit (hp : Odd p) (q : Q) (hq : q ≠ G.root) :
    1 ≤ G.missing q + G.excess q + G.singles q := by
  by_contra bad
  have hz : G.missing q = 0 := by omega
  have hh : G.excess q = 0 := by omega
  have hn : G.singles q = 0 := by omega
  exact (Nat.not_even_iff_odd.mpr hp) (G.zero_deficit_even q hq hz hh hn)

/-- Local and summed target deficits use the same incidence graph. Cycles
and mergers contribute to excess and are not removed by a tree unfolding. -/
private theorem summed_deficit (hp : Odd p) :
    (∀ q, q ≠ G.root → 1 ≤ G.missing q + G.excess q + G.singles q) ∧
    Fintype.card Q - 1 ≤
      (∑ q, G.missing q) + (∑ q, G.excess q) + (∑ q, G.singles q) := by
  classical
  refine ⟨G.target_deficit hp, ?_⟩
  have local_bound : ∀ q ∈ Finset.univ.erase G.root,
      1 ≤ G.missing q + G.excess q + G.singles q := by
    intro q hq
    exact G.target_deficit hp q (Finset.mem_erase.mp hq).1
  have sum_bound := Finset.sum_le_sum local_bound
  have extend : (∑ q ∈ Finset.univ.erase G.root,
      (G.missing q + G.excess q + G.singles q)) ≤
      ∑ q : Q, (G.missing q + G.excess q + G.singles q) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun _ _ _ => Nat.zero_le _)
  have card : (Finset.univ.erase G.root).card = Fintype.card Q - 1 := by simp
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at sum_bound
  rw [card] at sum_bound
  simpa only [Finset.sum_add_distrib] using sum_bound.trans extend

noncomputable def terminalCount : Nat :=
  (G.used.filter (fun u => (G.next u).card = 0)).card

private theorem edge_balance :
    (∑ u, (G.next u).card) = ∑ v, (G.incoming v).card := by
  classical
  simp only [incoming, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

private theorem incoming_balance :
    (∑ v, (G.incoming v).card) + p = G.used.card + ∑ q, G.excess q := by
  classical
  have point (v : Q × Fin p) :
      (G.incoming v).card + (if v.1 = G.root then 1 else 0) =
        (if v ∈ G.used then 1 else 0) + ((G.incoming v).card - 1) := by
    by_cases root : v.1 = G.root
    · have empty : G.incoming v = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        have hv := (Finset.mem_filter.mp hu).2
        have eq : v = (G.root, v.2) := Prod.ext root rfl
        rw [eq] at hv
        exact G.root_no_incoming u v.2 hv
      have used : v ∈ G.used := by
        have eq : v = (G.root, v.2) := Prod.ext root rfl
        rw [eq]
        exact G.root_used _
      simp [empty, root, used]
    · by_cases used : v ∈ G.used
      · obtain ⟨u, hu⟩ := G.nonroot_incoming v used root
        have pos : 0 < (G.incoming v).card :=
          Finset.card_pos.mpr ⟨u, by simp [incoming, hu]⟩
        simp only [root, used, if_false, if_true]
        omega
      · have empty : G.incoming v = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro u hu
          exact used (G.target_used u v (Finset.mem_filter.mp hu).2)
        simp [empty, root, used]
  have total := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
    rfl (fun v _ => point v)
  simp only [Finset.sum_add_distrib] at total
  have root_sum : (∑ v : Q × Fin p, if v.1 = G.root then 1 else 0) = p := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single G.root]
    · simp
    · intro q _ hq
      simp [hq]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  have used_sum : (∑ v : Q × Fin p, if v ∈ G.used then 1 else 0) = G.used.card := by
    simp
  have excess_sum : (∑ v : Q × Fin p, ((G.incoming v).card - 1)) =
      ∑ q, G.excess q := by
    rw [Fintype.sum_prod_type]
    rfl
  rwa [root_sum, used_sum, excess_sum] at total

private theorem outgoing_balance :
    (∑ u, (G.next u).card) + (∑ q, G.singles q) + 2 * G.terminalCount =
      2 * G.used.card := by
  classical
  have point (u : Q × Fin p) :
      (G.next u).card + (if (G.next u).card = 1 then 1 else 0) +
        2 * (if u ∈ G.used ∧ (G.next u).card = 0 then 1 else 0) =
      2 * (if u ∈ G.used then 1 else 0) := by
    have bound := G.at_most_two u
    by_cases zero : (G.next u).card = 0
    · by_cases used : u ∈ G.used <;> simp [zero, used]
    · have used := G.source_used u (Finset.card_pos.mp (Nat.pos_of_ne_zero zero))
      by_cases one : (G.next u).card = 1
      · simp [one, used]
      · have two : (G.next u).card = 2 := by omega
        simp [two, used]
  have total := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
    rfl (fun u _ => point u)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at total
  have singles_sum : (∑ q, G.singles q) =
      ∑ u : Q × Fin p, if (G.next u).card = 1 then 1 else 0 := by
    simp only [singles, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    by_cases one : (G.next u).card = 1 <;> simp [one]
  have terminal_sum : (∑ u : Q × Fin p,
      if u ∈ G.used ∧ (G.next u).card = 0 then 1 else 0) = G.terminalCount := by
    unfold terminalCount
    rw [Finset.card_filter]
    have filter : (Finset.univ.filter (fun u => u ∈ G.used)) = G.used := by simp
    rw [← filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : u ∈ G.used <;> by_cases hz : (G.next u).card = 0 <;> simp [hu, hz]
  have used_sum : (∑ u : Q × Fin p, if u ∈ G.used then 1 else 0) = G.used.card := by
    simp
  rwa [← singles_sum, terminal_sum, used_sum] at total

private theorem nominal_balance :
    p * Fintype.card Q = G.used.card + ∑ q, G.missing q := by
  classical
  have split := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Q × Fin p))) (p := fun v => v ∈ G.used)
  have first : (Finset.univ.filter (fun v => v ∈ G.used)).card = G.used.card := by simp
  have second : (Finset.univ.filter (fun v => v ∉ G.used)).card = ∑ q, G.missing q := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter, missing, Fintype.sum_prod_type]
  rw [first, second] at split
  simpa [Fintype.card_prod, Nat.mul_comm] using split.symm

/-- Exact incidence accounting and the odd-alphabet improvement. The terminal
count is the actual number of used slots with empty successor set. -/
private theorem capacity_accounting (hp : 2 ≤ p) (P : Nat) (hP : 1 ≤ P)
    (hterminal : G.terminalCount = p * P) :
    p * Fintype.card Q = 2 * (p * P) - p +
      (∑ q, G.excess q) + (∑ q, G.singles q) + (∑ q, G.missing q) ∧
    2 * P - 1 ≤ Fintype.card Q ∧
    (Odd p →
      (∀ q, q ≠ G.root → 1 ≤ G.missing q + G.excess q + G.singles q) ∧
      Fintype.card Q - 1 ≤
        (∑ q, G.missing q) + (∑ q, G.excess q) + (∑ q, G.singles q) ∧
      2 * p * (P - 1) ≤ (p - 1) * (Fintype.card Q - 1)) := by
  classical
  have inc := G.incoming_balance
  have out := G.outgoing_balance
  have edges := G.edge_balance
  have nominal := G.nominal_balance
  rw [hterminal] at out
  have identity : p * Fintype.card Q + p = 2 * (p * P) +
      (∑ q, G.excess q) + (∑ q, G.singles q) + (∑ q, G.missing q) := by omega
  have lower : 2 * P - 1 ≤ Fintype.card Q := by
    have sub : 2 * P - 1 + 1 = 2 * P := by omega
    have scaled : p * (2 * P - 1) + p = 2 * (p * P) := by
      calc
        p * (2 * P - 1) + p = p * (2 * P - 1 + 1) := by ring
        _ = p * (2 * P) := congrArg (fun n => p * n) sub
        _ = 2 * (p * P) := by ring
    have product : p * (2 * P - 1) ≤ p * Fintype.card Q := by omega
    exact Nat.le_of_mul_le_mul_left product (by omega)
  have source_identity : p * Fintype.card Q = 2 * (p * P) - p +
      (∑ q, G.excess q) + (∑ q, G.singles q) + (∑ q, G.missing q) := by
    have scale : p ≤ 2 * (p * P) := by nlinarith
    omega
  refine ⟨source_identity, lower, ?_⟩
  intro odd
  obtain ⟨local_bound, global_bound⟩ := G.summed_deficit odd
  refine ⟨local_bound, global_bound, ?_⟩
  have qr : 1 ≤ Fintype.card Q := Fintype.card_pos_iff.mpr ⟨G.root⟩
  have subp : p - 1 + 1 = p := by omega
  have subP : P - 1 + 1 = P := by omega
  have subq : Fintype.card Q - 1 + 1 = Fintype.card Q := by omega
  nlinarith

end SlotGraph

end SlotIncidence

inductive Action where
  | read | wait | halt

/-- The control table has no access to the physical source except through
its fixed digit row. The output extension is used only on halt controls. -/
structure Controller (p P : Nat) (Q : Type) where
  initial : Q
  action : Q → Action
  waitNext : Q → Q
  readNext : Q → Fin p → Q
  output : Q → ZMod (p * P)

variable {p P : Nat} {Q : Type} (hp : 2 ≤ p) (hP : 0 < P)

/-- The physical digit of the finite source. -/
def digit (s : ZMod (p * P)) : Fin p := by
  letI : NeZero (p * P) := ⟨by positivity⟩
  exact ⟨s.val / P, Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using s.val_lt)⟩

namespace Controller

variable (C : Controller p P Q)

def step (c : ZMod (p * P) × Q) : ZMod (p * P) × Q :=
  match C.action c.2 with
  | .read => (c.1, C.readNext c.2 (digit hp hP c.1))
  | .wait => (c.1 + 1, C.waitNext c.2)
  | .halt => c

def run (x : ZMod (p * P)) (t : Nat) : ZMod (p * P) × Q :=
  (C.step hp hP)^[t] (x, C.initial)

/-- Every initial source has a finite correct execution of R(W⁺R)*.
The trajectory index is mathematical data and is not supplied to the table. -/
structure Correct where
  length : ZMod (p * P) → Nat
  first_read : C.action C.initial = .read
  halt : ∀ x, C.action (C.run hp hP x (length x)).2 = .halt
  output : ∀ x, C.output (C.run hp hP x (length x)).2 = x
  live : ∀ x t, t < length x → C.action (C.run hp hP x t).2 ≠ .halt
  after_read : ∀ x t, t + 1 < length x → C.action (C.run hp hP x t).2 = .read →
    C.action (C.run hp hP x (t + 1)).2 = .wait
  last_read : ∀ x, C.action (C.run hp hP x (length x - 1)).2 = .read

variable {hp hP} (I : C.Correct hp hP)

private theorem run_shift (x : ZMod (p * P)) (t n : Nat) :
    C.run hp hP x (t + n) = (C.step hp hP)^[n] (C.run hp hP x t) := by
  change (C.step hp hP)^[t + n] (x, C.initial) = _
  rw [Nat.add_comm t n, Function.iterate_add_apply]
  rfl

private theorem run_stopped (x : ZMod (p * P)) (t : Nat) (ht : I.length x ≤ t) :
    C.run hp hP x t = C.run hp hP x (I.length x) := by
  have fixed : C.step hp hP (C.run hp hP x (I.length x)) =
      C.run hp hP x (I.length x) := by simp [step, I.halt x]
  rw [← Nat.add_sub_of_le ht, C.run_shift]
  exact (Function.IsFixedPt.iterate fixed _).eq

/-- Equal joint configurations in actual initialized executions identify
both the original label and the event time, without acyclicity of controls. -/
private theorem configuration_separation {x y : ZMod (p * P)} {t u : Nat}
    (ht : t ≤ I.length x) (hu : u ≤ I.length y)
    (he : C.run hp hP x t = C.run hp hP y u) : x = y ∧ t = u := by
  have shift (n : Nat) : C.run hp hP x (t + n) = C.run hp hP y (u + n) := by
    rw [C.run_shift, C.run_shift, he]
  have far := shift (I.length x + I.length y)
  have rx := C.run_stopped I x (t + (I.length x + I.length y)) (by omega)
  have ry := C.run_stopped I y (u + (I.length x + I.length y)) (by omega)
  rw [rx, ry] at far
  have xy : x = y := (I.output x).symm.trans ((congrArg (fun c => C.output c.2) far).trans
    (I.output y))
  subst y
  have not_lt : ¬ t < u := by
    intro hlt
    have early := shift (I.length x - u)
    have stop : u + (I.length x - u) = I.length x := by omega
    rw [stop] at early
    exact I.live x (t + (I.length x - u)) (by omega)
      ((congrArg (fun c => C.action c.2) early).trans (I.halt x))
  have not_gt : ¬ u < t := by
    intro hlt
    have early := shift (I.length x - t)
    have stop : t + (I.length x - t) = I.length x := by omega
    rw [stop] at early
    exact I.live x (u + (I.length x - t)) (by omega)
      ((congrArg (fun c => C.action c.2) early.symm).trans (I.halt x))
  exact ⟨rfl, by omega⟩

private theorem root_no_return (x : ZMod (p * P)) (t : Nat)
    (ht : t ≤ I.length x) (hq : (C.run hp hP x t).2 = C.initial) : t = 0 := by
  have same : C.run hp hP x t = C.run hp hP (C.run hp hP x t).1 0 := by
    simp only [run, Function.iterate_zero, id_eq]
    exact Prod.ext rfl hq
  exact (C.configuration_separation I ht (Nat.zero_le _) same).2

/-- A used slot retains its actual source occurrence; a terminal slot is
one whose fixed row successor is a halt control. -/
def Used (q : Q) (b : Fin p) : Prop :=
  ∃ x t, t < I.length x ∧ (C.run hp hP x t).2 = q ∧
    C.action q = .read ∧ digit hp hP (C.run hp hP x t).1 = b

def Terminal (q : Q) (b : Fin p) : Prop :=
  C.Used I q b ∧ C.action (C.readNext q b) = .halt

private theorem positive_length (x : ZMod (p * P)) : 0 < I.length x := by
  by_contra hz
  have eq : I.length x = 0 := by omega
  have h := I.halt x
  simp only [eq, run, Function.iterate_zero, id_eq] at h
  rw [I.first_read] at h
  cases h

private theorem read_advance {x : ZMod (p * P)} {t : Nat}
    (hr : C.action (C.run hp hP x t).2 = .read) :
    C.run hp hP x (t + 1) =
      ((C.run hp hP x t).1, C.readNext (C.run hp hP x t).2
        (digit hp hP (C.run hp hP x t).1)) := by
  rw [C.run_shift]
  simp [step, hr]

private theorem terminal_label {q : Q} {b : Fin p} (h : C.Terminal I q b)
    {x : ZMod (p * P)} {t : Nat} (ht : t < I.length x)
    (hq : (C.run hp hP x t).2 = q)
    (hb : digit hp hP (C.run hp hP x t).1 = b) :
    C.output (C.readNext q b) = x ∧ t + 1 = I.length x := by
  have hr := h.1
  obtain ⟨_, _, _, _, read, _⟩ := hr
  have advance := C.read_advance (x := x) (t := t) (hq ▸ read)
  have control : (C.run hp hP x (t + 1)).2 = C.readNext q b := by
    rw [advance, hq, hb]
  have eq : t + 1 = I.length x := by
    by_contra bad
    exact I.live x (t + 1) (by omega) (control ▸ h.2)
  exact ⟨by simpa [← control, eq] using I.output x, eq⟩

/-- The final actual read defines a slot, including executions with no waits. -/
private noncomputable def finalSlot (x : ZMod (p * P)) : Q × Fin p :=
  ((C.run hp hP x (I.length x - 1)).2,
    digit hp hP (C.run hp hP x (I.length x - 1)).1)

private theorem final_terminal (x : ZMod (p * P)) :
    C.Terminal I (C.finalSlot I x).1 (C.finalSlot I x).2 := by
  have pos := C.positive_length I x
  refine ⟨⟨x, I.length x - 1, by omega, rfl, I.last_read x, rfl⟩, ?_⟩
  have advance := C.read_advance (I.last_read x)
  have eq : I.length x - 1 + 1 = I.length x := by omega
  rw [eq] at advance
  have control := congrArg Prod.snd advance
  dsimp only at control
  change C.action (C.readNext (C.run hp hP x (I.length x - 1)).2
    (digit hp hP (C.run hp hP x (I.length x - 1)).1)) = .halt
  rw [← control]
  exact I.halt x

/-- The used terminal slots correspond exactly to original sources. -/
private theorem final_bijective : Function.Bijective
    (fun x => (⟨C.finalSlot I x, C.final_terminal I x⟩ :
      {s : Q × Fin p // C.Terminal I s.1 s.2})) := by
  constructor
  · intro x y he
    have slot := congrArg (fun s : {s : Q × Fin p // C.Terminal I s.1 s.2} => s.val) he
    change C.finalSlot I x = C.finalSlot I y at slot
    have lx := C.terminal_label I (C.final_terminal I x)
      (by have := C.positive_length I x; omega) rfl rfl
    have ly := C.terminal_label I (C.final_terminal I y)
      (by have := C.positive_length I y; omega) rfl rfl
    change C.output (C.readNext (C.finalSlot I x).1 (C.finalSlot I x).2) = x ∧ _ at lx
    rw [slot] at lx
    exact lx.1.symm.trans ly.1
  · intro s
    obtain ⟨x, t, ht, hq, hr, hb⟩ := s.property.1
    have last := (C.terminal_label I s.property ht hq hb).2
    refine ⟨x, Subtype.ext ?_⟩
    have idx : I.length x - 1 = t := by omega
    exact Prod.ext (by simpa [finalSlot, idx] using hq)
      (by simpa [finalSlot, idx] using hb)

/-- Actual terminal-slot cardinality and the absence of later root visits.
No assumptions on distinct control histories, trees, or parent uniqueness occur. -/
private theorem terminal_root :
    Nat.card {s : Q × Fin p // C.Terminal I s.1 s.2} = p * P ∧
    (∀ x t, t ≤ I.length x → (C.run hp hP x t).2 = C.initial → t = 0) := by
  have : NeZero (p * P) := ⟨by positivity⟩
  have card := Nat.card_congr (Equiv.ofBijective _ (C.final_bijective I))
  refine ⟨?_, C.root_no_return I⟩
  simpa using card.symm

/-- A reachable waiting control includes an original-input occurrence. -/
def Waiting (q : Q) : Prop :=
  ∃ x t, t < I.length x ∧ (C.run hp hP x t).2 = q ∧ C.action q = .wait

private theorem read_action {q : Q} (hq : ∃ b, C.Used I q b) : C.action q = .read := by
  obtain ⟨b, x, t, ht, he, hr, hb⟩ := hq
  exact hr

private theorem root_read : ∃ b, C.Used I C.initial b := by
  refine ⟨digit hp hP 0, 0, 0, C.positive_length I 0, rfl, I.first_read, rfl⟩

private theorem incoming_wait {q : Q} (hq : ∃ b, C.Used I q b) (hn : q ≠ C.initial) :
    ∃ w, C.Waiting I w ∧ C.waitNext w = q := by
  obtain ⟨b, x, t, ht, he, hr, hb⟩ := hq
  have positive : 0 < t := by
    by_contra bad
    have zero : t = 0 := by omega
    simp only [zero, run, Function.iterate_zero, id_eq] at he
    exact hn he.symm
  have before : t - 1 < I.length x := by omega
  have advance : C.run hp hP x t = C.step hp hP (C.run hp hP x (t - 1)) := by
    have eq : t = (t - 1) + 1 := by omega
    conv_lhs => rw [eq]
    rw [C.run_shift]
    rfl
  have wait : C.action (C.run hp hP x (t - 1)).2 = .wait := by
    cases ha : C.action (C.run hp hP x (t - 1)).2 with
    | wait => rfl
    | halt => exact False.elim (I.live x (t - 1) before ha)
    | read =>
      have after := I.after_read x (t - 1) (by omega) ha
      have eq : t - 1 + 1 = t := by omega
      rw [eq, he, hr] at after
      cases after
  refine ⟨(C.run hp hP x (t - 1)).2, ⟨x, t - 1, before, rfl, wait⟩, ?_⟩
  simpa only [step, wait] using (congrArg Prod.snd advance).symm.trans he

private theorem wait_bound [Finite Q] :
    Nat.card {q : Q // ∃ b, C.Used I q b} - 1 ≤ Nat.card {q : Q // C.Waiting I q} := by
  classical
  let _ := Fintype.ofFinite Q
  let R := {q : Q // ∃ b, C.Used I q b}
  let W := {q : Q // C.Waiting I q}
  let root : R := ⟨C.initial, C.root_read I⟩
  let A := {q : R // q ≠ root}
  have arrival (q : A) : ∃ w, C.Waiting I w ∧ C.waitNext w = q.val.val := by
    apply C.incoming_wait I q.val.property
    intro he
    exact q.property (Subtype.ext he)
  let f : A → W := fun q => ⟨(arrival q).choose, (arrival q).choose_spec.1⟩
  have injective : Function.Injective f := by
    intro q r he
    apply Subtype.ext
    apply Subtype.ext
    have controls := congrArg Subtype.val he
    have targets := congrArg C.waitNext controls
    exact (arrival q).choose_spec.2.symm.trans (targets.trans (arrival r).choose_spec.2)
  have count : Nat.card A ≤ Nat.card W := Nat.card_le_card_of_injective f injective
  have nr : Nat.card A = Nat.card R - 1 := by
    simp only [A, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_unique]
  simpa only [nr, R, W] using count


private theorem wait_segment (x : ZMod (p * P)) (t n : Nat)
    (hw : ∀ i, i < n → C.action (C.run hp hP x (t + i)).2 = .wait) :
    C.run hp hP x (t + n) =
      ((C.run hp hP x t).1 + (n : ZMod (p * P)),
        C.waitNext^[n] (C.run hp hP x t).2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have before := ih (fun i hi => hw i (by omega))
    have ha := hw n (by omega)
    have advance : C.run hp hP x (t + (n + 1)) =
        C.step hp hP (C.run hp hP x (t + n)) := by
      rw [show t + (n + 1) = (t + n) + 1 by omega, C.run_shift]
      rfl
    rw [advance]
    simp only [before] at ha
    simp only [step, before, ha]
    simp [Function.iterate_succ_apply', Nat.cast_add, add_assoc]

private theorem shift_digit {b : Fin p} (a : Nat) (s : ZMod (p * P))
    (hb : digit hp hP s = b) :
    (digit hp hP (s + (a : ZMod (p * P)))).val = (b.val + a / P) % p ∨
    (digit hp hP (s + (a : ZMod (p * P)))).val = (b.val + a / P + 1) % p := by
  have : NeZero (p * P) := ⟨by positivity⟩
  have base : s.val / P = b.val := congrArg Fin.val hb
  change (s + (a : ZMod (p * P))).val / P = (b.val + a / P) % p ∨
    (s + (a : ZMod (p * P))).val / P = (b.val + a / P + 1) % p
  have moddiv (v : Nat) : v % (p * P) / P = v / P % p := by
    rw [Nat.mul_comm p P, Nat.mod_mul_right_div_self]
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, moddiv, Nat.add_div hP, base]
  split_ifs <;> simp

section FiniteCarrier

variable [Fintype Q] [DecidableEq Q]
attribute [local instance] Classical.propDecidable

local notation "RC" => {q : Q // ∃ b, C.Used I q b}

def Occurs (x : ZMod (p * P)) (t : Nat)
    (s : RC × Fin p) : Prop :=
  t < I.length x ∧ (C.run hp hP x t).2 = s.1.val ∧
    digit hp hP (C.run hp hP x t).1 = s.2

def Edge (u v : RC × Fin p) : Prop :=
  ∃ x i j, C.Occurs I x i u ∧ C.Occurs I x j v ∧ i < j ∧
    ∀ t, i < t → t < j → C.action (C.run hp hP x t).2 = .wait

omit [Fintype Q] [DecidableEq Q] in
private theorem edge_tail {u v : RC × Fin p} (he : C.Edge I u v) :
    ∃ x i d, C.Occurs I x i u ∧ 0 < d ∧
      (C.run hp hP x (i + 1 + d)).2 = v.1.val ∧
      digit hp hP (C.run hp hP x (i + 1 + d)).1 = v.2 ∧
      (∀ n, n < d → C.action (C.waitNext^[n] (C.readNext u.1.val u.2)) = .wait) ∧
      C.waitNext^[d] (C.readNext u.1.val u.2) = v.1.val ∧
      (C.run hp hP x (i + 1 + d)).1 =
        (C.run hp hP x i).1 + (d : ZMod (p * P)) := by
  obtain ⟨x, i, j, hi, hj, hij, waits⟩ := he
  have source_read : C.action (C.run hp hP x i).2 = .read :=
    hi.2.1 ▸ C.read_action I u.1.property
  have read_step := C.read_advance source_read
  have jlen := hj.1
  have pos : i + 1 < j := by
    by_contra bad
    have eq : j = i + 1 := by omega
    have after := I.after_read x i (by omega) source_read
    rw [← eq, hj.2.1, C.read_action I v.1.property] at after
    cases after
  let d := j - (i + 1)
  have eq : i + 1 + d = j := by dsimp [d]; omega
  have pure (n : Nat) (hn : n ≤ d) : C.run hp hP x (i + 1 + n) =
      ((C.run hp hP x i).1 + (n : ZMod (p * P)),
        C.waitNext^[n] (C.readNext u.1.val u.2)) := by
    rw [C.wait_segment x (i + 1) n (fun k hk => waits _ (by omega) (by omega))]
    rw [read_step]
    simp only [hi.2.1, hi.2.2]
  refine ⟨x, i, d, hi, by dsimp [d]; omega, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [eq] using hj.2.1
  · simpa only [eq] using hj.2.2
  · intro n hn
    have state := congrArg Prod.snd (pure n (Nat.le_of_lt hn))
    have actual := waits (i + 1 + n) (by omega) (by omega)
    simpa only [state] using actual
  · have state := congrArg Prod.snd (pure d le_rfl)
    exact state.symm.trans (by simpa only [eq] using hj.2.1)
  · exact congrArg Prod.fst (pure d le_rfl)

omit [Fintype Q] [DecidableEq Q] in
private theorem tail_unique {q : Q} {d e : Nat}
    (hd : ∀ n, n < d → C.action (C.waitNext^[n] q) = .wait)
    (he : ∀ n, n < e → C.action (C.waitNext^[n] q) = .wait)
    (rd : C.action (C.waitNext^[d] q) = .read)
    (re : C.action (C.waitNext^[e] q) = .read) : d = e := by
  rcases lt_trichotomy d e with h | h | h
  · have clash := he d h
    rw [rd] at clash
    cases clash
  · exact h
  · have clash := hd e h
    rw [re] at clash
    cases clash

omit [Fintype Q] [DecidableEq Q] in
private theorem edge_target_unique {u v w : RC × Fin p}
    (hv : C.Edge I u v) (hw : C.Edge I u w) : v.1 = w.1 := by
  obtain ⟨x, i, d, _, _, _, _, waits, endpoint, _⟩ := C.edge_tail I hv
  obtain ⟨y, j, e, _, _, _, _, waits', endpoint', _⟩ := C.edge_tail I hw
  have eq := C.tail_unique waits waits' (endpoint ▸ C.read_action I v.1.property)
    (endpoint' ▸ C.read_action I w.1.property)
  apply Subtype.ext
  exact endpoint.symm.trans (eq ▸ endpoint')

private noncomputable def successors (u : RC × Fin p) :
    Finset (RC × Fin p) := Finset.univ.filter (C.Edge I u)

private theorem successor_pair (u : RC × Fin p) (empty : (C.successors I u).Nonempty) :
    ∃ q b c, C.successors I u ⊆ {(q, b), (q, c)} ∧ c.val = (b.val + 1) % p := by
  classical
  obtain ⟨v, hv⟩ := empty
  have edge := (Finset.mem_filter.mp hv).2
  obtain ⟨x, i, d, hi, _, _, _, waits, endpoint, _⟩ := C.edge_tail I edge
  let b : Fin p := ⟨(u.2.val + d / P) % p, Nat.mod_lt _ (by omega)⟩
  let c : Fin p := ⟨(u.2.val + d / P + 1) % p, Nat.mod_lt _ (by omega)⟩
  have subset : C.successors I u ⊆ {(v.1, b), (v.1, c)} := by
    intro w hw
    have ew := (Finset.mem_filter.mp hw).2
    have target := C.edge_target_unique I ew edge
    obtain ⟨y, j, e, hj, _, _, digitw, waitw, endw, physical⟩ := C.edge_tail I ew
    have de := C.tail_unique waits waitw (endpoint ▸ C.read_action I v.1.property)
      (endw ▸ C.read_action I w.1.property)
    have digits := shift_digit (hp := hp) (hP := hP) e (C.run hp hP y j).1 hj.2.2
    rw [← physical, digitw, ← de] at digits
    rcases digits with h | h
    · exact Finset.mem_insert.mpr (Or.inl (Prod.ext target (Fin.ext h)))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
        (Prod.ext target (Fin.ext h))))
  exact ⟨v.1, b, c, subset, by simp only [b, c, Nat.mod_add_mod]⟩

omit [DecidableEq Q] in
private theorem successor_binary (u : RC × Fin p) :
    (C.successors I u).card ≤ 2 := by
  classical
  by_cases nonempty : (C.successors I u).Nonempty
  · obtain ⟨q, b, c, subset, _⟩ := C.successor_pair I u nonempty
    exact (Finset.card_le_card subset).trans (Finset.card_insert_le _ _ |>.trans (by simp))
  · rw [Finset.not_nonempty_iff_eq_empty.mp nonempty]
    simp

omit [Fintype Q] [DecidableEq Q] in
private theorem digit_surjective (b : Fin p) : ∃ x : ZMod (p * P), digit hp hP x = b := by
  have : NeZero (p * P) := ⟨by positivity⟩
  refine ⟨(b.val * P : Nat), ?_⟩
  apply Fin.ext
  have bound : b.val * P < p * P := Nat.mul_lt_mul_of_pos_right b.isLt hP
  change ((b.val * P : Nat) : ZMod (p * P)).val / P = b.val
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt bound, Nat.mul_div_cancel]
  exact hP

omit [Fintype Q] [DecidableEq Q] in
private theorem earlier_edge {v : RC × Fin p}
    (hv : ∃ x t, C.Occurs I x t v) (hn : v.1.val ≠ C.initial) :
    ∃ u, C.Edge I u v := by
  classical
  obtain ⟨x, j, hj⟩ := hv
  have jlen := hj.1
  have pos : 0 < j := by
    by_contra bad
    have eq : j = 0 := by omega
    have control := hj.2.1
    simp only [eq, run, Function.iterate_zero, id_eq] at control
    exact hn control.symm
  let S := (Finset.range j).filter (fun i => C.action (C.run hp hP x i).2 = .read)
  have nonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨pos, by simpa only [run, Function.iterate_zero, id_eq] using I.first_read⟩
  let i := S.max' nonempty
  have mem : i ∈ S := Finset.max'_mem S nonempty
  have before : i < j := Finset.mem_range.mp (Finset.mem_filter.mp mem).1
  have read : C.action (C.run hp hP x i).2 = .read := (Finset.mem_filter.mp mem).2
  let u : RC × Fin p :=
    (⟨(C.run hp hP x i).2, ⟨digit hp hP (C.run hp hP x i).1,
      x, i, by omega, rfl, read, rfl⟩⟩, digit hp hP (C.run hp hP x i).1)
  refine ⟨u, x, i, j, ⟨by omega, rfl, rfl⟩, hj, before, ?_⟩
  intro t hit htj
  have no_read : C.action (C.run hp hP x t).2 ≠ .read := by
    intro hr
    have mt : t ∈ S := by simp [S, htj, hr]
    have bound := Finset.le_max' S t mt
    change t ≤ i at bound
    omega
  cases ha : C.action (C.run hp hP x t).2 with
  | read => exact False.elim (no_read ha)
  | halt => exact False.elim (I.live x t (by omega) ha)
  | wait => rfl

omit [Fintype Q] [DecidableEq Q] in
private theorem later_edge {u : RC × Fin p}
    (hu : ∃ x t, C.Occurs I x t u)
    (hn : C.action (C.readNext u.1.val u.2) ≠ .halt) :
    ∃ v, C.Edge I u v := by
  classical
  obtain ⟨x, i, hi⟩ := hu
  have ilen := hi.1
  have read := C.read_action I u.1.property
  have advance := C.read_advance (x := x) (t := i) (hi.2.1 ▸ read)
  have early : i + 1 < I.length x := by
    by_contra bad
    have eq : i + 1 = I.length x := by omega
    have next : (C.run hp hP x (I.length x)).2 = C.readNext u.1.val u.2 := by
      simpa only [eq, hi.2.1, hi.2.2] using congrArg Prod.snd advance
    exact hn (next ▸ I.halt x)
  let S := (Finset.range (I.length x)).filter
    (fun j => i < j ∧ C.action (C.run hp hP x j).2 = .read)
  have nonempty : S.Nonempty := by
    refine ⟨I.length x - 1, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by omega, I.last_read x⟩
  let j := S.min' nonempty
  have mem : j ∈ S := Finset.min'_mem S nonempty
  obtain ⟨hjt, hij, readj⟩ := Finset.mem_filter.mp mem
  have hjlen : j < I.length x := Finset.mem_range.mp hjt
  let v : RC × Fin p :=
    (⟨(C.run hp hP x j).2, ⟨digit hp hP (C.run hp hP x j).1,
      x, j, hjlen, rfl, readj, rfl⟩⟩, digit hp hP (C.run hp hP x j).1)
  refine ⟨v, x, i, j, hi, ⟨hjlen, rfl, rfl⟩, hij, ?_⟩
  intro t hit htj
  have no_read : C.action (C.run hp hP x t).2 ≠ .read := by
    intro hr
    have mt : t ∈ S := by simp [S, show t < I.length x by omega, hit, hr]
    have bound := Finset.min'_le S t mt
    change j ≤ t at bound
    omega
  cases ha : C.action (C.run hp hP x t).2 with
  | read => exact False.elim (no_read ha)
  | halt => exact False.elim (I.live x t (by omega) ha)
  | wait => rfl

omit [DecidableEq Q] in
private theorem terminal_successors {u : RC × Fin p}
    (hu : ∃ x t, C.Occurs I x t u) :
    C.action (C.readNext u.1.val u.2) = .halt ↔ C.successors I u = ∅ := by
  classical
  constructor
  · intro halt
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨x, i, d, _, positive, _, _, waits, _, _⟩ :=
      C.edge_tail I (Finset.mem_filter.mp hv).2
    have clash := waits 0 positive
    simp only [Function.iterate_zero, id_eq, halt] at clash
    cases clash
  · intro empty
    by_contra hn
    obtain ⟨v, hv⟩ := C.later_edge I hu hn
    have mem : v ∈ C.successors I u := by simp [successors, hv]
    rw [empty] at mem
    exact Finset.notMem_empty _ mem

private noncomputable def slotGraph :
    SlotGraph p (RC) := by
  classical
  let root : RC := ⟨C.initial, C.root_read I⟩
  let target (u : RC × Fin p) : RC :=
    if h : ∃ v, C.Edge I u v then h.choose.1 else root
  refine {
    root := root
    used := Finset.univ.filter (fun u => ∃ x t, C.Occurs I x t u)
    next := C.successors I
    target := target
    target_eq := ?_
    source_used := ?_
    target_used := ?_
    root_used := ?_
    root_no_incoming := ?_
    nonroot_incoming := ?_
    at_most_two := C.successor_binary I }
  · intro u v hv
    have edge := (Finset.mem_filter.mp hv).2
    have ex : ∃ w, C.Edge I u w := ⟨v, edge⟩
    simp only [target, dif_pos ex]
    exact C.edge_target_unique I edge ex.choose_spec
  · intro u hu
    obtain ⟨v, hv⟩ := hu
    obtain ⟨x, i, j, hi, _, _, _⟩ := (Finset.mem_filter.mp hv).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, i, hi⟩
  · intro u v hv
    obtain ⟨x, i, j, _, hj, _, _⟩ := (Finset.mem_filter.mp hv).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, j, hj⟩
  · intro b
    obtain ⟨x, hx⟩ := digit_surjective (hp := hp) (hP := hP) b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x, 0, C.positive_length I x, rfl, hx⟩
  · intro u b hv
    obtain ⟨x, i, j, _, hj, hij, _⟩ := (Finset.mem_filter.mp hv).2
    have zero := C.root_no_return I x j (Nat.le_of_lt hj.1) hj.2.1
    omega
  · intro v hv hn
    have used := (Finset.mem_filter.mp hv).2
    have nr : v.1.val ≠ C.initial := by
      intro eq
      exact hn (Subtype.ext eq)
    obtain ⟨u, hu⟩ := C.earlier_edge I used nr
    exact ⟨u, by simp [successors, hu]⟩

private theorem graph_terminal_count : (C.slotGraph I).terminalCount = p * P := by
  classical
  have terminal_iff (u : RC × Fin p) :
      u ∈ (C.slotGraph I).used ∧ ((C.slotGraph I).next u).card = 0 ↔
        C.Terminal I u.1.val u.2 := by
    change (u ∈ Finset.univ.filter (fun u => ∃ x t, C.Occurs I x t u)) ∧
      (C.successors I u).card = 0 ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨used, empty⟩
      obtain ⟨x, t, ht, hq, hb⟩ := used
      refine ⟨⟨x, t, ht, hq, C.read_action I u.1.property, hb⟩, ?_⟩
      exact (C.terminal_successors I ⟨x, t, ht, hq, hb⟩).mpr (Finset.card_eq_zero.mp empty)
    · rintro ⟨⟨x, t, ht, hq, hr, hb⟩, halt⟩
      have used : ∃ x t, C.Occurs I x t u := ⟨x, t, ht, hq, hb⟩
      exact ⟨used, Finset.card_eq_zero.mpr ((C.terminal_successors I used).mp halt)⟩
  let A := {u : RC × Fin p // C.Terminal I u.1.val u.2}
  let B := {u : Q × Fin p // C.Terminal I u.1 u.2}
  let e : A ≃ B := {
    toFun := fun u => ⟨(u.val.1.val, u.val.2), u.property⟩
    invFun := fun u => ⟨(⟨u.val.1, ⟨u.val.2, u.property.1⟩⟩, u.val.2), u.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have count := (C.terminal_root I).1
  have equal : (C.slotGraph I).terminalCount = Nat.card A := by
    rw [SlotGraph.terminalCount, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    apply congrArg Finset.card
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, terminal_iff]
  rw [equal, Nat.card_congr e]
  exact count

end FiniteCarrier


attribute [local instance] Classical.propDecidable

/-- The actual reading-slot graph, its exact incidence identity, and all
three capacity bounds. The width P is arbitrary positive, including p^k. -/
theorem result [Fintype Q] [DecidableEq Q] :
    let r := Nat.card {q : Q // ∃ b, C.Used I q b}
    let w := Nat.card {q : Q // C.Waiting I q}
    ∃ G : SlotGraph p {q : Q // ∃ b, C.Used I q b},
      G.root.val = C.initial ∧
      (∀ u, u ∈ G.used ↔ ∃ x t, C.Occurs I x t u) ∧
      (∀ u v, v ∈ G.next u ↔ C.Edge I u v) ∧
      (∀ u, (G.next u).Nonempty → ∃ q b c,
        G.next u ⊆ {(q, b), (q, c)} ∧ c.val = (b.val + 1) % p) ∧
      G.terminalCount = p * P ∧
      Nat.card {s : Q × Fin p // C.Terminal I s.1 s.2} = p * P ∧
      (∀ x t, t ≤ I.length x → (C.run hp hP x t).2 = C.initial → t = 0) ∧
      r - 1 ≤ w ∧
      p * r = 2 * (p * P) - p +
        (∑ q, G.excess q) + (∑ q, G.singles q) + (∑ q, G.missing q) ∧
      2 * P - 1 ≤ r ∧
      (Odd p →
        (∀ q, q ≠ G.root → 1 ≤ G.missing q + G.excess q + G.singles q) ∧
        r - 1 ≤ (∑ q, G.missing q) + (∑ q, G.excess q) + (∑ q, G.singles q) ∧
        2 * p * (P - 1) ≤ (p - 1) * (r - 1)) := by
  classical
  dsimp only
  let G := C.slotGraph I
  have terminal := C.graph_terminal_count I
  have count := G.capacity_accounting hp P (by omega) terminal
  have card : Fintype.card {q : Q // ∃ b, C.Used I q b} =
      Nat.card {q : Q // ∃ b, C.Used I q b} := Nat.card_eq_fintype_card.symm
  obtain ⟨id, lower, odd⟩ := count
  rw [card] at id lower odd
  obtain ⟨terminal_slots, root⟩ := C.terminal_root I
  refine ⟨G, rfl, ?_, ?_, C.successor_pair I, terminal, terminal_slots, root,
    C.wait_bound I, id, lower, odd⟩
  · intro u
    change u ∈ Finset.univ.filter (fun u => ∃ x t, C.Occurs I x t u) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro u v
    change v ∈ Finset.univ.filter (C.Edge I u) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end Controller
end D5.S3.ObserverMemory.Algorithms.ActualControlSlots
