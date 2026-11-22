/- GID: D5/S3/Arith/FibonacciAtomic/LocalWiring/PhysicalBirthClock
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/LocalWiring/PhysicalBirthClock
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Basic]
   utility: none
   digest: Exact ordered physical births and finite-prefix dependence for the fixed source stream. -/

import D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers

/-! An actual left-first update of the old tree with one source input per beta split. -/

namespace D5.S3.Arith.FibonacciAtomic.LocalWiring.PhysicalBirthClock

open D5.S3.Arith.FibonacciAtomic.LocalWiring.LocalTwoStepRecognizer
open D5.S3.Arith.FibonacciAtomic.LocalWiring.KnownSeedCurrentFibers


def alphaLeaves : Labelled → Nat
  | .of b => if b then 1 else 0
  | .mul l r => alphaLeaves l + alphaLeaves r

def betaLeaves : Labelled → Nat
  | .of b => if b then 0 else 1
  | .mul l r => betaLeaves l + betaLeaves r

private theorem leafCounts_step {t w : Labelled} (h : Step t w) :
    alphaLeaves w = betaLeaves t ∧ betaLeaves w = alphaLeaves t + betaLeaves t := by
  induction h with
  | alphaToBeta => decide
  | betaLeft => decide
  | betaRight => decide
  | @branch l l' r r' _ _ il ir =>
    constructor
    · change alphaLeaves l' + alphaLeaves r' = betaLeaves l + betaLeaves r
      rw [il.1, ir.1]
    · change betaLeaves l' + betaLeaves r' = (alphaLeaves l + alphaLeaves r) +
        (betaLeaves l + betaLeaves r)
      rw [il.2, ir.2]
      omega

private theorem leafCounts_after_shifted {n : Nat} {t : Labelled} (ht : After n t) :
    betaLeaves t = Nat.fib n ∧ alphaLeaves t + betaLeaves t = Nat.fib (n + 1) := by
  induction ht with
  | zero => decide
  | next _ h ih =>
    obtain ⟨ha, hb⟩ := leafCounts_step h
    exact ⟨hb.trans ih.2, by rw [ha, hb, ih.2, ih.1, Nat.fib_add_two]⟩

private theorem leafCounts_after {n : Nat} {t : Labelled} (hn : 1 ≤ n) (ht : After n t) :
    betaLeaves t = Nat.fib n ∧ alphaLeaves t = Nat.fib (n - 1) := by
  cases n with
  | zero => omega
  | succ n =>
    cases ht with
    | next h st =>
      exact ⟨(leafCounts_after_shifted (.next h st)).1,
        (leafCounts_step st).1.trans (leafCounts_after_shifted h).1⟩

def clockSum (n : Nat) : Nat := ((List.range n).map Nat.fib).sum

private theorem clockSum_add_one (n : Nat) : clockSum (n + 1) = clockSum n + Nat.fib n := by
  simp [clockSum, List.range_succ]

private theorem clockSum_eq_fib (n : Nat) : clockSum n = Nat.fib (n + 1) - 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hp := Nat.fib_pos.mpr (by omega : 0 < n + 1)
    rw [clockSum_add_one, ih, Nat.fib_add_two]
    omega



def oldBetaAddresses (path : Address) : Labelled → List Address
  | .of true => []
  | .of false => [path]
  | .mul l r =>
      oldBetaAddresses (path ++ [false]) l ++ oldBetaAddresses (path ++ [true]) r

private theorem mem_oldBetaAddresses_prefix (path q : Address) (t : Labelled) :
    q ∈ oldBetaAddresses path t ↔ ∃ s : Address, q = path ++ s ∧ isBeta t s = true := by
  induction t generalizing path with
  | of a =>
    cases a <;> simp only [oldBetaAddresses, List.mem_singleton, List.not_mem_nil]
    · constructor
      · rintro rfl
        exact ⟨[], by simp, by decide⟩
      · rintro ⟨s, rfl, hs⟩
        cases s with
        | nil => simp
        | cons b s =>
          cases b <;> simp [isBeta, atTree] at hs
    · refine ⟨False.elim, ?_⟩
      rintro ⟨s, _, hs⟩
      cases s with
      | nil =>
        have he : (some (FreeMagma.of true) : Option Labelled) = some beta :=
          of_decide_eq_true hs
        cases he
      | cons b s => cases b <;> simp [isBeta, atTree] at hs
  | mul l r ihl ihr =>
    rw [oldBetaAddresses, List.mem_append, ihl, ihr]
    constructor
    · rintro (⟨s, hq, hs⟩ | ⟨s, hq, hs⟩)
      · exact ⟨false :: s, by simpa [List.append_assoc] using hq, hs⟩
      · exact ⟨true :: s, by simpa [List.append_assoc] using hq, hs⟩
    · rintro ⟨s, hq, hs⟩
      cases s with
      | nil => simp [isBeta, atTree, beta] at hs
      | cons b s =>
        cases b
        · exact Or.inl ⟨s, by simpa [List.append_assoc] using hq, hs⟩
        · exact Or.inr ⟨s, by simpa [List.append_assoc] using hq, hs⟩

private theorem mem_oldBetaAddresses (q : Address) (t : Labelled) :
    q ∈ oldBetaAddresses [] t ↔ isBeta t q = true := by
  rw [mem_oldBetaAddresses_prefix]
  simp

private theorem beta_address_cross_prefix (path a b : Address) :
    List.Lex (fun x y : Bool => x < y) (path ++ false :: a) (path ++ true :: b) := by
  induction path with
  | nil => exact .rel (by decide)
  | cons x xs ih => exact .cons ih

private theorem oldBetaAddresses_pairwise (path : Address) (t : Labelled) :
    (oldBetaAddresses path t).Pairwise (List.Lex (fun a b : Bool => a < b)) := by
  induction t generalizing path with
  | of a => cases a <;> simp [oldBetaAddresses]
  | mul l r ihl ihr =>
    apply List.pairwise_append.mpr
    refine ⟨ihl _, ihr _, ?_⟩
    intro a ha b hb
    obtain ⟨a', rfl, _⟩ := (mem_oldBetaAddresses_prefix _ _ _).mp ha
    obtain ⟨b', rfl, _⟩ := (mem_oldBetaAddresses_prefix _ _ _).mp hb
    simpa only [List.append_assoc, List.singleton_append] using beta_address_cross_prefix path a' b'

private theorem oldBetaAddresses_nodup (path : Address) (t : Labelled) :
    (oldBetaAddresses path t).Nodup := by
  apply (oldBetaAddresses_pairwise path t).imp
  intro a b h hab
  subst b
  exact List.lex_irrefl (fun x => lt_irrefl x) a h




/-- A fixed source-owned bit stream, indexed at births starting with 1. -/
abbrev BirthStream := Nat → Bool

/-- The actual next input at cursor c. No observation advances this cursor. -/
def consume (z : BirthStream) (c : Nat) : Bool := z (c + 1)

/-- One actual beta split. The serial field counts births, not physical time. -/
structure BirthEvent where
  serial : Nat
  update : Nat
  parent : Address
  mark : Bool
  deriving DecidableEq, Repr

structure BirthRun where
  tree : Labelled
  cursor : Nat
  births : List BirthEvent

/-- Traverse the old tree in physical order. Only an old beta consumes a bit.
A newly created child is never an argument of either recursive call. -/
def birthRound (z : BirthStream) (update : Nat) (c : Nat) (p : Address) : Labelled → BirthRun
  | .of true => ⟨beta, c, []⟩
  | .of false =>
    let b := consume z c
    ⟨if b then .mul beta alpha else .mul alpha beta, c + 1, [⟨c + 1, update, p, b⟩]⟩
  | .mul l r =>
    let a := birthRound z update c (p ++ [false]) l
    let b := birthRound z update a.cursor (p ++ [true]) r
    ⟨.mul a.tree b.tree, b.cursor, a.births ++ b.births⟩

/-- Complete successive rounds from alpha, retaining chronological birth
marks without providing them as extra read ports to an observer. -/
def physicalBirthClock (z : BirthStream) : Nat → BirthRun
  | 0 => ⟨alpha, 0, []⟩
  | n + 1 =>
    let old := physicalBirthClock z n
    let r := birthRound z (n + 1) old.cursor [] old.tree
    ⟨r.tree, r.cursor, old.births ++ r.births⟩

private theorem round_step (z : BirthStream) (epoch c : Nat) (p : Address) (t : Labelled) :
    Step t (birthRound z epoch c p t).tree := by
  induction t generalizing c p with
  | of b =>
    cases b
    · change Step beta (if consume z c then .mul beta alpha else .mul alpha beta)
      cases consume z c
      · exact .betaRight
      · exact .betaLeft
    · exact .alphaToBeta
  | mul l r il ir => exact .branch (il c _) (ir _ _)

private theorem round_size (z : BirthStream) (epoch c : Nat) (p : Address) (t : Labelled) :
    (birthRound z epoch c p t).cursor = c + betaLeaves t ∧
    (birthRound z epoch c p t).births.length = betaLeaves t := by
  induction t generalizing c p with
  | of b => cases b <;> simp [birthRound, betaLeaves]
  | mul l r il ir =>
    let a := birthRound z epoch c (p ++ [false]) l
    let b := birthRound z epoch a.cursor (p ++ [true]) r
    have ha := il c (p ++ [false])
    have hb := ir a.cursor (p ++ [true])
    change b.cursor = c + (betaLeaves l + betaLeaves r) ∧
      (a.births ++ b.births).length = betaLeaves l + betaLeaves r
    exact ⟨by rw [hb.1, ha.1]; omega, by rw [List.length_append, ha.2, hb.2]⟩

private theorem round_epoch_mark (z : BirthStream) (epoch c : Nat) (p : Address) (t : Labelled) :
    ∀ e ∈ (birthRound z epoch c p t).births, e.update = epoch ∧ e.mark = z e.serial := by
  induction t generalizing c p with
  | of b => cases b <;> simp [birthRound, consume]
  | mul l r il ir =>
    intro e he
    rcases List.mem_append.mp he with hl | hr
    · exact il _ _ e hl
    · exact ir _ _ e hr

private theorem round_serials (z : BirthStream) (epoch c : Nat) (p : Address) (t : Labelled) :
    (birthRound z epoch c p t).births.map BirthEvent.serial =
      List.range' (c + 1) (betaLeaves t) := by
  induction t generalizing c p with
  | of b => cases b <;> simp [birthRound, betaLeaves]
  | mul l r il ir =>
    let a := birthRound z epoch c (p ++ [false]) l
    let b := birthRound z epoch a.cursor (p ++ [true]) r
    change (a.births ++ b.births).map BirthEvent.serial =
      List.range' (c + 1) (betaLeaves l + betaLeaves r)
    rw [List.map_append, il, ir, (round_size z epoch c (p ++ [false]) l).1]
    rw [show c + betaLeaves l + 1 = c + 1 + 1 * betaLeaves l by omega, List.range'_append]

private theorem round_prefix (z z' : BirthStream) (epoch c : Nat) (p : Address) (t : Labelled)
    (same : ∀ k, c < k → k ≤ c + betaLeaves t → z k = z' k) :
    birthRound z epoch c p t = birthRound z' epoch c p t := by
  induction t generalizing c p with
  | of b =>
    cases b
    · have h := same (c + 1) (by omega) (by simp [betaLeaves])
      simp only [birthRound, consume, h]
      rfl
    · rfl
  | mul l r il ir =>
    let a := birthRound z epoch c (p ++ [false]) l
    have hL : a = birthRound z' epoch c (p ++ [false]) l :=
      il c _ (fun k hk hK => same k hk (by simp only [betaLeaves]; omega))
    have hc : a.cursor = c + betaLeaves l := (round_size z epoch c _ l).1
    have hR := ir a.cursor (p ++ [true]) (fun k hk hK => same k
      (by omega) (by simp only [betaLeaves]; omega))
    unfold birthRound
    rw [← hL]
    change (⟨.mul a.tree (birthRound z epoch a.cursor (p ++ [true]) r).tree,
      (birthRound z epoch a.cursor (p ++ [true]) r).cursor,
      a.births ++ (birthRound z epoch a.cursor (p ++ [true]) r).births⟩ : BirthRun) = _
    rw [hR]

private theorem clock_after (z : BirthStream) (n : Nat) : After n (physicalBirthClock z n).tree := by
  induction n with
  | zero => exact .zero
  | succ n ih => exact .next ih (round_step _ _ _ _ _)

private theorem clock_count (z : BirthStream) (n : Nat) :
    (physicalBirthClock z n).cursor = clockSum n ∧
    (physicalBirthClock z n).births.length = clockSum n := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    let old := physicalBirthClock z n
    let r := birthRound z (n + 1) old.cursor [] old.tree
    have count := round_size z (n + 1) old.cursor [] old.tree
    have oldBeta := (leafCounts_after_shifted (clock_after z n)).1
    change r.cursor = clockSum (n+1) ∧ (old.births ++ r.births).length = clockSum (n+1)
    rw [count.1, List.length_append, count.2, ih.1, ih.2, oldBeta, clockSum_add_one]
    exact ⟨rfl, rfl⟩

private theorem clock_serials (z : BirthStream) (n : Nat) :
    (physicalBirthClock z n).births.map BirthEvent.serial = List.range' 1 (clockSum n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let old := physicalBirthClock z n
    let r := birthRound z (n + 1) old.cursor [] old.tree
    have hb := (leafCounts_after_shifted (clock_after z n)).1
    change (old.births ++ r.births).map BirthEvent.serial = _
    rw [List.map_append, ih, round_serials, (clock_count z n).1, hb, clockSum_add_one]
    rw [show clockSum n + 1 = 1 + 1 * clockSum n by omega, List.range'_append]

private theorem clock_epoch_mark (z : BirthStream) (n : Nat) :
    ∀ e ∈ (physicalBirthClock z n).births, e.update ≤ n ∧ e.mark = z e.serial := by
  induction n with
  | zero => simp [physicalBirthClock]
  | succ n ih =>
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact ⟨(ih e he).1.trans (Nat.le_succ _), (ih e he).2⟩
    · have hh := round_epoch_mark _ _ _ _ _ e he
      exact ⟨hh.1.le, hh.2⟩

private theorem clock_prefix (z z' : BirthStream) (n : Nat)
    (same : ∀ j, 1 ≤ j → j ≤ clockSum n → z j = z' j) :
    physicalBirthClock z n = physicalBirthClock z' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hh := ih (fun j hp hj => same j hp (by rw [clockSum_add_one]; omega))
    let old := physicalBirthClock z n
    have he := round_prefix z z' (n+1) old.cursor [] old.tree (by
      intro j hj hk
      apply same j (by omega)
      rwa [clockSum_add_one, ← (leafCounts_after_shifted (clock_after z n)).1,
        ← (clock_count z n).1])
    dsimp only [old] at he
    simp only [physicalBirthClock, ← hh, he]

private theorem mature_prefix (z : BirthStream) (n : Nat) :
    (physicalBirthClock z (n+1)).births.filter (fun e => e.update < n+1) =
      (physicalBirthClock z n).births := by
  change List.filter (fun e : BirthEvent => e.update < n+1)
    ((physicalBirthClock z n).births ++
      (birthRound z (n+1) (physicalBirthClock z n).cursor [] (physicalBirthClock z n).tree).births) = _
  rw [List.filter_append, List.filter_eq_self.mpr]
  · have hz : (birthRound z (n+1) (physicalBirthClock z n).cursor []
        (physicalBirthClock z n).tree).births.filter (fun e => e.update < n+1) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e he
      simp [(round_epoch_mark z _ _ _ _ e he).1]
    rw [hz, List.append_nil]
  · intro e he
    exact decide_eq_true (Nat.lt_succ_of_le (clock_epoch_mark z n e he).1)

private theorem clock_indexed (z : BirthStream) (n i : Nat) (e : BirthEvent)
    (h : (physicalBirthClock z n).births[i]? = some e) : consume z i = e.mark ∧ e.serial = i + 1 := by
  have hi : ((physicalBirthClock z n).births.map BirthEvent.serial)[i]? = some e.serial := by
    simp [List.getElem?_map, h]
  have hil : i < clockSum n := by
    rw [← (clock_count z n).2]
    exact (List.getElem?_eq_some_iff.mp h).choose
  rw [clock_serials, List.getElem?_range' hil] at hi
  have hs : e.serial = i + 1 := by injection hi with hh; omega
  have hm := clock_epoch_mark z n e (List.mem_of_getElem? h)
  exact ⟨by simpa [consume, hs] using hm.2.symm, hs⟩


/-- Earlier update first; left-before-right lexicographic order within a round. -/
def chronologicallyBefore (e f : BirthEvent) : Prop :=
  e.update < f.update ∨ (e.update = f.update ∧ List.Lex (fun a b : Bool => a < b) e.parent f.parent)

private theorem round_addresses (z : BirthStream) (epoch c : Nat) (p : Address) (t : Labelled) :
    (birthRound z epoch c p t).births.map BirthEvent.parent = oldBetaAddresses p t := by
  induction t generalizing c p with
  | of b => cases b <;> rfl
  | mul l r il ir =>
    simp only [birthRound, List.map_append, oldBetaAddresses, il, ir]

private theorem round_old_orientation (z : BirthStream) (epoch c : Nat) (p : Address) (t : Labelled)
    (e : BirthEvent) (h : e ∈ (birthRound z epoch c p t).births) :
    ∃ q, e.parent = p ++ q ∧ atTree (birthRound z epoch c p t).tree q =
      some (if e.mark then .mul beta alpha else .mul alpha beta) := by
  induction t generalizing c p with
  | of b =>
    cases b
    · have he : e = ⟨c+1, epoch, p, consume z c⟩ := by
        exact List.mem_singleton.mp h
      subst e
      refine ⟨[], (List.append_nil p).symm, ?_⟩
      cases b : consume z c <;> simp [birthRound, atTree, b]
    · contradiction
  | mul l r il ir =>
    rcases List.mem_append.mp h with hl | hr
    · obtain ⟨q, hq, hT⟩ := il c (p ++ [false]) hl
      exact ⟨false :: q, by simpa [List.append_assoc] using hq, hT⟩
    · obtain ⟨q, hq, hT⟩ := ir _ (p ++ [true]) hr
      exact ⟨true :: q, by simpa [List.append_assoc] using hq, hT⟩

private theorem round_order (z : BirthStream) (epoch c : Nat) (p : Address) (t : Labelled) :
    (birthRound z epoch c p t).births.Pairwise chronologicallyBefore := by
  have hOrd := oldBetaAddresses_pairwise p t
  rw [← round_addresses z epoch c p t, List.pairwise_map] at hOrd
  apply hOrd.imp_of_mem
  intro e f he hf hl
  exact Or.inr ⟨(round_epoch_mark z _ _ _ _ e he).1.trans
    (round_epoch_mark z _ _ _ _ f hf).1.symm, hl⟩

private theorem clock_order (z : BirthStream) (n : Nat) :
    (physicalBirthClock z n).births.Pairwise chronologicallyBefore := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    let old := physicalBirthClock z n
    change (old.births ++ (birthRound z (n+1) old.cursor [] old.tree).births).Pairwise _
    rw [List.pairwise_append]
    refine ⟨ih, round_order _ _ _ _ _, fun e he f hf => Or.inl ?_⟩
    rw [(round_epoch_mark z _ _ _ _ f hf).1]
    exact Nat.lt_succ_of_le (clock_epoch_mark z n e he).1

private theorem exact_split_by_update (z : BirthStream) (n : Nat) :
    ∃ batch : List BirthEvent,
      (physicalBirthClock z (n+1)).births = (physicalBirthClock z n).births ++ batch ∧
      (∀ e ∈ batch, e.update = n+1) ∧
      (∀ e, e ∈ (physicalBirthClock z n).births ↔
        e ∈ (physicalBirthClock z (n+1)).births ∧ e.update < n+1) := by
  refine ⟨(birthRound z (n+1) (physicalBirthClock z n).cursor [] (physicalBirthClock z n).tree).births,
    rfl, fun e he => (round_epoch_mark z _ _ _ _ e he).1, ?_⟩
  intro e
  rw [← mature_prefix z n, List.mem_filter]
  simp only [decide_eq_true_eq]

/-- The physical chronological clock, from the fixed alpha seed and the source's
fixed birth stream. Each index and marked placement is attained by the actuator. -/
theorem physical_birth_clock (z : BirthStream) (n : Nat) :
    (∀ i (e : BirthEvent), (physicalBirthClock z n).births[i]? = some e →
      consume z i = e.mark ∧ e.serial = i + 1) ∧
    After n (physicalBirthClock z n).tree ∧
    Step (physicalBirthClock z n).tree (physicalBirthClock z (n+1)).tree ∧
    (physicalBirthClock z n).cursor = (physicalBirthClock z n).births.length ∧
    (physicalBirthClock z n).births.length = clockSum n ∧
    (physicalBirthClock z n).births.length = Nat.fib (n+1) - 1 ∧
    (physicalBirthClock z n).births.Pairwise chronologicallyBefore ∧
    (∃ batch : List BirthEvent,
      (physicalBirthClock z (n+1)).births = (physicalBirthClock z n).births ++ batch ∧
      (∀ e ∈ batch, e.update = n+1) ∧
      (∀ e, e ∈ (physicalBirthClock z n).births ↔
        e ∈ (physicalBirthClock z (n+1)).births ∧ e.update < n+1)) ∧
    (2 ≤ n →
      (physicalBirthClock z (n-1)).births.length = Nat.fib n - 1 ∧
      (physicalBirthClock z n).births.length -
        (physicalBirthClock z (n-1)).births.length = Nat.fib (n-1) ∧
      alphaLeaves (physicalBirthClock z n).tree = Nat.fib (n-1) ∧
      betaLeaves (physicalBirthClock z n).tree = Nat.fib n) ∧
    (let old := physicalBirthClock z n
     let r := birthRound z (n+1) old.cursor [] old.tree
     r.births.length = Nat.fib n ∧
     (r.births.map BirthEvent.parent).Nodup ∧
     (∀ p, p ∈ r.births.map BirthEvent.parent ↔ isBeta old.tree p = true) ∧
     (∀ e ∈ r.births, e.update = n+1 ∧ atTree r.tree e.parent =
       some (if e.mark then .mul beta alpha else .mul alpha beta))) ∧
    (∀ z' : BirthStream, (∀ j, 1 ≤ j → j ≤ (physicalBirthClock z n).cursor → z j = z' j) →
      physicalBirthClock z n = physicalBirthClock z' n) := by
  have h := clock_count z n
  refine ⟨clock_indexed z n, clock_after z n, round_step _ _ _ _ _,
    h.1.trans h.2.symm, h.2, h.2.trans (clockSum_eq_fib n),
    clock_order z n, exact_split_by_update z n, ?_, ?_, ?_⟩
  · intro hn
    cases n with
    | zero => omega
    | succ n =>
      rw [Nat.add_sub_cancel, (clock_count z n).2, (clock_count z (n+1)).2,
        clockSum_add_one, Nat.add_sub_cancel_left, clockSum_eq_fib]
      have hl := leafCounts_after (by omega) (clock_after z (n+1))
      exact ⟨rfl, rfl, hl.2, hl.1⟩
  · let old := physicalBirthClock z n
    let r := birthRound z (n+1) old.cursor [] old.tree
    change r.births.length = Nat.fib n ∧
      (r.births.map BirthEvent.parent).Nodup ∧
      (∀ p, p ∈ r.births.map BirthEvent.parent ↔ isBeta old.tree p = true) ∧ _
    rw [round_addresses]
    refine ⟨(round_size _ _ _ _ _).2.trans (leafCounts_after_shifted (clock_after z n)).1,
      oldBetaAddresses_nodup [] _, fun p => mem_oldBetaAddresses p _, ?_⟩
    intro e he
    obtain ⟨q, hq, hT⟩ := round_old_orientation z _ _ [] _ e he
    change e.parent = q at hq
    exact ⟨(round_epoch_mark z _ _ _ _ e he).1, hq.symm ▸ hT⟩
  · intro z' same
    exact clock_prefix z z' n (by simpa [h.1] using same)


#print axioms physical_birth_clock
end D5.S3.Arith.FibonacciAtomic.LocalWiring.PhysicalBirthClock
