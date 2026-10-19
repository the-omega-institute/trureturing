/- GID: D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeStationaryIntervalResources
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Sharp stationary actual-source interval capacities and joint literal resources. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceMass
import D5.S3.Arith.FibonacciAtomic.Observer.NativeClassRootSimulation
import D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.Kernel
import D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeStationaryIntervalResources

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open NativeRankedNavigationCompiler (pathCost)
open NativePassiveServiceRealization (Dialogue)
open NativeClassRootSimulation (nativeRun nativeDepth wordBound)
open Geometry.AncestorAreaInstability (T)
open Geometry.FiniteSourceMass (finite_source_masses)
open NativeSerialMachine

/-- Positive-source capacity, including the zero-call singleton. -/
def positiveCapacity (k : Nat) : Nat := 3 * 2^k - 2

/-- The actual zero-origin capacity has a distinct zero-call boundary. -/
def zeroCapacity (k : Nat) : Nat := if k = 0 then 1 else 3 * 2^k - 3

/-- A literal dialogue identifies the numeric age on every admitted source. -/
def Identifies (d : Dialogue Nat) (L U k : Nat) : Prop :=
  ∀ n, L ≤ n → n ≤ U →
    (nativeRun (fun a => readout a (T n)) d).1 = n ∧
    (nativeRun (fun a => readout a (T n)) d).2 ≤ k

private theorem actual_table (p : Address) (n : Nat) :
    readout p (T n) = if p = [] then
      (if n = 0 then .alpha else if n = 1 then .beta else .branch)
    else if pathCost p ≤ n ∧ pathCost p.dropLast + 2 ≤ n then
      (if n-pathCost p = 0 then .alpha else
        if n-pathCost p = 1 then .beta else .branch) else .absent := by
  by_cases hp : p = []
  · subst p
    simpa using (finite_source_masses.2.2.2.2.2.2.2.2 n).2
  · simp only [hp, ↓reduceIte]
    by_cases reach : pathCost p ≤ n ∧ pathCost p.dropLast + 2 ≤ n
    · rw [if_pos reach]
      exact finite_source_masses.2.2.2.2.2.2.1 n p
        (finite_source_masses.2.1 n p hp reach.1 reach.2).1
    · rw [if_neg reach]
      have no : subtree p (T n) = none := by
        cases hs : subtree p (T n) with
        | none => rfl
        | some u => exact (reach ((finite_source_masses.1 n p hp).mp ⟨u,hs⟩)).elim
      have h := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        p [] (T n)
      simpa [no] using h

private theorem leaf_age (p : Address) (n : Nat) :
    (readout p (T n) = .alpha → n = pathCost p) ∧
    (readout p (T n) = .beta → n = pathCost p + 1) := by
  rw [actual_table]
  by_cases hp : p = []
  · subst p
    simp only [↓reduceIte, pathCost]
    constructor <;> intro h <;> split_ifs at h <;> simp_all
  · simp only [hp, ↓reduceIte]
    constructor <;> intro h <;> split_ifs at h <;> simp_all <;> omega

private theorem nonroot_zero_one (p : Address) (hp : p ≠ []) :
    readout p (T 0) = .absent ∧ readout p (T 1) = .absent := by
  cases p with
  | nil => contradiction
  | cons b p => exact ⟨rfl,rfl⟩

private def cell (s : Finset Nat) (p : Address) (z : Reply) : Finset Nat :=
  s.filter (fun n => readout p (T n) = z)

private theorem cell_partition (s : Finset Nat) (p : Address) :
    s.card = (cell s p .alpha).card + (cell s p .beta).card +
      (cell s p .branch).card + (cell s p .absent).card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := s) (t := Finset.univ) (f := fun n => readout p (T n))
    (fun _ _ => Finset.mem_univ _)
  have univ : (Finset.univ : Finset Reply) = {.alpha,.beta,.branch,.absent} := rfl
  rw [univ] at h
  simpa [cell,add_assoc] using h

private theorem cell_leaf_card (s : Finset Nat) (p : Address) :
    (cell s p .alpha).card ≤ 1 ∧ (cell s p .beta).card ≤ 1 := by
  constructor
  · apply Finset.card_le_one.mpr
    intro a ha b hb
    exact (leaf_age p a).1 (Finset.mem_filter.mp ha).2 |>.trans
      ((leaf_age p b).1 (Finset.mem_filter.mp hb).2).symm
  · apply Finset.card_le_one.mpr
    intro a ha b hb
    exact (leaf_age p a).2 (Finset.mem_filter.mp ha).2 |>.trans
      ((leaf_age p b).2 (Finset.mem_filter.mp hb).2).symm

private theorem capacity_arithmetic (k : Nat) :
    1 ≤ positiveCapacity k ∧
    positiveCapacity (k+1) = 2 * positiveCapacity k + 2 ∧
    zeroCapacity (k+2) = zeroCapacity (k+1) + positiveCapacity (k+1) + 2 := by
  have pos : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
  simp only [positiveCapacity, zeroCapacity, Nat.succ_ne_zero, ↓reduceIte, pow_succ]
  omega

/-- The actual fixed-source chronological transcript of a finite dialogue. -/
def dialogueTrace {O : Type} : Dialogue O → Source → Trace
  | .stop _, _ => []
  | .read a A B C D, u =>
    let z := readout a u
    let tail := match z with
      | .alpha => dialogueTrace A u | .beta => dialogueTrace B u
      | .branch => dialogueTrace C u | .absent => dialogueTrace D u
    .read 0 a z :: tail

private def dialogueControl : Dialogue Nat → Op (Dialogue Nat) Nat
  | .stop o => .stop o
  | .read a A B C D => .read a
    (fun z => match z with | .alpha => A | .beta => B | .branch => C | .absent => D)

private theorem dialogue_run (d : Dialogue Nat) (u : Source) :
    Run dialogueControl d 0 u (dialogueTrace d u) (nativeRun (fun a => readout a u) d).1 ∧
    (answers (dialogueTrace d u)).length = (nativeRun (fun a => readout a u) d).2 := by
  induction d with
  | stop o => exact ⟨.stop rfl,rfl⟩
  | read a A B C D ihA ihB ihC ihD =>
    cases hz : readout a u <;> simp only [dialogueTrace, nativeRun, hz]
    · exact ⟨.read rfl hz ihA.1, by simpa [answers,reads] using congrArg Nat.succ ihA.2⟩
    · exact ⟨.read rfl hz ihB.1, by simpa [answers,reads] using congrArg Nat.succ ihB.2⟩
    · exact ⟨.read rfl hz ihC.1, by simpa [answers,reads] using congrArg Nat.succ ihC.2⟩
    · exact ⟨.read rfl hz ihD.1, by simpa [answers,reads] using congrArg Nat.succ ihD.2⟩

private def Separates {O : Type} (d : Dialogue O) (s : Finset Nat) (k : Nat) : Prop :=
  (∀ a ∈ s, ∀ b ∈ s, answers (dialogueTrace d (T a)) =
    answers (dialogueTrace d (T b)) → a = b) ∧
  ∀ n ∈ s, (answers (dialogueTrace d (T n))).length ≤ k

private theorem separated_stop {O : Type} (o : O) (s : Finset Nat) (k : Nat)
    (h : Separates (.stop o) s k) : s.card ≤ 1 :=
  Finset.card_le_one.mpr (fun a ha b hb => h.1 a ha b hb rfl)

private theorem separated_zero {O : Type} (d : Dialogue O) (s : Finset Nat)
    (h : Separates d s 0) : s.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  apply h.1 a ha b hb
  exact (List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (h.2 a ha))).trans
    (List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (h.2 b hb))).symm

private theorem separated_child {O : Type} (p : Address) (next : Reply → Dialogue O)
    (s : Finset Nat) (k : Nat)
    (h : Separates (.read p (next .alpha) (next .beta) (next .branch) (next .absent)) s (k + 1))
    (z : Reply) : Separates (next z) (cell s p z) k := by
  constructor
  · intro a ha b hb same
    obtain ⟨ha,za⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb,zb⟩ := Finset.mem_filter.mp hb
    apply h.1 a ha b hb
    cases z <;> simpa [dialogueTrace,answers,reads,za,zb] using same
  · intro n hn
    obtain ⟨hn,hz⟩ := Finset.mem_filter.mp hn
    have small := h.2 n hn
    cases z <;> simpa [dialogueTrace,answers,reads,hz] using small

private theorem positive_bound {O : Type} (k : Nat) (d : Dialogue O)
    (s : Finset Nat) (h : Separates d s k) : s.card ≤ positiveCapacity k := by
  induction k generalizing d s with
  | zero => simpa [positiveCapacity] using separated_zero d s h
  | succ k ih =>
    cases d with
    | stop o => exact (separated_stop o s (k+1) h).trans (capacity_arithmetic k.succ).1
    | read p A B C D =>
      let next : Reply → Dialogue O := fun z =>
        match z with | .alpha => A | .beta => B | .branch => C | .absent => D
      have tail (z : Reply) := separated_child p next s k h z
      have hb := ih C (cell s p .branch) (tail .branch)
      have hd := ih D (cell s p .absent) (tail .absent)
      have singles := cell_leaf_card s p
      have split := cell_partition s p
      rw [(capacity_arithmetic k).2.1]
      omega

private theorem zero_bound {O : Type} (k : Nat) (d : Dialogue O)
    (s : Finset Nat) (h : Separates d s k) (hz : 0 ∈ s) (ho : 1 ∈ s) :
    s.card ≤ zeroCapacity k := by
  induction k generalizing d s with
  | zero => simpa [zeroCapacity] using separated_zero d s h
  | succ k ih =>
    cases d with
    | stop o =>
      have single := separated_stop o s (k+1) h
      have eq := Finset.card_le_one.mp single 0 hz 1 ho
      omega
    | read p A B C D =>
      let next : Reply → Dialogue O := fun z =>
        match z with | .alpha => A | .beta => B | .branch => C | .absent => D
      have tail (z : Reply) := separated_child p next s k h z
      have hb := positive_bound k C (cell s p .branch) (tail .branch)
      have singles := cell_leaf_card s p
      have split := cell_partition s p
      by_cases hp : p = []
      · have empty : cell s p .absent = ∅ := by
          subst p
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro n hn
          have bad := (Finset.mem_filter.mp hn).2
          rw [actual_table] at bad
          split_ifs at bad; contradiction
        rw [empty,Finset.card_empty] at split
        cases k with
        | zero =>
          simp [positiveCapacity,zeroCapacity] at *
          omega
        | succ k => rw [(capacity_arithmetic k).2.2]; omega
      · have hz' : 0 ∈ cell s p .absent :=
          Finset.mem_filter.mpr ⟨hz,(nonroot_zero_one p hp).1⟩
        have ho' : 1 ∈ cell s p .absent :=
          Finset.mem_filter.mpr ⟨ho,(nonroot_zero_one p hp).2⟩
        have hd := ih D (cell s p .absent) (tail .absent) hz' ho'
        cases k with
        | zero =>
          have single := separated_zero D (cell s p .absent) (tail .absent)
          have eq := Finset.card_le_one.mp single 0 hz' 1 ho'
          omega
        | succ k => rw [(capacity_arithmetic k).2.2]; omega

private theorem separated_interval_bound {O : Type} (d : Dialogue O)
    (L U k : Nat) (hLU : L ≤ U) (sep : Separates d (Finset.Icc L U) k) :
    U-L+1 ≤ if L = 0 then zeroCapacity k else positiveCapacity k := by
  classical
  have card : (Finset.Icc L U).card = U-L+1 := by rw [Nat.card_Icc]; omega
  by_cases hz : L = 0
  · subst L
    simp only [↓reduceIte]
    by_cases hu : U = 0
    · subst U
      cases k with
      | zero => simp [zeroCapacity]
      | succ k =>
        have hpow : 2 ≤ 2^(k+1) := by
          simpa [pow_succ] using Nat.mul_le_mul_right 2 (Nat.one_le_pow k 2 (by decide))
        simp [zeroCapacity]
        omega
    · rw [← card]
      exact zero_bound k d _ sep (by simp) (by simp; omega)
  · simp only [hz,↓reduceIte]
    rw [← card]
    exact positive_bound k d _ sep

private theorem reachable_interval_capacity_induction (d : Dialogue Nat)
    (L U k : Nat) (hLU : L ≤ U) (correct : Identifies d L U k) :
    U-L+1 ≤ if L = 0 then zeroCapacity k else positiveCapacity k := by
  classical
  have sep : Separates d (Finset.Icc L U) k := by
    constructor
    · intro a ha b hb same
      obtain ⟨la,au⟩ := Finset.mem_Icc.mp ha
      obtain ⟨lb,bu⟩ := Finset.mem_Icc.mp hb
      have out := (NativeSerialImage.terminal_prefix_free
        (dialogue_run d (T a)).1 (dialogue_run d (T b)).1
        (by rw [same])).2
      simpa [(correct a la au).1,(correct b lb bu).1] using out
    · intro n hn
      obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hn
      rw [(dialogue_run d (T n)).2]
      exact (correct n lo hi).2
  exact separated_interval_bound d L U k hLU sep

/-- Materialized shortest right-ending query of a legal threshold. -/
def thresholdWord (t : Nat) : Address :=
  if t % 2 = 0 then DelayedOriginalReadout.rights (t/2)
  else false :: DelayedOriginalReadout.rights (t/2)

private theorem threshold_table (t n : Nat) (ht : 2 ≤ t) :
    (readout (thresholdWord t) (T n) = .absent ↔ n < t) ∧
    (readout (thresholdWord t) (T n) = .alpha ↔ n = t) ∧
    (readout (thresholdWord t) (T n) = .beta ↔ n = t+1) ∧
    (readout (thresholdWord t) (T n) = .branch ↔ t+2 ≤ n) := by
  have clock (j : Nat) : DelayedOriginalReadout.rightClock (T j) = j := by
    simpa [T,DelayedOriginalReadout.rightClock] using
      DelayedOriginalReadout.right_clock_iterate j (.of true)
  unfold thresholdWord
  split_ifs with he
  · have row := DelayedOriginalReadout.right_clock_readout (t/2) (T n)
    rw [clock] at row
    have et : t = 2 * (t/2) := by omega
    rw [← et] at row
    exact row
  · have odd : t = 2 * (t/2) + 1 := by omega
    have half : 1 ≤ t/2 := by omega
    cases n with
    | zero =>
      change (Reply.absent = .absent ↔ 0 < t) ∧ (Reply.absent = .alpha ↔ 0 = t) ∧
        (Reply.absent = .beta ↔ 0 = t+1) ∧ (Reply.absent = .branch ↔ t+2 ≤ 0)
      simp only [reduceCtorEq, false_iff, true_iff]
      exact ⟨by omega,by omega,trivial,by omega⟩
    | succ n => cases n with
      | zero =>
        change (Reply.absent = .absent ↔ 1 < t) ∧ (Reply.absent = .alpha ↔ 1 = t) ∧
          (Reply.absent = .beta ↔ 1 = t+1) ∧ (Reply.absent = .branch ↔ t+2 ≤ 1)
        simp only [reduceCtorEq, false_iff, true_iff]
        exact ⟨by omega,by omega,by omega,by omega⟩
      | succ n =>
        have pair := NativeRankedEqualityCompiler.atomic_pair n
        change T (n+2) = .mul (T (n+1)) (T n) at pair
        rw [pair]
        change (readout (DelayedOriginalReadout.rights (t/2)) (T (n+1)) = .absent ↔ _) ∧ _
        have row := DelayedOriginalReadout.right_clock_readout (t/2) (T (n+1))
        rw [clock] at row
        rcases row with ⟨ha,hb,hc,hd⟩
        exact ⟨ha.trans (by omega),hb.trans (by omega),hc.trans (by omega),hd.trans (by omega)⟩

private theorem threshold_length (t : Nat) :
    (thresholdWord t).length = (t+1)/2 := by
  unfold thresholdWord DelayedOriginalReadout.rights
  split_ifs <;> simp only [List.length_cons,List.length_replicate] <;> omega

/-- Balanced positive search tree with exactly the prescribed running nodes. -/
def plus : (r : Nat) → Nat → Dialogue Nat
  | 0, l => .stop l
  | r+1, l =>
    let a := r/2
    let b := r-a
    let t := l+3*a+1
    .read (thresholdWord t) (.stop t) (.stop (t+1)) (plus b (t+2)) (plus a l)
termination_by r => r

/-- The zero-origin tree uses a paid root query at its final zero branch. -/
def zero : (r : Nat) → Dialogue Nat
  | 0 => .stop 0
  | r+1 =>
    let a := r/2
    let b := r-a
    if a = 0 then .read [] (.stop 0) (.stop 1) (plus b 2) (.stop 0)
    else .read (thresholdWord (3*a)) (.stop (3*a)) (.stop (3*a+1))
      (plus b (3*a+2)) (zero a)
termination_by r => r

private theorem plus_correct (r l k : Nat) (hl : 1 ≤ l) (cap : r < 2 ^ k) :
    Identifies (plus r l) l (l+3*r) k := by
  induction k generalizing r l with
  | zero =>
    have hr : r = 0 := by simpa using cap
    subst r
    intro n lo hi
    have hn : n = l := by omega
    subst n
    simp [plus,nativeRun]
  | succ k ih =>
    cases r with
    | zero =>
      intro n lo hi
      have hn : n = l := by omega
      subst n
      simp [plus,nativeRun]
    | succ r =>
      have ha : r/2 < 2^k := by rw [pow_succ] at cap; omega
      have hb : r-r/2 < 2^k := by rw [pow_succ] at cap; omega
      have left := ih (r/2) l hl ha
      have right := ih (r-r/2) (l+3*(r/2)+3) (by omega) hb
      intro n lo hi
      have row := threshold_table (l+3*(r/2)+1) n (by omega)
      simp only [plus,nativeRun]
      cases hz : readout (thresholdWord (l+3*(r/2)+1)) (T n) with
      | alpha =>
        have hn := row.2.1.mp hz
        dsimp only
        exact ⟨hn.symm,by omega⟩
      | beta =>
        have hn := row.2.2.1.mp hz
        dsimp only
        exact ⟨hn.symm,by omega⟩
      | branch =>
        have hn := row.2.2.2.mp hz
        have answer := right n (by omega) (by omega)
        simpa only [hz,show l+3*(r/2)+1+2 = l+3*(r/2)+3 by omega] using
          And.intro answer.1 (Nat.succ_le_succ answer.2)
      | absent =>
        have hn := row.1.mp hz
        have answer := left n lo (by omega)
        simpa only [hz] using And.intro answer.1 (Nat.succ_le_succ answer.2)

private theorem zero_correct (r k : Nat) (hr : 1 ≤ r) (cap : r < 2 ^ k) :
    Identifies (zero r) 0 (3*r-1) k := by
  induction k generalizing r with
  | zero => simp at cap; omega
  | succ k ih =>
    obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    have ha : r/2 < 2^k := by rw [pow_succ] at cap; omega
    have hb : r-r/2 < 2^k := by rw [pow_succ] at cap; omega
    intro n lo hi
    simp only [zero]
    split_ifs with empty
    · have right := plus_correct (r-r/2) 2 k (by omega) hb
      have root := (finite_source_masses.2.2.2.2.2.2.2.2 n).2
      simp only [nativeRun,root]
      by_cases hn : n = 0
      · simp [hn]
      · by_cases ho : n = 1
        · simp [ho]
        · have answer := right n (by omega) (by omega)
          simpa [hn,ho] using And.intro answer.1 (Nat.succ_le_succ answer.2)
    · have left := ih (r/2) (by omega) ha
      have right := plus_correct (r-r/2) (3*(r/2)+2) k (by omega) hb
      have row := threshold_table (3*(r/2)) n (by omega)
      simp only [nativeRun]
      cases hz : readout (thresholdWord (3*(r/2))) (T n) with
      | alpha =>
        have hn := row.2.1.mp hz
        dsimp only
        exact ⟨hn.symm,by omega⟩
      | beta =>
        have hn := row.2.2.1.mp hz
        dsimp only
        exact ⟨hn.symm,by omega⟩
      | branch =>
        have hn := row.2.2.2.mp hz
        have answer := right n (by omega) (by omega)
        simpa only [hz] using And.intro answer.1 (Nat.succ_le_succ answer.2)
      | absent =>
        have hn := row.1.mp hz
        have answer := left n (by omega) (by omega)
        simpa only [hz] using And.intro answer.1 (Nat.succ_le_succ answer.2)

private theorem finite_capacity_iff (L U k : Nat) (hLU : L ≤ U) :
    (∃ d : Dialogue Nat, Identifies d L U k) ↔
      U-L+1 ≤ if L = 0 then zeroCapacity k else positiveCapacity k := by
  constructor
  · rintro ⟨d,hd⟩
    exact reachable_interval_capacity_induction d L U k hLU hd
  · intro cap
    by_cases single : L = U
    · refine ⟨.stop L,fun n lo hi => ?_⟩
      have hn : n = L := by omega
      subst n
      exact ⟨rfl,Nat.zero_le _⟩
    · by_cases hz : L = 0
      · subst L
        simp only [↓reduceIte,Nat.sub_zero] at cap
        have hk : k ≠ 0 := by intro eq; subst k; simp [zeroCapacity] at cap; omega
        have jr : 1 ≤ (U+3)/3 := by omega
        have jc : (U+3)/3 < 2^k := by simp only [zeroCapacity,if_neg hk] at cap; omega
        refine ⟨zero ((U+3)/3),fun n lo hi => ?_⟩
        exact zero_correct _ _ jr jc n lo (by omega)
      · simp only [hz,↓reduceIte] at cap
        have powpos := (capacity_arithmetic k).1
        have jc : (U-L+2)/3 < 2^k := by unfold positiveCapacity at cap; omega
        refine ⟨plus ((U-L+2)/3) L,fun n lo hi => ?_⟩
        exact plus_correct _ _ _ (by omega) jc n lo (by omega)

/-- Source-blind native control may perform silent computation but no update. -/
def Stationary {C O : Type} (δ : C → Op C O) : Prop :=
  ∀ c c', δ c ≠ .applyRho c'

private def Total {C O : Type} (δ : C → Op C O) (c : C) (s : Finset Nat) (k : Nat) : Prop :=
  ∀ n ∈ s, ∃ t o, Run δ c 0 (T n) t o ∧ (answers t).length ≤ k

private theorem local_total {C O : Type} (δ : C → Op C O) (c c' : C)
    (s : Finset Nat) (k : Nat) (action : δ c = .localStep c')
    (total : Total δ c s k) : Total δ c' s k := by
  intro n hn
  obtain ⟨t,o,run,budget⟩ := total n hn
  cases run with
  | stop h => cases action.symm.trans h
  | localStep h tail =>
    cases Op.localStep.inj (action.symm.trans h)
    exact ⟨_,o,tail,by simpa [answers,reads] using budget⟩
  | update h tail => cases action.symm.trans h
  | read h hy tail => cases action.symm.trans h

private theorem read_total {C O : Type} (δ : C → Op C O) (c : C)
    (p : Address) (next : Reply → C) (s : Finset Nat) (k : Nat)
    (action : δ c = .read p next) (total : Total δ c s (k + 1)) (z : Reply) :
    Total δ (next z) (cell s p z) k := by
  intro n hn
  obtain ⟨hn,hz⟩ := Finset.mem_filter.mp hn
  obtain ⟨t,o,run,budget⟩ := total n hn
  cases run with
  | stop h => cases action.symm.trans h
  | localStep h tail => cases action.symm.trans h
  | update h tail => cases action.symm.trans h
  | read h hy tail =>
    obtain ⟨hp,hnext⟩ := Op.read.inj (action.symm.trans h)
    cases hp
    cases hnext
    have eq := hy.symm.trans hz
    cases eq
    exact ⟨_,o,tail,by simpa [answers,reads] using budget⟩

private theorem serial_unroll {C O : Type} (δ : C → Op C O) (quiet : Stationary δ)
    (fallback : O) (k : Nat) (c : C) (s : Finset Nat) (total : Total δ c s k) :
    ∃ d : Dialogue O, ∀ n ∈ s, ∃ t o, Run δ c 0 (T n) t o ∧
      nativeRun (fun a => readout a (T n)) d = (o,(answers t).length) ∧
      answers (dialogueTrace d (T n)) = answers t := by
  classical
  induction k using Nat.strong_induction_on generalizing c s with
  | h k ihBudget =>
    have normalize {c : C} {e : Nat} {u : Source} {t : Trace} {o : O}
        (run : Run δ c e u t o) :
        ∀ s : Finset Nat, Total δ c s k →
          ∃ d : Dialogue O, ∀ n ∈ s, ∃ ts out, Run δ c 0 (T n) ts out ∧
            nativeRun (fun a => readout a (T n)) d = (out,(answers ts).length) ∧
            answers (dialogueTrace d (T n)) = answers ts := by
      induction run with
      | @stop c e r o action =>
        intro s total
        exact ⟨.stop o,fun n hn => ⟨[],o,.stop action,rfl,rfl⟩⟩
      | @localStep c c' e r t o action tail ih =>
        intro s total
        obtain ⟨d,hd⟩ := ih s (local_total δ c c' s k action total)
        refine ⟨d,fun n hn => ?_⟩
        obtain ⟨ts,z,run,eval,trace⟩ := hd n hn
        exact ⟨.localStep::ts,z,.localStep action run,eval,trace⟩
      | update action tail ih => exact False.elim (quiet _ _ action)
      | @read c e r p next z t o action hz tail ih =>
        intro s total
        cases k with
        | zero =>
          have impossible : s = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro j hj
            obtain ⟨ts,out,other,budget⟩ := total j hj
            cases other with
            | stop h => cases action.symm.trans h
            | localStep h tail => cases action.symm.trans h
            | update h tail => cases action.symm.trans h
            | read h hy tail => simp [answers,reads] at budget
          exact ⟨.stop fallback,by simp [impossible]⟩
        | succ k =>
          have children (z : Reply) := ihBudget k (by omega) (next z) (cell s p z)
            (read_total δ c p next s k action total z)
          choose d hd using children
          refine ⟨.read p (d .alpha) (d .beta) (d .branch) (d .absent),fun n hn => ?_⟩
          obtain ⟨ts,out,run,eval,trace⟩ := hd (readout p (T n)) n
            (Finset.mem_filter.mpr ⟨hn,rfl⟩)
          refine ⟨.read 0 p (readout p (T n))::ts,out,.read action rfl run,?_,?_⟩
          · cases hr : readout p (T n) <;>
              simpa [nativeRun,hr,answers,reads] using
                congrArg (fun v : O × Nat => (v.1,v.2+1)) eval
          · cases hr : readout p (T n) <;>
              simpa [dialogueTrace,hr,answers,reads] using
                congrArg (List.cons (readout p (T n))) trace
    by_cases empty : s = ∅
    · exact ⟨.stop fallback,by simp [empty]⟩
    obtain ⟨n,hn⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    obtain ⟨t,o,run,_⟩ := total n hn
    exact normalize run s total

/-- Correct native serial executions with every actual call charged. -/
def SerialCorrect {C : Type} (δ : C → Op C Nat) (c : C) (L U k : Nat) : Prop :=
  ∀ n, L ≤ n → n ≤ U → ∃ t, Run δ c 0 (T n) t n ∧ (answers t).length ≤ k

private theorem serial_correct_tree {C : Type} (δ : C → Op C Nat)
    (quiet : Stationary δ) (c : C) (L U k : Nat) (correct : SerialCorrect δ c L U k) :
    ∃ d : Dialogue Nat, Identifies d L U k := by
  classical
  have total : Total δ c (Finset.Icc L U) k := by
    intro n hn
    obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hn
    obtain ⟨t,run,budget⟩ := correct n lo hi
    exact ⟨t,n,run,budget⟩
  obtain ⟨d,hd⟩ := serial_unroll δ quiet L k c _ total
  refine ⟨d,fun n lo hi => ?_⟩
  obtain ⟨t,o,run,eval,_⟩ := hd n (Finset.mem_Icc.mpr ⟨lo,hi⟩)
  obtain ⟨other,run',budget⟩ := correct n lo hi
  have eq := NativeSerialDepth.run_unique run run'
  rw [eval,eq.1,eq.2]
  exact ⟨rfl,budget⟩

private theorem dialogue_stationary : Stationary dialogueControl := by
  intro c c' h
  cases c <;> cases h

/-- The exact integer-valued logarithmic call price. -/
noncomputable def minimumCalls (L U : Nat) : Nat :=
  if L = U then 0 else Nat.ceil (Real.logb 2
    ((((U-L+1 : Nat) : ℝ) + if L = 0 then 3 else 2) / 3))

private theorem log_capacity (N c k : Nat) (hc : 0 < c) :
    Nat.ceil (Real.logb 2 (((N : ℝ)+c)/3)) ≤ k ↔ N+c ≤ 3*2^k := by
  rw [Nat.ceil_le,Real.logb_le_iff_le_rpow (by norm_num) (by positivity),Real.rpow_natCast]
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3)]
  norm_cast
  omega

private theorem minimum_calls_capacity (L U k : Nat) (hLU : L ≤ U) :
    minimumCalls L U ≤ k ↔
      U-L+1 ≤ if L = 0 then zeroCapacity k else positiveCapacity k := by
  unfold minimumCalls
  by_cases single : L = U
  · subst U
    simp only [↓reduceIte,Nat.sub_self,Nat.zero_add,Nat.zero_le,true_iff]
    have pos := (capacity_arithmetic k).1
    by_cases hz : L = 0
    · simp only [hz,↓reduceIte]
      cases k with
      | zero => simp [zeroCapacity]
      | succ k =>
        have powpos : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
        simp [zeroCapacity,pow_succ]
        omega
    · simp only [hz,↓reduceIte]
      omega
  · simp only [single,↓reduceIte]
    by_cases hz : L = 0
    · simp only [hz,↓reduceIte]
      have law := log_capacity (U-0+1) 3 k (by decide)
      norm_num only [Nat.cast_ofNat] at law
      rw [law]
      cases k with
      | zero => simp [zeroCapacity]; omega
      | succ k => simp only [zeroCapacity,Nat.succ_ne_zero,↓reduceIte]; omega
    · simp only [hz,↓reduceIte]
      have law := log_capacity (U-L+1) 2 k (by decide)
      norm_num only [Nat.cast_ofNat] at law
      rw [law]
      have pos := (capacity_arithmetic k).1
      unfold positiveCapacity at *
      omega

private theorem fixed_source_collision {C O : Type} (δ : C → Op C O)
    (quiet : Stationary δ) (fallback : O) (c : C) (L U k : Nat)
    (hLU : L ≤ U) (small : k < minimumCalls L U)
    (total : Total δ c (Finset.Icc L U) k) :
    ∃ a ∈ Finset.Icc L U, ∃ b ∈ Finset.Icc L U, a ≠ b ∧
      ∃ t o, Run δ c 0 (T a) t o ∧ Run δ c 0 (T b) t o := by
  classical
  obtain ⟨d,hd⟩ := serial_unroll δ quiet fallback k c _ total
  by_contra absent
  have sep : Separates d (Finset.Icc L U) k := by
    constructor
    · intro a ha b hb same
      by_contra distinct
      obtain ⟨ta,oa,ra,_,ea⟩ := hd a ha
      obtain ⟨tb,ob,rb,_,eb⟩ := hd b hb
      have eq := NativeSerialImage.terminal_prefix_free ra rb (by rw [← ea,← eb,same])
      exact absent ⟨a,ha,b,hb,distinct,ta,oa,ra,by simpa [eq.1,eq.2] using rb⟩
    · intro n hn
      obtain ⟨t,o,run,eval,trace⟩ := hd n hn
      obtain ⟨ts,out,original,budget⟩ := total n hn
      have eq := NativeSerialDepth.run_unique run original
      rw [trace,eq.1]
      exact budget
  have cap := separated_interval_bound d L U k hLU sep
  exact (Nat.not_le_of_lt small) ((minimum_calls_capacity L U k hLU).mpr cap)

/-- Exact stationary capacity, its logarithmic minimum, and a finite attaining
literal tree. Silent native computation does not grant a source query. -/
theorem native_interval_capacity (L U : Nat) (hLU : L ≤ U) :
    (∀ k, (∃ (C : Type) (δ : C → Op C Nat) (c : C),
        Stationary δ ∧ SerialCorrect δ c L U k) ↔
      U-L+1 ≤ if L = 0 then zeroCapacity k else positiveCapacity k) ∧
    (∀ k, (∃ d : Dialogue Nat, Identifies d L U k) ↔ minimumCalls L U ≤ k) ∧
    (∃ d : Dialogue Nat, Identifies d L U (minimumCalls L U)) ∧
    (∀ (C O : Type) (δ : C → Op C O) (c : C) (_fallback : O) (k : Nat),
      Stationary δ → k < minimumCalls L U →
      (∀ n, L ≤ n → n ≤ U → ∃ t o, Run δ c 0 (T n) t o ∧ (answers t).length ≤ k) →
      ∃ a ∈ Finset.Icc L U, ∃ b ∈ Finset.Icc L U, a ≠ b ∧
        ∃ t o, Run δ c 0 (T a) t o ∧ Run δ c 0 (T b) t o) := by
  have finite (k : Nat) := finite_capacity_iff L U k hLU
  refine ⟨?_,?_,?_,?_⟩
  · intro k
    constructor
    · rintro ⟨C,δ,c,quiet,correct⟩
      exact (finite k).mp (serial_correct_tree δ quiet c L U k correct)
    · intro cap
      obtain ⟨d,hd⟩ := (finite k).mpr cap
      refine ⟨Dialogue Nat,dialogueControl,d,dialogue_stationary,fun n lo hi => ?_⟩
      refine ⟨dialogueTrace d (T n),?_,?_⟩
      · simpa [(hd n lo hi).1] using (dialogue_run d (T n)).1
      · rw [(dialogue_run d (T n)).2]
        exact (hd n lo hi).2
  · intro k
    exact (finite k).trans (minimum_calls_capacity L U k hLU).symm
  · exact (finite _).mpr ((minimum_calls_capacity L U _ hLU).mp le_rfl)
  · intro C O δ c fallback k quiet small total
    apply fixed_source_collision δ quiet fallback c L U k hLU small
    intro n hn
    obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hn
    exact total n lo hi

private theorem cost_append (p q : Address) : pathCost (p ++ q) = pathCost p + pathCost q := by
  induction p with
  | nil => simp [pathCost]
  | cons b p ih => cases b <;> simp [pathCost,ih,Nat.add_assoc]

private theorem normalized_query (p : Address) (hp : p ≠ []) :
    ∃ t : Nat, 2 ≤ t ∧ (thresholdWord t).length ≤ p.length ∧
      (∀ n, n < t → readout p (T n) = .absent) ∧
      ∃ phi : Reply → Reply, ∀ n,
        readout p (T n) = phi (readout (thresholdWord t) (T n)) := by
  let a := p.dropLast
  let b := p.getLast hp
  have shape : p = a ++ [b] := (List.dropLast_concat_getLast hp).symm
  have cost : pathCost p = pathCost a + if b then 2 else 1 := by
    rw [shape,cost_append]; simp [pathCost]
  have len : p.length = a.length+1 := by rw [shape,List.length_append]; rfl
  let t := pathCost a + 2
  have ht : 2 ≤ t := by omega
  refine ⟨t,ht,?_,?_,?_⟩
  · rw [threshold_length,len]
    have bound := (NativeFiniteMenuObstruction.path_bounds a).1
    dsimp [t]
    omega
  · intro n hn
    rw [actual_table,if_neg hp]
    have no : ¬ (pathCost p ≤ n ∧ pathCost p.dropLast+2 ≤ n) := by
      dsimp [t,a] at hn
      omega
    rw [if_neg no]
  · refine ⟨(fun z => if b then z else
        match z with
        | .alpha => .beta | .beta => .branch | .branch => .branch | .absent => .absent),?_⟩
    intro n
    have row := threshold_table t n ht
    rw [actual_table,if_neg hp]
    change (if pathCost p ≤ n ∧ pathCost a+2 ≤ n then _ else _) = _
    rw [cost]
    cases b <;> simp only [↓reduceIte] <;>
      cases hz : readout (thresholdWord t) (T n)
    all_goals
      first | have hn := row.1.mp hz | have hn := row.2.1.mp hz |
        have hn := row.2.2.1.mp hz | have hn := row.2.2.2.mp hz
      dsimp [t] at hn
      split_ifs <;> simp_all <;> omega

/-- On a declared bounded domain each literal is simulated by one paid
literal whose length is no larger than either the old length or the peak. -/
theorem bounded_query_recode (U : Nat) (_hU : 1 ≤ U) (p : Address) :
    ∃ (q : Address) (phi : Reply → Reply), q.length ≤ min p.length ((U-1)/2) ∧
      ∀ n, n ≤ U → readout p (T n) = phi (readout q (T n)) := by
  let m := (U-1)/2
  by_cases short : p.length ≤ m
  · exact ⟨p,id,by simp [short,m],fun n hn => rfl⟩
  by_cases small : U ≤ 2
  · refine ⟨[],(fun z : Reply => match z with
        | .alpha => readout p (T 0)
        | .beta => readout p (T 1)
        | .branch => readout p (T 2)
        | .absent => .absent),by simp,?_⟩
    intro n hn
    have hn2 : n ≤ 2 := le_trans hn small
    have root := (finite_source_masses.2.2.2.2.2.2.2.2 n).2
    rw [root]
    interval_cases n <;> rfl
  have hp : p ≠ [] := by intro eq; subst p; simp at short
  obtain ⟨t,ht,len,below,phi,decode⟩ := normalized_query p hp
  by_cases short' : (thresholdWord t).length ≤ m
  · exact ⟨thresholdWord t,phi,le_min len short',fun n hn => decode n⟩
  have mt : 2*m < t := by rw [threshold_length] at short'; omega
  have mp : 1 ≤ m := by dsimp [m]; omega
  have mu : U ≤ 2*m+2 := by dsimp [m]; omega
  refine ⟨DelayedOriginalReadout.rights m,
    (fun z : Reply => match z with
      | .absent => .absent
      | .alpha => readout p (T (2*m))
      | .beta => readout p (T (2*m+1))
      | .branch => readout p (T (2*m+2))),?_,?_⟩
  · simp only [DelayedOriginalReadout.rights,List.length_replicate]
    exact le_min (by omega) le_rfl
  · intro n hn
    have clock : DelayedOriginalReadout.rightClock (T n) = n := by
      simpa [T,DelayedOriginalReadout.rightClock] using
        DelayedOriginalReadout.right_clock_iterate n (.of true)
    have row := DelayedOriginalReadout.right_clock_readout m (T n)
    rw [clock] at row
    cases hz : readout (DelayedOriginalReadout.rights m) (T n) with
    | absent => exact below n (by have := row.1.mp hz; omega)
    | alpha => have eq := row.2.1.mp hz; simp [eq]
    | beta => have eq := row.2.2.1.mp hz; simp [eq]
    | branch => have eq : n = 2*m+2 := by have := row.2.2.2.mp hz; omega
                simp [eq]

private theorem recode_dialogue (U : Nat) (hU : 1 ≤ U) (d : Dialogue Nat) :
    ∃ e : Dialogue Nat, wordBound e ≤ (U-1)/2 ∧
      ∀ n, n ≤ U → nativeRun (fun p => readout p (T n)) e =
        nativeRun (fun p => readout p (T n)) d := by
  induction d with
  | stop o => exact ⟨.stop o,Nat.zero_le _,fun n hn => rfl⟩
  | read p A B C D ihA ihB ihC ihD =>
    obtain ⟨A',ba,ea⟩ := ihA
    obtain ⟨B',bb,eb⟩ := ihB
    obtain ⟨C',bc,ec⟩ := ihC
    obtain ⟨D',bd,ed⟩ := ihD
    obtain ⟨q,phi,bq,eq⟩ := bounded_query_recode U hU p
    let next : Reply → Dialogue Nat := fun z =>
      match z with | .alpha => A' | .beta => B' | .branch => C' | .absent => D'
    have bounds (z : Reply) : wordBound (next z) ≤ (U-1)/2 := by
      cases z <;> assumption
    refine ⟨.read q (next (phi .alpha)) (next (phi .beta))
      (next (phi .branch)) (next (phi .absent)),?_,?_⟩
    · simp only [wordBound,max_le_iff]
      exact ⟨bq.trans (min_le_right _ _),⟨bounds _,bounds _⟩,bounds _,bounds _⟩
    · intro n hn
      have decode := eq n hn
      have childs (z : Reply) : nativeRun (fun p => readout p (T n)) (next z) =
          nativeRun (fun p => readout p (T n))
            (match z with | .alpha => A | .beta => B | .branch => C | .absent => D) := by
        cases z <;> exact (by first | exact ea n hn | exact eb n hn | exact ec n hn | exact ed n hn)
      cases hz : readout q (T n) <;> simp only [nativeRun,hz,decode]
      all_goals rw [childs]; split <;> simp_all

/-- Every actually submitted literal respects the declared peak. -/
def Peak (t : Trace) (d : Nat) : Prop :=
  ∀ e a z, Event.read e a z ∈ t → a.length ≤ d

private theorem dialogue_peak (d : Dialogue Nat) (u : Source) :
    Peak (dialogueTrace d u) (wordBound d) := by
  induction d with
  | stop o => simp [Peak,dialogueTrace]
  | read p A B C D ihA ihB ihC ihD =>
    intro e a z hm
    have localBound : p.length ≤ wordBound (.read p A B C D) := le_max_left _ _
    have childBound (v : Nat) (hv : v ≤ max (max (wordBound A) (wordBound B))
        (max (wordBound C) (wordBound D))) : v ≤ wordBound (.read p A B C D) :=
      hv.trans (le_max_right _ _)
    cases hz : readout p u <;> simp only [dialogueTrace,hz,List.mem_cons] at hm
    all_goals rcases hm with eq | hm
    all_goals first
      | cases eq; exact localBound
      | exact childBound _ ((ihA e a z hm).trans ((le_max_left _ _).trans (le_max_left _ _)))
      | exact childBound _ ((ihB e a z hm).trans ((le_max_right _ _).trans (le_max_left _ _)))
      | exact childBound _ ((ihC e a z hm).trans ((le_max_left _ _).trans (le_max_right _ _)))
      | exact childBound _ ((ihD e a z hm).trans ((le_max_right _ _).trans (le_max_right _ _)))

private theorem high_transfer {C O : Type} (δ : C → Op C O) (quiet : Stationary δ)
    (d : Nat) {c : C} {e : Nat} {u : Source} {t : Trace} {o : O}
    (run : Run δ c e u t o) :
    ∀ n m, u = T n → 2*d+2 ≤ n → 2*d+2 ≤ m → Peak t d →
      Run δ c e (T m) t o := by
  induction run with
  | stop action => intro n m eq hn hm peak; exact .stop action
  | localStep action tail ih =>
    intro n m eq hn hm peak
    exact .localStep action (ih n m eq hn hm (fun e a z hz => peak e a z (by simp [hz])))
  | update action tail ih => exact (quiet _ _ action).elim
  | @read c e u p next z t o action hz tail ih =>
    intro n m eq hn hm peak
    have hp := peak e p z (by simp)
    have cost := (NativeFiniteMenuObstruction.path_bounds p).1
    have zn : readout p u = .branch := by
      rw [eq]; exact Kernel.branch_after p (.of true) n (by omega)
    have zm : readout p (T m) = .branch :=
      Kernel.branch_after p (.of true) m (by omega)
    exact .read action (zm.trans (zn.symm.trans hz))
      (ih n m eq hn hm (fun e a z hz => peak e a z (by simp [hz])))

/-- Simultaneous chronological call and submitted-word bounds. -/
def SerialBudgets {C : Type} (δ : C → Op C Nat) (c : C) (L U k d : Nat) : Prop :=
  ∀ n, L ≤ n → n ≤ U → ∃ t, Run δ c 0 (T n) t n ∧
    (answers t).length ≤ k ∧ Peak t d

/-- Exact joint call/peak feasibility, with a single finite dialogue attaining
both coordinate minima. -/
theorem native_interval_joint_optimum (L U : Nat) (hLU : L ≤ U) :
    (∀ k d, (∃ (C : Type) (δ : C → Op C Nat) (c : C),
      Stationary δ ∧ SerialBudgets δ c L U k d) ↔
      minimumCalls L U ≤ k ∧ (L = U ∨ U ≤ 2*d+2)) ∧
    (∃ e : Dialogue Nat, Identifies e L U (minimumCalls L U) ∧
      wordBound e ≤ if L = U then 0 else (U-1)/2) := by
  have attained : ∃ e : Dialogue Nat, Identifies e L U (minimumCalls L U) ∧
      wordBound e ≤ if L = U then 0 else (U-1)/2 := by
    by_cases single : L = U
    · refine ⟨.stop L,?_,by simp [wordBound,single]⟩
      intro n lo hi
      have eq : n = L := by omega
      exact ⟨eq.symm,Nat.zero_le _⟩
    · obtain ⟨d,hd⟩ := (native_interval_capacity L U hLU).2.2.1
      obtain ⟨e,peak,eval⟩ := recode_dialogue U (by omega) d
      refine ⟨e,?_,by simpa [single] using peak⟩
      intro n lo hi
      rw [eval n hi]
      exact hd n lo hi
  refine ⟨?_,attained⟩
  intro k d
  constructor
  · rintro ⟨C,δ,c,quiet,correct⟩
    have serial : SerialCorrect δ c L U k := by
      intro n lo hi
      obtain ⟨t,run,budget,peak⟩ := correct n lo hi
      exact ⟨t,run,budget⟩
    have calls := (minimum_calls_capacity L U k hLU).mpr
      ((native_interval_capacity L U hLU).1 k |>.mp ⟨C,δ,c,quiet,serial⟩)
    refine ⟨calls,?_⟩
    by_contra bad
    have high : 2*d+2 ≤ U-1 := by omega
    obtain ⟨ta,ra,_,pa⟩ := correct (U-1) (by omega) (by omega)
    obtain ⟨tb,rb,_,_⟩ := correct U hLU le_rfl
    have transfer := high_transfer δ quiet d ra (U-1) U rfl high (by omega) pa
    have same := (NativeSerialDepth.run_unique transfer rb).2
    omega
  · rintro ⟨calls,peak⟩
    obtain ⟨e,correct,words⟩ := attained
    have bound : wordBound e ≤ d := by
      rcases peak with single | upper
      · have empty : wordBound e = 0 := by simpa [single] using words
        rw [empty]; exact Nat.zero_le d
      · by_cases single : L = U
        · have empty : wordBound e = 0 := by simpa [single] using words
          rw [empty]; exact Nat.zero_le d
        · simp only [single,↓reduceIte] at words
          exact words.trans (by omega)
    refine ⟨Dialogue Nat,dialogueControl,e,dialogue_stationary,fun n lo hi => ?_⟩
    refine ⟨dialogueTrace e (T n),?_,?_,?_⟩
    · simpa [(correct n lo hi).1] using (dialogue_run e (T n)).1
    · rw [(dialogue_run e (T n)).2]; exact (correct n lo hi).2.trans calls
    · intro e' a z hm
      exact (dialogue_peak e (T n) e' a z hm).trans bound

#print axioms native_interval_capacity
#print axioms bounded_query_recode
#print axioms native_interval_joint_optimum

end D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu.NativeStationaryIntervalResources
