/- GID: D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.claim; result=D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.result; claim=D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.claim
   digest: Every finite two-layer RESOCA 115 nine-step return on the integer line is a three-step return. -/

import Init.Data.BitVec.Lemmas
import Init.Data.List.FinRange
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Notation
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Order.SuccPred.Int
import Mathlib.Order.SuccPred.Relation


namespace D5.S3.StatisticalMechanics.CellularAutomata
/-!
# Rule 115 and Formenti–Kamilya Question 1

   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.claim; result=D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.result; claim=D5/S3/StatisticalMechanics/CellularAutomata/FormentiKamilyaRule115.claim

The finite checks concern nine-bit time columns. Directed closure from the left
background and predecessor closure from the right background apply on the full
integer lattice. The certificate excludes least period nine for finite initial support.

Source: Formenti–Kamilya, arXiv:2606.13159v1, Question 1, p. 97.
-/

namespace FormentiKamilyaRule115

/-- The past and current layers, in that order. -/
abbrev Config := (ℤ → Bool) × (ℤ → Bool)

/-- The reversible second-order update with elementary rule 115. -/
def step (s : Config) : Config :=
  (s.2, fun i =>
    Bool.xor (s.1 i) (!(s.2 i) || (s.2 (i - 1) && !(s.2 (i + 1)))))

/-- Both layers have finite support, expressed with a common spatial bound. -/
private def FiniteConfig (s : Config) : Prop :=
  ∃ M : ℤ, ∀ i : ℤ, i < -M ∨ M < i → s.1 i = false ∧ s.2 i = false

def zeroConfig : Config := (fun _ => false, fun _ => false)

private theorem past_at_succ (s : Config) (n : ℕ) :
    (step^[n + 1] s).1 = (step^[n] s).2 := by
  rw [Function.iterate_succ_apply']
  rfl

private theorem current_at_succ (s : Config) (n : ℕ) (i : ℤ) :
    (step^[n + 1] s).2 i =
      Bool.xor ((step^[n] s).1 i)
        (!((step^[n] s).2 i) || ((step^[n] s).2 (i - 1) && !((step^[n] s).2 (i + 1)))) := by
  rw [Function.iterate_succ_apply']
  rfl

theorem zero_period_three :
    step^[3] zeroConfig = zeroConfig ∧
      ∀ q : ℕ, 0 < q → q < 3 → step^[q] zeroConfig ≠ zeroConfig := by
  refine ⟨rfl, ?_⟩
  intro q hpos hlt
  have hphase : q = 1 ∨ q = 2 := by omega
  rcases hphase with rfl | rfl
  · intro heq
    have hcurrent : true = false := congrArg (fun s : Config => s.2 0) heq
    cases hcurrent
  · intro heq
    have hpast : true = false := congrArg (fun s : Config => s.1 0) heq
    cases hpast

private theorem zero_current (n : ℕ) (i : ℤ) :
    (step^[n] zeroConfig).2 i = (n % 3 == 1) := by
  have hphase : step^[n] zeroConfig = step^[n % 3] zeroConfig := calc
    step^[n] zeroConfig = step^[n % 3 + 3 * (n / 3)] zeroConfig :=
      congrArg (fun k : ℕ => step^[k] zeroConfig) (Nat.mod_add_div n 3).symm
    _ = step^[n % 3] zeroConfig := by
      rw [Function.iterate_add_apply, Function.iterate_mul,
        Function.iterate_fixed zero_period_three.1]
  rw [hphase]
  have hlt : n % 3 < 3 := Nat.mod_lt n (by decide)
  generalize n % 3 = r at hlt ⊢
  have hrs : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases hrs with rfl | rfl | rfl <;> rfl

/-- At time n, the two layers agree with the uniform orbit outside the original bound plus n. -/
private theorem finite_propagation (s : Config) (M : ℤ)
    (hM : ∀ i : ℤ, i < -M ∨ M < i → s.1 i = false ∧ s.2 i = false)
    (n : ℕ) (i : ℤ) (hi : i < -(M + (n : ℤ)) ∨ M + (n : ℤ) < i) :
    (step^[n] s).1 i = (step^[n] zeroConfig).1 i ∧
      (step^[n] s).2 i = (step^[n] zeroConfig).2 i := by
  induction n generalizing i with
  | zero =>
    exact hM i (by omega)
  | succ n ih =>
    have hcenter := ih i (by omega)
    have hleft := ih (i - 1) (by omega)
    have hright := ih (i + 1) (by omega)
    constructor
    · simpa only [past_at_succ] using hcenter.2
    · rw [current_at_succ s n, current_at_succ zeroConfig n,
        hcenter.1, hcenter.2, hleft.2, hright.2]

/-- The current layer at the nine times represented by Fin 9. -/
private def column (s : Config) (i : ℤ) (t : Fin 9) : Bool :=
  (step^[t.val] s).2 i

private theorem current_eight_eq_past (s : Config) (h9 : step^[9] s = s) :
    (step^[8] s).2 = s.1 :=
  (past_at_succ s 8).symm.trans (congrArg Prod.fst h9)

private theorem column_cyclic (s : Config) (h9 : step^[9] s = s)
    (i : ℤ) (t : Fin 9) :
    Bool.xor (column s i (t + 8)) (column s i (t + 1)) =
      (!(column s i t) || (column s (i - 1) t && !(column s (i + 1) t))) := by
  have ht : t.val < 9 := t.isLt
  have hprev : column s i (t + 8) = (step^[t.val] s).1 i := by
    change (step^[(t.val + 8) % 9] s).2 i = _
    by_cases h : t.val = 0
    · rw [h]
      exact congrFun (current_eight_eq_past s h9) i
    · have hindex : (t.val + 8) % 9 + 1 = t.val := by omega
      exact (congrFun (past_at_succ s ((t.val + 8) % 9)) i).symm.trans
        (congrArg (fun n : ℕ => (step^[n] s).1 i) hindex)
  have hnext : column s i (t + 1) = (step^[t.val + 1] s).2 i := by
    change (step^[(t.val + 1) % 9] s).2 i = _
    by_cases h : t.val = 8
    · rw [h]
      exact (congrArg (fun q : Config => q.2 i) h9).symm
    · rw [Nat.mod_eq_of_lt (by omega : t.val + 1 < 9)]
  rw [hprev, hnext, current_at_succ]
  simp only [column, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]

private theorem column_background_tails (s : Config) (hs : FiniteConfig s) :
    ∃ M : ℤ, ∀ i : ℤ, i < -M ∨ M < i →
      column s i = (fun t : Fin 9 => t.val % 3 == 1) := by
  obtain ⟨M, hM⟩ := hs
  refine ⟨M + 8, ?_⟩
  intro i hi
  funext t
  have ht : t.val < 9 := t.isLt
  exact (finite_propagation s M hM t.val i (by omega)).2.trans (zero_current t.val i)

private theorem iterate_three_eq_of_column_invariant (s : Config) (h9 : step^[9] s = s)
    (h : ∀ (i : ℤ) (t : Fin 9), column s i (t + 3) = column s i t) :
    step^[3] s = s := by
  apply Prod.ext
  · rw [past_at_succ s 2]
    funext i
    calc
      (step^[2] s).2 i = column s i ((8 : Fin 9) + 3) := rfl
      _ = column s i 8 := h i 8
      _ = s.1 i := congrFun (current_eight_eq_past s h9) i
  · funext i
    exact h i 0

/-- The hypothesis supplied by the finite-column theorem. -/
private def FiniteColumnTheorem : Prop :=
  ∀ C : ℤ → Fin 9 → Bool,
    (∀ (i : ℤ) (t : Fin 9),
      Bool.xor (C i (t + 8)) (C i (t + 1)) =
        (!(C i t) || (C (i - 1) t && !(C (i + 1) t)))) →
    (∃ M : ℤ, ∀ i : ℤ, i < -M ∨ M < i →
      C i = (fun t : Fin 9 => t.val % 3 == 1)) →
    ∀ (i : ℤ) (t : Fin 9), C i (t + 3) = C i t

namespace Certificate

-- Bit zero in a mask represents time zero.

private abbrev Mask := BitVec 9
private abbrev ColumnPair := Mask × Mask
private abbrev ColumnTriple := Mask × Mask × Mask

private def encode (column : Fin 9 → Bool) : Mask :=
  (BitVec.ofBoolListLE (List.ofFn column)).cast List.length_ofFn

private def bit (mask : Mask) (t : Fin 9) : Bool :=
  mask.getLsbD t.val

@[simp] private theorem bit_encode (column : Fin 9 → Bool) (t : Fin 9) :
    bit (encode column) t = column t := by
  cases t with
  | mk i hi =>
    simp only [bit, encode, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, dite_true, Option.getD_some]

private theorem encode_bit (mask : Mask) : encode (bit mask) = mask := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact bit_encode (bit mask) ⟨i, hi⟩

private def B : Mask := 146
private def U : Mask := 511

private def background (t : Fin 9) : Bool := t.val % 3 == 1

private theorem bit_B : ∀ t, bit B t = background t := by decide

private theorem encode_background : encode background = B := by
  rw [← encode_bit B]
  exact congrArg encode (funext fun t => (bit_B t).symm)

private def lagXor (middle : Mask) (t : Fin 9) : Bool :=
  Bool.xor (bit middle (t + 8)) (bit middle (t + 1))

private def zeroCondition (middle : Mask) : Prop :=
  ∀ t, bit middle t = false → lagXor middle t = true

private def transitionCheck (left middle right : Mask) : Bool :=
  (List.finRange 9).all fun t =>
    lagXor middle t == (!(bit middle t) || (bit left t && !(bit right t)))

private def Transition (left middle right : Mask) : Prop :=
  transitionCheck left middle right = true

private theorem transition_iff (left middle right : Mask) :
    Transition left middle right ↔ ∀ t : Fin 9,
      Bool.xor (bit middle (t + 8)) (bit middle (t + 1)) =
        (!(bit middle t) || (bit left t && !(bit right t))) := by
  simp [Transition, transitionCheck, lagXor, List.mem_finRange]

private theorem transition_encode_iff (left middle right : Fin 9 → Bool) :
    Transition (encode left) (encode middle) (encode right) ↔ ∀ t : Fin 9,
      Bool.xor (middle (t + 8)) (middle (t + 1)) =
        (!(middle t) || (left t && !(right t))) := by
  simpa only [bit_encode] using transition_iff (encode left) (encode middle) (encode right)

private theorem zeroCondition_of_transition {left middle right : Mask}
    (h : Transition left middle right) : zeroCondition middle := by
  intro t hzero
  have ht := (transition_iff left middle right).mp h t
  simpa [lagXor, hzero] using ht

-- These lists transcribe the authorized certificate tables.

private def candidateColumns : List Mask := [
  73, 79, 103, 115, 121, 127, 146, 158, 206, 230, 242, 254,
  292, 295, 307, 313, 316, 319, 403, 409, 412, 415, 457, 460,
  463, 484, 487, 499, 505, 508, 511]

private def forwardPairs : List ColumnPair := [
  (79, 230), (121, 307), (146, 146), (146, 158), (146, 242),
  (146, 254), (146, 403), (146, 415), (146, 499), (146, 511),
  (158, 457), (158, 460), (158, 484), (242, 79), (242, 103),
  (242, 295), (254, 121), (254, 313), (254, 316), (295, 115),
  (316, 409), (403, 121), (403, 313), (403, 316), (415, 79),
  (415, 103), (415, 295), (457, 412), (484, 206), (499, 457),
  (499, 460), (499, 484), (511, 146), (511, 158), (511, 242),
  (511, 254), (511, 403), (511, 415), (511, 499), (511, 511)]

private def forwardEdges : List ColumnTriple := [
  (146, 146, 146), (146, 146, 158), (146, 146, 242), (146, 146, 254),
  (146, 146, 403), (146, 146, 415), (146, 146, 499), (146, 146, 511),
  (146, 158, 457), (146, 158, 460), (146, 158, 484), (146, 242, 79),
  (146, 242, 103), (146, 242, 295), (146, 254, 121), (146, 254, 313),
  (146, 254, 316), (146, 403, 121), (146, 403, 313), (146, 403, 316),
  (146, 415, 79), (146, 415, 103), (146, 415, 295), (146, 499, 457),
  (146, 499, 460), (146, 499, 484), (146, 511, 146), (146, 511, 158),
  (146, 511, 242), (146, 511, 254), (146, 511, 403), (146, 511, 415),
  (146, 511, 499), (146, 511, 511), (254, 121, 307), (254, 316, 409),
  (415, 79, 230), (415, 295, 115), (499, 457, 412), (499, 484, 206),
  (511, 146, 146), (511, 146, 158), (511, 146, 242), (511, 146, 254),
  (511, 146, 403), (511, 146, 415), (511, 146, 499), (511, 146, 511),
  (511, 158, 460), (511, 242, 103), (511, 403, 313), (511, 511, 511)]

private def returningPairs : List ColumnPair := [
  (146, 146), (146, 511), (511, 146)]

private def returningEdges : List ColumnTriple := [
  (146, 146, 146), (146, 146, 511), (146, 511, 146), (511, 146, 146),
  (511, 146, 511)]

private def zeroCheck (m : Mask) : Bool :=
  (List.finRange 9).all fun t => bit m t || lagXor m t

private theorem zeroCheck_iff (m : Mask) :
    zeroCheck m = true ↔ zeroCondition m := by
  simp only [zeroCheck, List.all_eq_true, List.mem_finRange, true_implies, zeroCondition]
  apply forall_congr'
  intro t
  cases bit m t <;> simp

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem checkedCandidates :
    (List.finRange (2 ^ 9)).all (fun n =>
      zeroCheck (BitVec.ofFin n) == candidateColumns.contains (BitVec.ofFin n)) = true := by
  decide +kernel

private theorem candidate_iff (m : Mask) : m ∈ candidateColumns ↔ zeroCondition m := by
  have h := (List.all_eq_true.mp checkedCandidates) m.toFin (List.mem_finRange _)
  have heq : zeroCheck m = candidateColumns.contains m := by
    simpa only [BitVec.ofFin_toFin, beq_iff_eq] using h
  rw [← zeroCheck_iff, heq, List.contains_iff_mem]

private def Step (p q : ColumnPair) : Prop :=
  p.2 = q.1 ∧ q.2 ∈ candidateColumns ∧ Transition p.1 p.2 q.2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem checkedForwardRows :
    forwardPairs.all (fun p => candidateColumns.all fun r =>
      transitionCheck p.1 p.2 r == forwardEdges.contains (p.1, p.2, r)) = true := by
  decide +kernel

private theorem forward_edge_iff {p : ColumnPair} {r : Mask}
    (hp : p ∈ forwardPairs) (hr : r ∈ candidateColumns) :
    Transition p.1 p.2 r ↔ (p.1, p.2, r) ∈ forwardEdges := by
  have hrow := List.all_eq_true.mp checkedForwardRows p hp
  have heq := beq_iff_eq.mp (List.all_eq_true.mp hrow r hr)
  rw [Transition, heq, List.contains_iff_mem]

private theorem checkedForwardTargets :
    forwardEdges.all (fun (_, m, r) => forwardPairs.contains (m, r)) = true := by
  decide

private theorem checkedReturningEdges :
    forwardEdges.filter (fun (_, m, r) => returningPairs.contains (m, r)) =
      returningEdges := by
  decide

private theorem checkedReturningSources :
    returningEdges.all (fun (l, m, _) => returningPairs.contains (l, m)) = true := by
  decide

private theorem seed_forward : (B, B) ∈ forwardPairs := by decide

private theorem seed_returning : (B, B) ∈ returningPairs := by decide

private theorem forward_closed {p q : ColumnPair} (hp : p ∈ forwardPairs) (h : Step p q) :
    q ∈ forwardPairs := by
  obtain ⟨hlink, hr, ht⟩ := h
  have hedge := (forward_edge_iff hp hr).mp ht
  have htarget := List.contains_iff_mem.mp
    (List.all_eq_true.mp checkedForwardTargets (p.1, p.2, q.2) hedge)
  simpa [hlink] using htarget

private theorem returning_predecessor {p q : ColumnPair} (hp : p ∈ forwardPairs)
    (h : Step p q) (hq : q ∈ returningPairs) : p ∈ returningPairs := by
  obtain ⟨hlink, hr, ht⟩ := h
  have hedge := (forward_edge_iff hp hr).mp ht
  have hfilter : (p.1, p.2, q.2) ∈ returningEdges := by
    rw [← checkedReturningEdges]
    exact List.mem_filter.mpr ⟨hedge, List.contains_iff_mem.mpr (by simpa [hlink] using hq)⟩
  exact List.contains_iff_mem.mp
    (List.all_eq_true.mp checkedReturningSources (p.1, p.2, q.2) hfilter)

private theorem bit_B_three : ∀ t : Fin 9, bit B (t + 3) = bit B t := by decide

private theorem bit_U_three : ∀ t : Fin 9, bit U (t + 3) = bit U t := by decide

private theorem checkedReturningSeconds :
    returningPairs.all (fun p => p.2 == B || p.2 == U) = true := by decide

private theorem returning_second {p : ColumnPair} (hp : p ∈ returningPairs) :
    p.2 = B ∨ p.2 = U := by
  simpa only [Bool.or_eq_true, beq_iff_eq] using
    List.all_eq_true.mp checkedReturningSeconds p hp

-- The finite spatial interval is traversed in increasing integer order.
private theorem path_of_int_segment {α : Type} {step : α → α → Prop}
    (p : ℤ → α) (hs : ∀ i, step (p i) (p (i + 1)))
    {a b : ℤ} (hab : a ≤ b) : Relation.ReflTransGen step (p a) (p b) := by
  have hpath : Relation.ReflTransGen (fun i j => step (p i) (p j)) a b :=
    reflTransGen_of_succ_of_le (fun i j => step (p i) (p j))
      (fun i _ => by simpa only [Order.succ_eq_add_one] using hs i) hab
  exact hpath.lift p (fun _ _ h => h)

private theorem forward_along_path {p q : ColumnPair} (hp : p ∈ forwardPairs)
    (h : Relation.ReflTransGen Step p q) : q ∈ forwardPairs := by
  induction h with
  | refl => exact hp
  | tail _ hs ih => exact forward_closed ih hs

private theorem returning_along_path {p q : ColumnPair}
    (h : Relation.ReflTransGen (fun a b => a ∈ forwardPairs ∧ Step a b) p q)
    (hq : q ∈ returningPairs) : p ∈ returningPairs := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hq
  | head hs _ ih => exact returning_predecessor hs.1 hs.2 ih

private theorem three_periodic
    (C : ℤ → Fin 9 → Bool)
    (hcol : ∀ (i : ℤ) (t : Fin 9),
      Bool.xor (C i (t + 8)) (C i (t + 1)) =
        (!(C i t) || (C (i - 1) t && !(C (i + 1) t))))
    (htail : ∃ M : ℤ, ∀ i, i < -M ∨ M < i →
      C i = (fun t : Fin 9 => t.val % 3 == 1)) :
    ∀ i t, C i (t + 3) = C i t := by
  obtain ⟨M, htail⟩ := htail
  let mask : ℤ → Mask := fun i => encode (C i)
  let pair : ℤ → ColumnPair := fun i => (mask (i - 1), mask i)
  have htransition (i : ℤ) : Transition (mask (i - 1)) (mask i) (mask (i + 1)) :=
    (transition_encode_iff _ _ _).mpr (hcol i)
  have hadmissible (i : ℤ) : mask i ∈ candidateColumns :=
    (candidate_iff _).mpr (zeroCondition_of_transition (htransition i))
  have hstep (i : ℤ) : Step (pair i) (pair (i + 1)) := by
    have hprev : i + 1 - 1 = i := by omega
    exact ⟨congrArg mask hprev.symm, hadmissible (i + 1), htransition i⟩
  have htailMask (i : ℤ) (hi : i < -M ∨ M < i) : mask i = B := by
    change encode (C i) = B
    rw [htail i hi]
    exact encode_background
  have hallForward (i : ℤ) : pair i ∈ forwardPairs := by
    let a := min i (-M - 1)
    have hai : a ≤ i := Int.min_le_left _ _
    have haLeft : a ≤ -M - 1 := Int.min_le_right _ _
    have ha : pair a = (B, B) := by
      exact Prod.ext (htailMask _ (Or.inl (by omega))) (htailMask _ (Or.inl (by omega)))
    have hstart : pair a ∈ forwardPairs := ha.symm ▸ seed_forward
    exact forward_along_path hstart (path_of_int_segment pair hstep hai)
  have hstepForward (i : ℤ) : pair i ∈ forwardPairs ∧ Step (pair i) (pair (i + 1)) :=
    ⟨hallForward i, hstep i⟩
  intro i t
  let b := max i (M + 2)
  have hib : i ≤ b := Int.le_max_left _ _
  have hbRight : M + 2 ≤ b := Int.le_max_right _ _
  have hb : pair b = (B, B) := by
    exact Prod.ext (htailMask _ (Or.inr (by omega))) (htailMask _ (Or.inr (by omega)))
  have hend : pair b ∈ returningPairs := hb.symm ▸ seed_returning
  have hreturn := returning_along_path (path_of_int_segment pair hstepForward hib) hend
  have hmask : mask i = B ∨ mask i = U := returning_second hreturn
  have hperiod : bit (mask i) (t + 3) = bit (mask i) t := by
    rcases hmask with heq | heq
    · rw [heq]
      exact bit_B_three t
    · rw [heq]
      exact bit_U_three t
  simpa only [mask, bit_encode] using hperiod

end Certificate

/-- The union of the two initial supports is finite exactly when both layers
vanish beyond a common spatial bound. -/
private theorem finite_support_iff (s : Config) :
    Set.Finite {i : ℤ | s.1 i = true ∨ s.2 i = true} ↔ FiniteConfig s := by
  constructor
  · intro h
    obtain ⟨lo, hlo⟩ := h.bddBelow
    obtain ⟨hi, hhi⟩ := h.bddAbove
    refine ⟨max (-lo) hi, ?_⟩
    intro i houtside
    have hnot : i ∉ {j : ℤ | s.1 j = true ∨ s.2 j = true} := by
      intro hin
      have hl := hlo hin
      have hu := hhi hin
      change lo ≤ i at hl
      change i ≤ hi at hu
      have hleft := le_max_left (-lo) hi
      have hright := le_max_right (-lo) hi
      omega
    change ¬ (s.1 i = true ∨ s.2 i = true) at hnot
    simpa only [not_or, Bool.not_eq_true] using hnot
  · rintro ⟨M, hM⟩
    refine (Set.finite_Icc (a := -M) (b := M)).subset ?_
    intro i hin
    change s.1 i = true ∨ s.2 i = true at hin
    change -M ≤ i ∧ i ≤ M
    by_contra h
    have houtside : i < -M ∨ M < i := by omega
    obtain ⟨hPast, hCurrent⟩ := hM i houtside
    simp [hPast, hCurrent] at hin

/-- Every nine-step return from two finitely supported layers is a three-step return. -/
theorem returns_three_of_returns_nine (s : Config)
    (hfinite : Set.Finite {i : ℤ | s.1 i = true ∨ s.2 i = true})
    (h9 : step^[9] s = s) : step^[3] s = s := by
  have hcolumns : FiniteColumnTheorem := Certificate.three_periodic
  have hinvariant := hcolumns (column s) (column_cyclic s h9)
    (column_background_tails s ((finite_support_iff s).mp hfinite))
  exact iterate_three_eq_of_column_invariant s h9 hinvariant

/-- Every positive multiple of three occurs as a least period with two finitely
supported initial layers. -/
def claim : Prop :=
  ∀ p : ℕ, 0 < p → 3 ∣ p →
    ∃ s : Config, Set.Finite {i : ℤ | s.1 i = true ∨ s.2 i = true} ∧
      step^[p] s = s ∧ ∀ q : ℕ, 0 < q → q < p → step^[q] s ≠ s

/-- Period nine refutes the assertion in Question 1. -/
theorem result : ¬ claim := by
  intro hclaim
  obtain ⟨s, hfinite, h9, hleast⟩ := hclaim 9 (by decide) (by decide)
  exact hleast 3 (by decide) (by decide) (returns_three_of_returns_nine s hfinite h9)

end FormentiKamilyaRule115

end D5.S3.StatisticalMechanics.CellularAutomata
