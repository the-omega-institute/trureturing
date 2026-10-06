/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CoprimeSingletonCost
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CoprimeSingletonCost
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Coprime nonzero initial phase singletons have exact safe complete-block cost. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalNarrowCost

set_option autoImplicit false
noncomputable section
universe z

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.CoprimeSingletonCost

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells OriginalNarrowCost
open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Tower.DBonacciGeneral.UniformBaseGap
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S0.Tower.DBonacci.Names
open scoped BigOperators

-- Literal protocols and the original scanner are coupled within one proof.
set_option maxHeartbeats 1500000 in
/-- The minimum ranges over every actual selector, including actions that reject.
The attaining selector and its endpoint tree share one literal execution and keep
all legal old tails safe. The target index is the initial index. -/
theorem coprime_nonzero_singleton_cost {Y : Type z}
    (k m j : ℕ) (hk : 2 ≤ k) (hm : 2 ≤ m) (hshort : m < k)
    (hcoprime : Nat.Coprime m (k + 1)) (hj : 1 ≤ j) (hjk : j ≤ k)
    (A B bottom : Y) (hAB : A ≠ B) (v : ZMod 2) (localAlphabet : Bool) :
    let D := max 2 (j ⌈/⌉ m)
    let labels : Fin ((k + 1) / Nat.gcd m (k + 1)) → Y :=
      fun i => if i.val = j then B else A
    IsLeast {d : ℕ | NarrowWindowCost.Feasible k m (by omega)
      localAlphabet labels bottom v d} D ∧
    ∃ (π : NarrowWindowCost.Selector m Y)
      (trees : Option (ZMod 2) → AcquisitionTree k m localAlphabet Y D),
      (∀ y₀ archive word, π y₀ archive = .inr word →
        localAlphabet = true → DBonacciAdmissible k m word) ∧
      π none [] = .inl bottom ∧
      (trees none).result none = bottom ∧ (trees none).archive none = [] ∧
      (∀ (i : Fin ((k + 1) / Nat.gcd m (k + 1))) (s : ℕ), s < k →
        let q : Option (LiveRecord k) := some ⟨v, -(i.val : ZMod (k + 1)), s⟩
        (trees (some v)).result q = labels i ∧
        ((trees (some v)).archive q).length ≤ D ∧
        (∀ entry ∈ (trees (some v)).archive q, entry.2 ≠ none) ∧
        (∀ t (ht : t < ((trees (some v)).archive q).length),
          π (some v) (((trees (some v)).archive q).take t |>.map
            (fun entry => (entry.1.val, entry.2))) =
          .inr (((trees (some v)).archive q)[t].1.val)) ∧
        π (some v) (((trees (some v)).archive q).map
          (fun entry => (entry.1.val, entry.2))) = .inl (labels i)) ∧
      (∀ (w : List Bool) (i : Fin ((k + 1) / Nat.gcd m (k + 1))),
        m ∣ w.length → NarrowWindowCost.output k (by omega) w = some v →
        k + 1 ∣ w.length + i.val * Nat.gcd m (k + 1) →
        ∃ c ≤ D,
          NarrowWindowCost.execute k (by omega) π D w (some v) [] =
            some (labels i, c) ∧
          (trees (some v)).result (OriginalNarrowCost.OriginalRecord k (by omega) w) =
            labels i ∧
          ((trees (some v)).archive
            (OriginalNarrowCost.OriginalRecord k (by omega) w)).length = c) := by
  classical
  dsimp only
  have hg : Nat.gcd m (k + 1) = 1 := hcoprime
  have hk3 : 3 ≤ k := by omega
  let marker (phi : ZMod (k + 1)) : ZMod 2 := if phi = 0 then 1 else 0
  have nontrivial : (1 : ZMod (k + 1)) ≠ 0 := by
    intro eq
    have hd := (ZMod.natCast_eq_zero_iff 1 (k + 1)).mp eq
    have bound := Nat.le_of_dvd (by omega : 0 < 1) hd
    omega
  have edge (phi : ZMod (k + 1)) :
      coefficient k phi = marker phi + marker (phi + 1) := by
    have next : phi + 1 = 0 ↔ phi = -1 := by
      constructor
      · intro h; exact eq_neg_of_add_eq_zero_left h
      · intro h; simp [h]
    by_cases zero : phi = 0
    · have notLast : phi ≠ -1 := by
        intro h
        have : (1 : ZMod (k + 1)) = 0 := by
          have e : (0 : ZMod (k + 1)) = -1 := zero.symm.trans h
          simpa using (congrArg Neg.neg e).symm
        exact nontrivial this
      simp [coefficient, marker, zero, nontrivial]
    · by_cases last : phi = -1
      · simp [coefficient, marker, zero, next, last, nontrivial]
      · simp [coefficient, marker, zero, next, last, nontrivial]
  have appendRun (left right : List Bool) (q : Option (LiveRecord k)) :
      runWord (bitUpdate k) (left ++ right) q =
        runWord (bitUpdate k) right (runWord (bitUpdate k) left q) := by
    induction left generalizing q with
    | nil => rfl
    | cons bit left ih => simpa only [List.cons_append, runWord] using ih (bitUpdate k bit q)
  have absorbed (bits : List Bool) : runWord (bitUpdate k) bits none = none := by
    induction bits with
    | nil => rfl
    | cons bit bits ih => simpa only [runWord, bitUpdate] using ih
  have zeros : ∀ n (a : ZMod 2) (phi : ZMod (k + 1)) s,
      runWord (bitUpdate k) (List.replicate n false) (some ⟨a, phi, s⟩) =
        some ⟨a, phi + (n : ℕ), if n = 0 then s else 0⟩ := by
    intro n
    induction n with
    | zero => intros; simp [runWord]
    | succ n ih =>
        intro a phi s
        rw [List.replicate_succ, runWord]
        simp only [bitUpdate, Bool.false_eq_true, if_false]
        rw [ih]
        simp [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
  have ones : ∀ n (a : ZMod 2) (phi : ZMod (k + 1)) s, s + n < k →
      runWord (bitUpdate k) (List.replicate n true) (some ⟨a, phi, s⟩) =
        some ⟨a + marker phi + marker (phi + (n : ℕ)), phi + (n : ℕ), s + n⟩ := by
    intro n
    induction n with
    | zero =>
        intro a phi s safe
        simp [runWord, CharTwo.add_self_eq_zero, add_assoc]
    | succ n ih =>
        intro a phi s safe
        have firstSafe : s + 1 < k := by omega
        rw [List.replicate_succ, runWord]
        simp only [bitUpdate, if_true, firstSafe, if_pos]
        rw [ih _ _ _ (by omega), edge]
        have cancel := CharTwo.add_self_eq_zero (marker (phi + 1))
        have phase : phi + 1 + (n : ℕ) = phi + ((n + 1 : ℕ) : ZMod (k + 1)) := by
          push_cast; abel
        rw [phase]
        have scalar : a + (marker phi + marker (phi + 1)) + marker (phi + 1) +
            marker (phi + ((n + 1 : ℕ) : ZMod (k + 1))) =
            a + marker phi + marker (phi + ((n + 1 : ℕ) : ZMod (k + 1))) := by
          linear_combination cancel
        rw [scalar, show s + 1 + n = s + (n + 1) by omega]
  have zeroThenOnes (a b : ℕ) (ha : 0 < a) (hb : b < k)
      (value : ZMod 2) (phi : ZMod (k + 1)) (s : ℕ) :
      runWord (bitUpdate k) (List.replicate a false ++ List.replicate b true)
        (some ⟨value, phi, s⟩) =
      some ⟨value + marker (phi + (a : ℕ)) + marker (phi + ((a + b : ℕ) : ZMod (k + 1))),
        phi + ((a + b : ℕ) : ZMod (k + 1)), b⟩ := by
    rw [appendRun, zeros, if_neg (by omega), ones _ _ _ _ (by omega)]
    simp only [zero_add, Nat.cast_add, add_assoc]
  have onesThenZero (a b : ℕ) (value : ZMod 2) (phi : ZMod (k + 1)) (s : ℕ)
      (safe : s + a < k) :
      runWord (bitUpdate k) (List.replicate a true ++ List.replicate b false)
        (some ⟨value, phi, s⟩) =
      some ⟨value + marker phi + marker (phi + (a : ℕ)),
        phi + ((a + b : ℕ) : ZMod (k + 1)), if b = 0 then s + a else 0⟩ := by
    rw [appendRun, ones _ _ _ _ safe, zeros]
    simp only [Nat.cast_add, add_assoc]
  have indexedMarker (i t : ℕ) (hi : i ≤ k) (ht : t ≤ k) :
      marker (-(i : ZMod (k + 1)) + (t : ℕ)) = if t = i then 1 else 0 := by
    have eq : -(i : ZMod (k + 1)) + (t : ℕ) = 0 ↔ t = i := by
      rw [neg_add_eq_zero, ZMod.natCast_eq_natCast_iff']
      rw [Nat.mod_eq_of_lt (by omega : t < k + 1), Nat.mod_eq_of_lt (by omega : i < k + 1)]
      exact eq_comm
    simp only [marker, eq]
  have rootBelow (i s : ℕ) (hi : i ≤ k) (hs : s < k) (below : j < m) :
      runWord (bitUpdate k) (List.replicate j false ++ List.replicate (m - j) true)
        (some ⟨v, -(i : ZMod (k + 1)), s⟩) =
      some ⟨v + (if j = i then 1 else 0) + (if m = i then 1 else 0),
        -(i : ZMod (k + 1)) + (m : ℕ), m - j⟩ := by
    rw [zeroThenOnes _ _ hj (by omega)]
    have endLength : j + (m - j) = m := by omega
    rw [endLength, indexedMarker i j hi hjk, indexedMarker i m hi (by omega)]
  have rootAt (i s : ℕ) (hi : i ≤ k) (hs : s < k) :
      runWord (bitUpdate k) (List.replicate (m - 1) false ++ [true])
        (some ⟨v, -(i : ZMod (k + 1)), s⟩) =
      some ⟨v + (if m - 1 = i then 1 else 0) + (if m = i then 1 else 0),
        -(i : ZMod (k + 1)) + (m : ℕ), 1⟩ := by
    change runWord (bitUpdate k) (List.replicate (m - 1) false ++ List.replicate 1 true) _ = _
    rw [zeroThenOnes _ _ (by omega) (by omega)]
    have endLength : m - 1 + 1 = m := by omega
    rw [endLength, indexedMarker i (m - 1) hi (by omega), indexedMarker i m hi (by omega)]
  have repair (i s : ℕ) (hi : i ≤ k) (safe : s + 1 < k) (value : ZMod 2) :
      runWord (bitUpdate k) ([true] ++ List.replicate (m - 1) false)
        (some ⟨value, -(i : ZMod (k + 1)) + (m : ℕ), s⟩) =
      some ⟨value + (if m = i then 1 else 0) + (if m + 1 = i then 1 else 0),
        -(i : ZMod (k + 1)) + ((2 * m : ℕ) : ZMod (k + 1)), 0⟩ := by
    change runWord (bitUpdate k) (List.replicate 1 true ++ List.replicate (m - 1) false) _ = _
    rw [onesThenZero _ _ _ _ _ safe]
    have len : m + (1 + (m - 1)) = 2 * m := by omega
    have phaseEnd : -(i : ZMod (k + 1)) + (m : ℕ) + ((1 + (m - 1) : ℕ) : ZMod (k + 1)) =
        -(i : ZMod (k + 1)) + ((2 * m : ℕ) : ZMod (k + 1)) := by
      rw [add_assoc, ← Nat.cast_add, len]
    simp only [phaseEnd, show m - 1 ≠ 0 by omega, if_false]
    rw [indexedMarker i m hi (by omega)]
    have shifted : -(i : ZMod (k + 1)) + (m : ℕ) + (1 : ℕ) =
        -(i : ZMod (k + 1)) + ((m + 1 : ℕ) : ZMod (k + 1)) := by push_cast; abel
    rw [shifted, indexedMarker i (m + 1) hi (by omega)]
  have remoteArithmetic (remote : m < j) :
      let d := j ⌈/⌉ m
      let a := (d - 1) * m
      let r := j - a
      2 ≤ d ∧ a < j ∧ 1 ≤ r ∧ r ≤ m ∧ a + r = j ∧ 1 + r < k := by
    dsimp only
    let d := j ⌈/⌉ m
    have hd2 : 2 ≤ d := by
      have notOne : ¬ d ≤ 1 := by
        intro bound
        have := (ceilDiv_le_iff_le_mul (by omega : 0 < m)).mp bound
        simp only [Nat.mul_one] at this
        omega
      omega
    have upper : j ≤ m * d := (ceilDiv_le_iff_le_mul (by omega : 0 < m)).mp le_rfl
    have lower : (d - 1) * m < j := by
      by_contra bad
      have bound : d ≤ d - 1 := (ceilDiv_le_iff_le_mul (by omega : 0 < m)).mpr
        (by simpa only [Nat.mul_comm] using Nat.le_of_not_gt bad)
      omega
    have split : d * m = (d - 1) * m + m := by
      have hd : d = (d - 1) + 1 := by omega
      conv_lhs => rw [hd]
      ring
    have upper' : j ≤ (d - 1) * m + m := by
      rw [← split]
      simpa only [Nat.mul_comm] using upper
    have rbound : j - (d - 1) * m ≤ m := by omega
    have seam : 1 + (j - (d - 1) * m) < k := by
      by_cases wide : m = k - 1
      · have jtop : j = k := by omega
        have deq : d = 2 := by
          apply le_antisymm
          · apply (ceilDiv_le_iff_le_mul (by omega : 0 < m)).mpr
            omega
          · exact hd2
        rw [deq]
        simp only [Nat.reduceSub, Nat.one_mul]
        omega
      · omega
    change 2 ≤ d ∧ (d - 1) * m < j ∧ 1 ≤ j - (d - 1) * m ∧
      j - (d - 1) * m ≤ m ∧ (d - 1) * m + (j - (d - 1) * m) = j ∧
      1 + (j - (d - 1) * m) < k
    exact ⟨hd2, lower, by omega, rbound, by omega, seam⟩
  have remotePulse (remote : m < j) (i s : ℕ) (hi : i ≤ k) (hs : s < k) :
      let d := j ⌈/⌉ m
      let a := (d - 1) * m
      runWord (bitUpdate k)
        (List.replicate ((d - 2) * m) false ++
          (List.replicate (m - 1) false ++ [true]))
        (some ⟨v, -(i : ZMod (k + 1)), s⟩) =
      some ⟨v + (if a - 1 = i then 1 else 0) + (if a = i then 1 else 0),
        -(i : ZMod (k + 1)) + (a : ℕ), 1⟩ := by
    dsimp only
    obtain ⟨hd, ha, hr, hrm, sum, seam⟩ := remoteArithmetic remote
    have zerosLength : (j ⌈/⌉ m - 2) * m + (m - 1) = (j ⌈/⌉ m - 1) * m - 1 := by
      have dec : j ⌈/⌉ m - 1 = (j ⌈/⌉ m - 2) + 1 := by omega
      rw [dec, Nat.add_mul]
      simp only [Nat.one_mul]
      omega
    rw [← List.append_assoc, ← List.replicate_add, zerosLength]
    change runWord (bitUpdate k)
      (List.replicate ((j ⌈/⌉ m - 1) * m - 1) false ++ List.replicate 1 true) _ = _
    have apos : 0 < (j ⌈/⌉ m - 1) * m - 1 := by
      have one : 1 ≤ j ⌈/⌉ m - 1 := by omega
      have bound := Nat.mul_le_mul_right m one
      simp only [Nat.one_mul] at bound
      omega
    rw [zeroThenOnes _ _ apos (by omega)]
    have endLength : (j ⌈/⌉ m - 1) * m - 1 + 1 = (j ⌈/⌉ m - 1) * m := by omega
    rw [endLength, indexedMarker i _ hi (by omega), indexedMarker i _ hi (by omega)]
  have remoteFinal (remote : m < j) (i : ℕ) (hi : i ≤ k) (value : ZMod 2) :
      let d := j ⌈/⌉ m
      let a := (d - 1) * m
      let r := j - a
      runWord (bitUpdate k)
        (List.replicate r true ++ List.replicate (m - r) false)
        (some ⟨value, -(i : ZMod (k + 1)) + (a : ℕ), 1⟩) =
      some ⟨value + (if a = i then 1 else 0) + (if j = i then 1 else 0),
        -(i : ZMod (k + 1)) + ((d * m : ℕ) : ZMod (k + 1)),
        if r = m then 1 + r else 0⟩ := by
    dsimp only
    obtain ⟨hd, ha, hr, hrm, sum, seam⟩ := remoteArithmetic remote
    rw [onesThenZero _ _ _ _ _ seam]
    rw [indexedMarker i _ hi (by omega)]
    have phaseJ : -(i : ZMod (k + 1)) + (((j ⌈/⌉ m - 1) * m : ℕ) : ZMod (k + 1)) +
        ((j - (j ⌈/⌉ m - 1) * m : ℕ) : ZMod (k + 1)) =
        -(i : ZMod (k + 1)) + (j : ℕ) := by
      rw [add_assoc, ← Nat.cast_add, sum]
    rw [phaseJ, indexedMarker i j hi hjk]
    have total : (j ⌈/⌉ m - 1) * m +
        ((j - (j ⌈/⌉ m - 1) * m) + (m - (j - (j ⌈/⌉ m - 1) * m))) =
        (j ⌈/⌉ m) * m := by
      have pad : (j - (j ⌈/⌉ m - 1) * m) + (m - (j - (j ⌈/⌉ m - 1) * m)) = m := by omega
      rw [pad]
      have dec : j ⌈/⌉ m = (j ⌈/⌉ m - 1) + 1 := by omega
      conv_rhs => rw [dec]
      ring
    have phaseEnd : -(i : ZMod (k + 1)) + (((j ⌈/⌉ m - 1) * m : ℕ) : ZMod (k + 1)) +
        (((j - (j ⌈/⌉ m - 1) * m) + (m - (j - (j ⌈/⌉ m - 1) * m)) : ℕ) : ZMod (k + 1)) =
        -(i : ZMod (k + 1)) + (((j ⌈/⌉ m) * m : ℕ) : ZMod (k + 1)) := by
      rw [add_assoc, ← Nat.cast_add, total]
    rw [phaseEnd]
    congr 2
    apply if_congr
    · omega
    · rfl
    · rfl
  let NativeExecute {Y : Type z} {k m : ℕ} (π : NarrowWindowCost.Selector m Y)
      (d : ℕ) : Option (LiveRecord k) → Option (ZMod 2) →
        NarrowWindowCost.Archive m → Option (Y × ℕ) :=
    Nat.rec
      (fun _ y₀ archive => match π y₀ archive with
        | .inl y => some (y,0)
        | .inr _ => none)
      (fun _ next q y₀ archive => match π y₀ archive with
        | .inl y => some (y,0)
        | .inr B =>
          let q' := runBits k B q
          (next q' y₀ (archive++[(B,endpointReading q')])).map
            (fun r => (r.1,r.2+1))) d
  have nativeZero {Y' : Type z} {k' m' : ℕ}
      (π' : NarrowWindowCost.Selector m' Y') (q : Option (LiveRecord k')) initial archive :
      NativeExecute π' 0 q initial archive =
        (match π' initial archive with | .inl label => some (label, 0) | .inr _ => none) := rfl
  have nativeStep {Y' : Type z} {k' m' : ℕ}
      (π' : NarrowWindowCost.Selector m' Y') (n : ℕ) (q : Option (LiveRecord k')) initial archive :
      NativeExecute π' (n + 1) q initial archive =
        (match π' initial archive with
        | .inl label => some (label, 0)
        | .inr word =>
          (NativeExecute π' n (runBits k' word q) initial
            (archive ++ [(word, endpointReading (runBits k' word q))])).map
            (fun result => (result.1, result.2 + 1))) := rfl
  let SelectorTree {Y : Type z} {k m : ℕ} {localAlphabet : Bool}
      (fallback : Y) (π : NarrowWindowCost.Selector m Y)
      (legal : ∀ y₀ archive B, π y₀ archive = .inr B →
        localAlphabet=true → DBonacciAdmissible k m B)
      (d : ℕ) (y₀ : Option (ZMod 2)) (archive : NarrowWindowCost.Archive m) :
      AcquisitionTree k m localAlphabet Y d :=
    Nat.rec (motive := fun n => NarrowWindowCost.Archive m →
      AcquisitionTree k m localAlphabet Y n)
      (fun archive => .stop (match π y₀ archive with
        | .inl y => y
        | .inr _ => fallback))
      (fun _ next archive => match selected : π y₀ archive with
        | .inl y => .stop y
        | .inr B => .step ⟨B,legal y₀ archive B selected⟩
          (fun reply => next (archive++[(B,reply)]))) d archive
  have selectorTreeSuccess :
    ∀ {Y : Type z} (k m : ℕ) (localAlphabet : Bool) (fallback : Y)
      (π : D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.Selector m Y)
      (legal : ∀ y₀ archive B, π y₀ archive=.inr B →
        localAlphabet=true → DBonacciAdmissible k m B)
      (d : ℕ) (q : Option (LiveRecord k)) (y₀ : Option (ZMod 2))
      (archive : D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.Archive m) (y : Y) (c : ℕ),
      NativeExecute π d q y₀ archive=some (y,c) →
        (SelectorTree fallback π legal d y₀ archive).result q=y ∧
        ((SelectorTree fallback π legal d y₀ archive).archive q).length=c ∧
        (∀ t (ht : t < ((SelectorTree fallback π legal d y₀ archive).archive q).length),
          π y₀ (archive ++ (((SelectorTree fallback π legal d y₀ archive).archive q).take t).map
            (fun entry => (entry.1.val, entry.2))) =
            .inr (((SelectorTree fallback π legal d y₀ archive).archive q)[t].1.val)) ∧
        π y₀ (archive ++ ((SelectorTree fallback π legal d y₀ archive).archive q).map
          (fun entry => (entry.1.val, entry.2))) = .inl y := by
    classical
    intro Y k m localAlphabet fallback π legal d
    induction d with
    | zero =>
        intro q y₀ archive y c success
        cases eq : π y₀ archive with
        | inl label =>
            simp only [NativeExecute,Nat.rec_zero,Nat.rec_add_one,eq,Option.some.injEq,Prod.mk.injEq] at success
            simp [SelectorTree,Nat.rec_zero,Nat.rec_add_one,eq,AcquisitionTree.result,AcquisitionTree.archive,success.1,success.2]
            omega
        | inr B => simp [NativeExecute,Nat.rec_zero,Nat.rec_add_one,eq] at success
    | succ d ih =>
        intro q y₀ archive y c success
        cases eq : π y₀ archive with
        | inl label =>
            simp only [NativeExecute,Nat.rec_zero,Nat.rec_add_one,eq,Option.some.injEq,Prod.mk.injEq] at success
            simp only [SelectorTree,Nat.rec_zero,Nat.rec_add_one]
            split
            · rename_i label' chosen
              have same : label'=label := Sum.inl.inj (chosen.symm.trans eq)
              subst label'
              simp only [AcquisitionTree.result, AcquisitionTree.archive, List.length_nil,
                List.map_nil, List.append_nil]
              exact ⟨success.1, success.2, by omega, eq.trans (congrArg Sum.inl success.1)⟩
            · rename_i B chosen
              have impossible := chosen.symm.trans eq
              cases impossible
        | inr B =>
            simp only [NativeExecute,Nat.rec_zero,Nat.rec_add_one,eq] at success
            obtain ⟨r,hr,he⟩ := Option.map_eq_some_iff.mp success
            have nextProof := ih (runBits k B q) y₀ (archive++[(B,endpointReading (runBits k B q))]) r.1 r.2 hr
            have he' : r.1=y ∧ r.2+1=c := Prod.mk.inj he
            simp only [SelectorTree,Nat.rec_zero,Nat.rec_add_one]
            split
            · rename_i label chosen
              have impossible := chosen.symm.trans eq
              cases impossible
            · rename_i B' chosen
              have same : B'=B := Sum.inr.inj (chosen.symm.trans eq)
              subst B'
              simp only [AcquisitionTree.result,AcquisitionTree.archive,List.length_cons]
              refine ⟨nextProof.1.trans he'.1, ?_, ?_, ?_⟩
              · simpa only [SelectorTree] using
                  (congrArg (fun n => n + 1) nextProof.2.1).trans he'.2
              · intro t ht
                cases t with
                | zero => simpa only [List.take_zero, List.map_nil, List.append_nil,
                    List.getElem_cons_zero] using eq
                | succ t =>
                    have tailBound : t < ((SelectorTree fallback π legal d y₀
                      (archive ++ [(B, endpointReading (runBits k B q))])).archive
                        (runBits k B q)).length := by
                      dsimp only [SelectorTree]
                      omega
                    simpa only [SelectorTree, List.take_succ_cons, List.map_cons,
                      List.getElem_cons_succ, List.append_assoc, List.singleton_append]
                      using nextProof.2.2.1 t tailBound
              · simpa only [SelectorTree, List.map_cons, List.append_assoc,
                  List.singleton_append, he'.1] using nextProof.2.2.2
  have weight_coefficient :
      ∀ (k : ℕ), 2 ≤ k → ∀ n : ℕ,
        originalWeight k n = coefficient k (n : ZMod (k+1)) := by
    intro k hk
    let W := originalWeight k
    have recurrence (n : ℕ) : W (n+k) = ∑ i ∈ Finset.range k, W (n+i) := by
      have h := congrArg (fun a : ℕ => (a : ZMod 2))
        (dbonacci_add_two_of_le k (n+k) (by omega))
      have hfin : W (n+k) = ∑ i : Fin k, W (n+i.val) := by
        simpa only [Nat.add_sub_cancel,Nat.cast_sum,W,originalWeight] using h
      rw [Finset.sum_fin_eq_sum_range] at hfin
      calc
        _ = _ := hfin
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Finset.mem_range.mp hi,dif_pos,Fin.val_mk]
    have period : Function.Periodic W (k+1) := by
      intro n
      have window : (∑ i ∈ Finset.range k, W (n+1+i)) + W n =
          (∑ i ∈ Finset.range k, W (n+i)) + W (n+k) := by
        have left := Finset.sum_range_succ' (fun i => W (n+i)) k
        have right := Finset.sum_range_succ (fun i => W (n+i)) k
        simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          using left.symm.trans right
      rw [← recurrence (n+1), ← recurrence n] at window
      have hzero : W (n+k) + W (n+k) = 0 := CharTwo.add_self_eq_zero _
      rw [hzero] at window
      have same := CharTwo.add_eq_zero.mp window
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using same
    intro n
    let r := n % (k+1)
    have hr : r < k+1 := Nat.mod_lt n (by omega)
    have seed : W r = if r=0 ∨ r=k then 1 else 0 := by
      by_cases last : r=k
      · rw [if_pos (Or.inr last),last]
        change (dbonacci k (k+2) : ZMod 2)=1
        rw [dbonacci_diagonal_cardinality]
        rw [Nat.cast_sub (Nat.one_le_pow k 2 (by omega))]
        simp [Nat.cast_pow, CharTwo.two_eq_zero, show k ≠ 0 by omega]
      · change (dbonacci k (r+2) : ZMod 2) = _
        rw [dbonacci_add_two_of_lt k r (by omega)]
        by_cases zero : r=0
        · simp [zero]
        · simp [zero,last,Nat.cast_pow,CharTwo.two_eq_zero]
    have hz : (n : ZMod (k+1))=0 ↔ r=0 := by
      rw [← Nat.cast_zero,ZMod.natCast_eq_natCast_iff']
      simp only [Nat.zero_mod,r]
    have ht : (n : ZMod (k+1)) = -1 ↔ r=k := by
      constructor
      · intro h
        simpa only [ZMod.val_natCast,ZMod.val_neg_one,r] using congrArg ZMod.val h
      · intro h
        apply ZMod.val_injective (k+1)
        simpa only [ZMod.val_natCast,ZMod.val_neg_one,r] using h
    change W n = _
    rw [← period.map_mod_nat n,seed]
    simp only [coefficient,hz,ht]

  have run_append : ∀ (k : ℕ) (a b : List Bool) (q : Option (LiveRecord k)),
      runWord (bitUpdate k) (a++b) q =
        runWord (bitUpdate k) b (runWord (bitUpdate k) a q) := by
    intro k a
    induction a with
    | nil => intros; rfl
    | cons bit a ih =>
        intro b q
        simpa only [List.cons_append,runWord] using ih b (bitUpdate k bit q)

  have run_absorbed : ∀ (k : ℕ) (w : List Bool),
      runWord (bitUpdate k) w none = none := by
    intro k w
    induction w with
    | nil => rfl
    | cons bit w ih => simpa only [runWord,bitUpdate] using ih

  have scanner_value_joint :
      ∀ (k : ℕ) (hk : 2 ≤ k) (w : List Bool) (n : ℕ) (a : ZMod 2) (s : Fin k),
        runWord (bitUpdate k) w (some ⟨a,(n : ZMod (k+1)),s.val⟩) =
          ((D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.scanner k (by omega)).evalFrom s w).map
            (fun tail => ⟨a+D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.value k n w,((n+w.length : ℕ) : ZMod (k+1)),tail.val⟩) := by
    intro k hk w
    induction w with
    | nil => intro n a s; simp [runWord,PartialDFA.evalFrom,runTransition,D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.value]
    | cons bit w ih =>
        intro n a s
        cases bit with
        | false =>
            have h := ih (n+1) a ⟨0,by omega⟩
            simpa only [runWord,bitUpdate,Bool.false_eq_true,if_false,
              PartialDFA.evalFrom,runTransition,D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.scanner,D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.value,List.length_cons,
              Nat.cast_add,Nat.cast_one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,
              zero_add,add_zero] using h
        | true =>
            by_cases safe : s.val+1<k
            · have h := ih (n+1) (a+coefficient k (n : ZMod (k+1))) ⟨s.val+1,safe⟩
              simpa only [runWord,bitUpdate,if_true,safe,if_pos,dite_true,
                PartialDFA.evalFrom,runTransition,D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.scanner,D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.value,List.length_cons,
                Nat.cast_add,Nat.cast_one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,
                ← weight_coefficient k hk n,originalWeight,add_assoc] using h
            · simp only [runWord,bitUpdate,if_true,safe,if_false,dite_false,run_absorbed,
                PartialDFA.evalFrom,runTransition,D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.scanner,dif_neg safe,Option.map_none]

  have record_run : ∀ (k : ℕ) (hk : 2 ≤ k) (w : List Bool),
      OriginalRecord k (by omega) w =
        runWord (bitUpdate k) w (some ⟨0,0,0⟩) := by
    intro k hk w
    have h := scanner_value_joint k hk w 0 0 ⟨0,by omega⟩
    simpa only [OriginalRecord,PartialDFA.eval,D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.scanner,Nat.cast_zero,
      Nat.zero_add,zero_add] using h.symm

  have record_append : ∀ (k : ℕ) (hk : 2 ≤ k) (w b : List Bool),
      OriginalRecord k (by omega) (w++b) =
        runWord (bitUpdate k) b (OriginalRecord k (by omega) w) := by
    intro k hk w b
    rw [record_run k hk,run_append,record_run k hk]

  have output_record : ∀ (k : ℕ) (hk : 0<k) (w : List Bool),
      D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.output k hk w = endpointReading (OriginalRecord k hk w) := by
    intro k hk w
    unfold D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.output OriginalRecord
    cases (D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.scanner k hk).eval w <;> rfl

  have execute_same : ∀ {Y : Type z} (k m : ℕ) (hk : 2 ≤ k)
      (π : D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.Selector m Y) (d : ℕ) (w : List Bool) (y₀ : Option (ZMod 2)) (archive : D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.Archive m),
      D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.execute k (by omega) π d w y₀ archive =
        NativeExecute π d (OriginalRecord k (by omega) w) y₀ archive := by
    intro Y k m hk π d
    induction d with
    | zero => intros; rfl
    | succ d ih =>
        intro w y₀ archive
        cases selected : π y₀ archive with
        | inl label => simp only [D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.execute,NativeExecute,selected]
        | inr B =>
            simp only [D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.execute,NativeExecute,selected]
            rw [ih,output_record,record_append k hk]
            rfl
  have everyBlockLegal (word : Fin m → Bool) : DBonacciAdmissible k m word := by
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have safe := runAdmissible_eq_true_of_length_le (k - 1) (k - 1) m word (by omega) le_rfl
    simpa [hr, DBonacciAdmissible] using safe
  let asWord (bits : List Bool) (length : bits.length = m) : Fin m → Bool :=
    fun i => bits.get ⟨i.val, by rw [length]; exact i.isLt⟩
  have asWordLiteral (bits : List Bool) (length : bits.length = m) :
      List.ofFn (asWord bits length) = bits := by
    apply List.ext_getElem
    · simp [length]
    · intro i hleft hright
      simp [asWord]
  let zeroWord : Fin m → Bool := fun _ => false
  let pulseWord := asWord (List.replicate (m - 1) false ++ [true])
    (by simp only [List.length_append, List.length_replicate, List.length_singleton]; omega)
  let repairWord := asWord ([true] ++ List.replicate (m - 1) false)
    (by simp only [List.length_append, List.length_replicate, List.length_singleton]; omega)
  let belowWord := asWord (List.replicate (min j m) false ++ List.replicate (m - min j m) true)
    (by simp only [List.length_append, List.length_replicate, List.length_singleton]; omega)
  let d := j ⌈/⌉ m
  let a := (d - 1) * m
  let r := j - a
  let finalWord := asWord (List.replicate (min r m) true ++ List.replicate (m - min r m) false)
    (by simp only [List.length_append, List.length_replicate, List.length_singleton]; omega)
  let π : NarrowWindowCost.Selector m Y := fun initial archive =>
    match initial with
    | none => .inl bottom
    | some _ =>
      if j ≤ m then
        match archive with
        | [] => .inr (if j < m then belowWord else pulseWord)
        | [(_, reply)] => if reply = some (v + 1) then .inr repairWord else .inl A
        | _ =>
          if archive.getLast?.bind (fun entry => entry.2) = some v then
            .inl (if j < m then A else B)
          else .inl (if j < m then B else A)
      else
        if archive.length < d - 2 then .inr zeroWord
        else if archive.length = d - 2 then .inr pulseWord
        else if archive.length = d - 1 then
          if archive.getLast?.bind (fun entry => entry.2) = some (v + 1) then .inl A
          else .inr finalWord
        else
          if archive.getLast?.bind (fun entry => entry.2) = some (v + 1) then .inl B
          else .inl A
  have πlegal : ∀ initial archive word, π initial archive = .inr word →
      localAlphabet = true → DBonacciAdmissible k m word := by
    intro initial archive word selected onlyLocal
    exact everyBlockLegal word
  let trees (initial : Option (ZMod 2)) :=
    SelectorTree bottom π πlegal (max 2 d) initial []
  have πbottom : π none [] = .inl bottom := rfl
  have treeBottom : (trees none).result none = bottom ∧ (trees none).archive none = [] := by
    have executed : NativeExecute π (max 2 d) (none : Option (LiveRecord k)) none [] =
        some (bottom, 0) := by
      cases max 2 d <;> simp [NativeExecute, π]
    have matched := selectorTreeSuccess k m localAlphabet bottom π πlegal
      (max 2 d) none none [] bottom 0 executed
    exact ⟨matched.1, List.length_eq_zero_iff.mp matched.2.1⟩
  have rootZero (n : ℕ) (action : AllowedBlock k m localAlphabet)
      (next : Option (ZMod 2) → AcquisitionTree k m localAlphabet Y n)
      (correct : ∀ i s : ℕ, i ≤ k → s < k →
        (AcquisitionTree.step action next).result
          (some ⟨v, -(i : ZMod (k + 1)), s⟩) = if i = j then B else A) :
      action.val ⟨0, by omega⟩ = false := by
    by_contra notZero
    have headOne : action.val ⟨0, by omega⟩ = true := by
      cases h : action.val ⟨0, by omega⟩ with
      | false => exact False.elim (notZero h)
      | true => rfl
    have reject (i : ℕ) :
        runBits k action.val (some ⟨v, -(i : ZMod (k + 1)), k - 1⟩) = none := by
      obtain ⟨width, widthEq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      cases widthEq
      have badSeam : ¬ k - 1 + 1 < k := by omega
      have headOne' : action.val 0 = true := headOne
      simp only [runBits, List.ofFn_succ, runWord, bitUpdate, headOne',
        ↓reduceIte, if_true, badSeam, if_false]
      exact absorbed _
    have left := correct 0 (k - 1) (by omega) (by omega)
    have right := correct j (k - 1) hjk (by omega)
    rw [AcquisitionTree.result, reject 0] at left
    rw [AcquisitionTree.result, reject j] at right
    simp only [endpointReading, if_pos rfl, if_neg (by omega : ¬ 0 = j)] at left right
    exact hAB (left.symm.trans right)
  have quietZero (t : ℕ) (lo : 1 ≤ t) (hi : t + 1 < j) :
      coefficient k (t : ZMod (k + 1)) = 0 := by
    rw [edge]
    have first := indexedMarker 0 t (by omega) (by omega)
    have second := indexedMarker 0 (t + 1) (by omega) (by omega)
    simp only [Nat.cast_zero, neg_zero, zero_add] at first second
    rw [first, show (t : ZMod (k + 1)) + 1 = ((t + 1 : ℕ) : ZMod (k + 1)) by push_cast; rfl,
      second]
    simp [show t ≠ 0 by omega, show t + 1 ≠ 0 by omega]
  have quietTarget (t : ℕ) (hi : t + 1 < j) :
      coefficient k (-(j : ZMod (k + 1)) + (t : ℕ)) = 0 := by
    rw [edge, indexedMarker j t hjk (by omega)]
    have shifted : -(j : ZMod (k + 1)) + (t : ℕ) + 1 =
        -(j : ZMod (k + 1)) + ((t + 1 : ℕ) : ZMod (k + 1)) := by push_cast; abel
    rw [shifted, indexedMarker j (t + 1) hjk (by omega)]
    simp [show t ≠ j by omega, show t + 1 ≠ j by omega]
  have silentBits : ∀ (bits : List Bool) (t s : ℕ) (value : ZMod 2),
      s < k → 1 ≤ t → t + bits.length < j →
      ∃ tail : Option ℕ,
        runWord (bitUpdate k) bits (some ⟨value, (t : ℕ), s⟩) =
          tail.map (fun r => ⟨value, ((t + bits.length : ℕ) : ZMod (k + 1)), r⟩) ∧
        runWord (bitUpdate k) bits (some ⟨value, -(j : ZMod (k + 1)) + (t : ℕ), s⟩) =
          tail.map (fun r => ⟨value, -(j : ZMod (k + 1)) + ((t + bits.length : ℕ) : ZMod (k + 1)), r⟩) ∧
        ∀ r, tail = some r → r < k := by
    intro bits
    induction bits with
    | nil =>
        intro t s value hs lo hi
        exact ⟨some s, by simp [runWord], by simp [runWord], by intro r hr; cases hr; exact hs⟩
    | cons bit bits ih =>
        intro t s value hs lo hi
        have silent : t + 1 < j := by simp only [List.length_cons] at hi; omega
        have phase : (t : ZMod (k + 1)) + 1 = ((t + 1 : ℕ) : ZMod (k + 1)) := by push_cast; rfl
        have targetPhase : -(j : ZMod (k + 1)) + (t : ℕ) + 1 =
            -(j : ZMod (k + 1)) + ((t + 1 : ℕ) : ZMod (k + 1)) := by push_cast; abel
        cases bit with
        | false =>
            obtain ⟨tail, first, second, bound⟩ := ih (t + 1) 0 value (by omega) (by omega)
              (by simp only [List.length_cons] at hi; omega)
            refine ⟨tail, ?_, ?_, bound⟩
            · simpa only [runWord, bitUpdate, Bool.false_eq_true, if_false, phase,
                List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm 1 bits.length] using first
            · simpa only [runWord, bitUpdate, Bool.false_eq_true, if_false, targetPhase,
                List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm 1 bits.length] using second
        | true =>
            by_cases safe : s + 1 < k
            · obtain ⟨tail, first, second, bound⟩ := ih (t + 1) (s + 1) value safe (by omega)
                (by simp only [List.length_cons] at hi; omega)
              refine ⟨tail, ?_, ?_, bound⟩
              · simpa only [runWord, bitUpdate, ↓reduceIte, if_true, safe, if_pos,
                  quietZero t lo silent, add_zero, phase, List.length_cons,
                  Nat.add_assoc, Nat.add_left_comm, Nat.add_comm 1 bits.length] using first
              · simpa only [runWord, bitUpdate, ↓reduceIte, if_true, safe, if_pos,
                  quietTarget t silent, add_zero, targetPhase, List.length_cons,
                  Nat.add_assoc, Nat.add_left_comm, Nat.add_comm 1 bits.length] using second
            · refine ⟨none, ?_, ?_, by simp⟩
              · simp [runWord, bitUpdate, safe, absorbed]
              · simp [runWord, bitUpdate, safe, absorbed]
  have silentTree : ∀ (n : ℕ) (tree : AcquisitionTree k m localAlphabet Y n)
      (t s : ℕ) (value : ZMod 2), s < k → 1 ≤ t → t + n * m < j →
      tree.result (some ⟨value, (t : ℕ), s⟩) =
        tree.result (some ⟨value, -(j : ZMod (k + 1)) + (t : ℕ), s⟩) ∧
      tree.archive (some ⟨value, (t : ℕ), s⟩) =
        tree.archive (some ⟨value, -(j : ZMod (k + 1)) + (t : ℕ), s⟩) := by
    intro n tree
    induction tree with
    | stop label => intros; exact ⟨rfl, rfl⟩
    | @step n action next ih =>
        intro t s value hs lo hi
        have blockBound : t + (List.ofFn action.val).length < j := by
          rw [List.length_ofFn]
          nlinarith
        obtain ⟨tail, first, second, bound⟩ := silentBits (List.ofFn action.val) t s value hs lo blockBound
        rw [List.length_ofFn] at first second
        change runBits k action.val (some ⟨value, (t : ℕ), s⟩) = _ at first
        change runBits k action.val (some ⟨value, -(j : ZMod (k + 1)) + (t : ℕ), s⟩) = _ at second
        cases tail with
        | none => simp only [AcquisitionTree.result, AcquisitionTree.archive, first, second,
            Option.map_none, and_self, true_and]
        | some r =>
            have hr : r < k := bound r rfl
            have future : t + m + n * m < j := by nlinarith
            have equal := ih (some value) (t + m) r value hr (by omega) future
            simpa only [AcquisitionTree.result, AcquisitionTree.archive, first, second,
              Option.map_some, endpointReading, List.cons.injEq, and_true, true_and] using equal
  have belowNative (below : j < m) (i s : ℕ) (hi : i ≤ k) (hs : s < k) :
      NativeExecute π 2 (some ⟨v, -(i : ZMod (k + 1)), s⟩) (some v) [] =
        some (if i = j then B else A, if i = j ∨ i = m then 2 else 1) := by
    have root := rootBelow i s hi hs below
    have repairSafe : m - j + 1 < k := by omega
    have second := repair i (m - j) hi repairSafe (v + 1)
    simp only [List.singleton_append] at second
    by_cases target : i = j
    · subst i
      simp [nativeStep, nativeZero, π, below, below.le, belowWord, repairWord, runBits,
        asWordLiteral, min_eq_left below.le, root, second, endpointReading, show j ≠ m by omega,
        show m ≠ j by omega, show m + 1 ≠ j by omega, CharTwo.add_self_eq_zero, add_assoc]
    · by_cases helper : i = m
      · subst i
        simp only [neg_add_cancel] at second
        simp [nativeStep, nativeZero, π, below, below.le, belowWord, repairWord, runBits,
          asWordLiteral, min_eq_left below.le, root, second, endpointReading, target,
          show j ≠ m by omega, show m + 1 ≠ m by omega, CharTwo.add_self_eq_zero, add_assoc]
      · simp [nativeStep, nativeZero, π, below, below.le, belowWord, repairWord, runBits,
          asWordLiteral, min_eq_left below.le, root, endpointReading, target, helper, Ne.symm target, Ne.symm helper]

  have atNative (atIndex : j = m) (i s : ℕ) (hi : i ≤ k) (hs : s < k) :
      NativeExecute π 2 (some ⟨v, -(i : ZMod (k + 1)), s⟩) (some v) [] =
        some (if i = j then B else A, if i = m - 1 ∨ i = m then 2 else 1) := by
    have root := rootAt i s hi hs
    have second := repair i 1 hi (by omega) (v + 1)
    simp only [List.singleton_append] at second
    by_cases target : i = m
    · subst i
      simp only [neg_add_cancel] at second
      simp [nativeStep, nativeZero, π, atIndex, pulseWord, repairWord, runBits,
        asWordLiteral, root, second, endpointReading, show m - 1 ≠ m by omega,
        show m + 1 ≠ m by omega, CharTwo.add_self_eq_zero, add_assoc]
    · by_cases helper : i = m - 1
      · subst i
        simp [nativeStep, nativeZero, π, atIndex, pulseWord, repairWord, runBits,
          asWordLiteral, root, second, endpointReading, target,
          show m ≠ m - 1 by omega, show m + 1 ≠ m - 1 by omega,
          CharTwo.add_self_eq_zero, add_assoc]
      · simp [nativeStep, nativeZero, π, atIndex, pulseWord, repairWord, runBits,
          asWordLiteral, root, endpointReading, target, helper, Ne.symm target, Ne.symm helper]

  have actualSource (i s : ℕ) (hi : i ≤ k) (hs : s < k) :
      ∃ w : List Bool, m ∣ w.length ∧
        OriginalRecord k (by omega) w = some ⟨v, -(i : ZMod (k + 1)), s⟩ ∧
        NarrowWindowCost.output k (by omega) w = some v ∧ k + 1 ∣ w.length + i := by
    obtain ⟨N, word, width, admissible, realized, rest⟩ :=
      joint_history_realization k m hk (by omega) v (-(i : ZMod (k + 1))) s hs
        (by rw [hg]; exact one_dvd _)
    let w := List.ofFn word
    have record : OriginalRecord k (by omega) w = some ⟨v, -(i : ZMod (k + 1)), s⟩ := by
      rw [record_run k hk]
      exact realized
    refine ⟨w, by simpa [w] using width, record, ?_, ?_⟩
    · rw [output_record, record]
      rfl
    · have phase : (w.length : ZMod (k + 1)) = -(i : ZMod (k + 1)) := by
        unfold OriginalRecord at record
        cases scan : (NarrowWindowCost.scanner k (by omega)).eval w with
        | none => simp [scan] at record
        | some tail =>
            simp only [scan, Option.map_some, Option.some.injEq] at record
            exact congrArg LiveRecord.phase record
      apply (ZMod.natCast_eq_zero_iff (w.length + i) (k + 1)).mp
      rw [Nat.cast_add, phase, neg_add_cancel]
  have rawRecord (w : List Bool) (i : Fin ((k + 1) / Nat.gcd m (k + 1)))
      (observed : NarrowWindowCost.output k (by omega) w = some v)
      (indexed : k + 1 ∣ w.length + i.val * Nat.gcd m (k + 1)) :
      ∃ s < k, OriginalRecord k (by omega) w = some ⟨v, -(i.val : ZMod (k + 1)), s⟩ := by
    have indexed' : k + 1 ∣ w.length + i.val := by
      simpa only [hg, Nat.mul_one] using indexed
    have phaseZero := (ZMod.natCast_eq_zero_iff (w.length + i.val) (k + 1)).mpr indexed'
    rw [Nat.cast_add] at phaseZero
    have phase := eq_neg_of_add_eq_zero_left phaseZero
    unfold NarrowWindowCost.output at observed
    cases scan : (NarrowWindowCost.scanner k (by omega)).eval w with
    | none => simp [scan] at observed
    | some tail =>
        simp only [scan, Option.map_some, Option.some.injEq] at observed
        refine ⟨tail.val, tail.isLt, ?_⟩
        simp [OriginalRecord, scan, observed, phase]
  have feasibleTree (n : ℕ)
      (feasible : NarrowWindowCost.Feasible k m (by omega) localAlphabet
        (fun i => if i.val = j then B else A) bottom v n) :
      ∃ tree : AcquisitionTree k m localAlphabet Y n,
        ∀ i s : ℕ, i ≤ k → s < k →
          tree.result (some ⟨v, -(i : ZMod (k + 1)), s⟩) = if i = j then B else A := by
    obtain ⟨σ, legal, rejected, correct⟩ := feasible
    refine ⟨SelectorTree bottom σ legal n (some v) [], ?_⟩
    intro i s hi hs
    obtain ⟨w, width, record, observed, indexed⟩ := actualSource i s hi hs
    let index : Fin ((k + 1) / Nat.gcd m (k + 1)) := ⟨i, by rw [hg]; simp only [Nat.div_one]; omega⟩
    have indexed' : k + 1 ∣ w.length + index.val * Nat.gcd m (k + 1) := by
      simpa only [index, hg, Nat.mul_one] using indexed
    obtain ⟨c, bounded, success⟩ := correct w index width observed indexed'
    rw [execute_same k m hk σ n, record] at success
    exact (selectorTreeSuccess k m localAlphabet bottom σ legal n
      (some ⟨v, -(i : ZMod (k + 1)), s⟩) (some v) [] _ c success).1

  have rootSilent (word : Fin m → Bool) (headZero : word ⟨0, by omega⟩ = false)
      (early : m < j) :
      ∃ tail : Option ℕ,
        runBits k word (some ⟨v, 0, 0⟩) =
          tail.map (fun s => ⟨v, (m : ZMod (k + 1)), s⟩) ∧
        runBits k word (some ⟨v, -(j : ZMod (k + 1)), 0⟩) =
          tail.map (fun s => ⟨v, -(j : ZMod (k + 1)) + (m : ℕ), s⟩) ∧
        ∀ s, tail = some s → s < k := by
    obtain ⟨width, widthEq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    cases widthEq
    have headZero' : word 0 = false := headZero
    obtain ⟨tail, first, second, bounded⟩ :=
      silentBits (List.ofFn (Fin.tail word)) 1 0 v (by omega) le_rfl
        (by rw [List.length_ofFn]; omega)
    refine ⟨tail, ?_, ?_, bounded⟩
    · simpa +unfoldPartialApp only [runBits, List.ofFn_succ, runWord, bitUpdate, headZero', Fin.tail,
        Bool.false_eq_true, if_false, zero_add, Nat.cast_one, List.length_ofFn,
        Nat.one_add] using first
    · simpa +unfoldPartialApp only [runBits, List.ofFn_succ, runWord, bitUpdate, headZero', Fin.tail,
        Bool.false_eq_true, if_false, Nat.cast_one, List.length_ofFn,
        Nat.one_add] using second
  have arrivalLower (n : ℕ) (tree : AcquisitionTree k m localAlphabet Y n)
      (correct : ∀ i s : ℕ, i ≤ k → s < k →
        tree.result (some ⟨v, -(i : ZMod (k + 1)), s⟩) = if i = j then B else A) :
      j ⌈/⌉ m ≤ n := by
    by_contra tooEarly
    have early : n * m < j := by
      by_contra late
      have bound : j ⌈/⌉ m ≤ n := (ceilDiv_le_iff_le_mul (by omega : 0 < m)).mpr
        (by simpa only [Nat.mul_comm] using Nat.le_of_not_gt late)
      exact tooEarly bound
    have left := correct 0 0 (by omega) (by omega)
    have right := correct j 0 hjk (by omega)
    simp only [Nat.cast_zero, neg_zero, if_neg (by omega : ¬ 0 = j), if_pos rfl] at left right
    cases tree with
    | stop label =>
        exact hAB (left.symm.trans right)
    | @step n action next =>
        have headZero := rootZero n action next correct
        have blockEarly : m < j := by nlinarith
        obtain ⟨tail, first, second, bounded⟩ := rootSilent action.val headZero blockEarly
        have same : (AcquisitionTree.step action next).result (some ⟨v, 0, 0⟩) =
            (AcquisitionTree.step action next).result (some ⟨v, -(j : ZMod (k + 1)), 0⟩) := by
          cases tail with
          | none => simp only [AcquisitionTree.result, first, second, Option.map_none]
          | some s =>
              have hs := bounded s rfl
              have restEarly : m + n * m < j := by nlinarith
              have rest := (silentTree n (next (some v)) m s v hs (by omega) restEarly).1
              simpa only [AcquisitionTree.result, first, second, Option.map_some,
                endpointReading] using rest
        exact hAB (left.symm.trans (same.trans right))

  have twoLower (n : ℕ) (tree : AcquisitionTree k m localAlphabet Y n)
      (correct : ∀ i s : ℕ, i ≤ k → s < k →
        tree.result (some ⟨v, -(i : ZMod (k + 1)), s⟩) = if i = j then B else A) :
      2 ≤ n := by
    by_contra tooSmall
    have small : n ≤ 1 := by omega
    have zeroLabel := correct 0 0 (by omega) (by omega)
    have targetLabel := correct j 0 hjk (by omega)
    simp only [Nat.cast_zero, neg_zero, if_neg (by omega : ¬ 0 = j), if_pos rfl]
      at zeroLabel targetLabel
    interval_cases n
    · cases tree with
      | stop label => exact hAB (zeroLabel.symm.trans targetLabel)
    · cases tree with
      | stop label => exact hAB (zeroLabel.symm.trans targetLabel)
      | step action next =>
          have headZero := rootZero 0 action next correct
          have leafConstant (reply : Option (ZMod 2)) (q q' : Option (LiveRecord k)) :
              (next reply).result q = (next reply).result q' := by
            cases next reply with
            | stop label => rfl
          let δ (i : Fin (k + 1)) : ZMod 2 :=
            wordIncrement k (-(i.val : ZMod (k + 1))) action.val
          let origin : Fin (k + 1) := ⟨0, by omega⟩
          let target : Fin (k + 1) := ⟨j, by omega⟩
          have run (i : Fin (k + 1)) :
              runBits k action.val (some ⟨v, -(i.val : ZMod (k + 1)), 0⟩) =
                some ⟨v + δ i, -(i.val : ZMod (k + 1)) + (m : ℕ), tailAfter 0 action.val⟩ := by
            have model := (literal_block_execution k hk m action.val v
              (-(i.val : ZMod (k + 1))) 0 (by omega)).1
            have safe := runAdmissible_eq_true_of_length_le (k - 1) (k - 1) m
              action.val (by omega) le_rfl
            simpa only [Nat.sub_zero, safe, if_true, δ] using model
          have originQuiet : δ origin = 0 := by
            simp only [δ, origin, Nat.cast_zero, neg_zero, wordIncrement, zero_add]
            apply Finset.sum_eq_zero
            intro t ht
            by_cases first : t.val = 0
            · have eq : t = ⟨0, by omega⟩ := Fin.ext first
              simp [eq, headZero]
            · have lower : 1 ≤ t.val := by omega
              have upper : t.val + 1 ≤ k := by omega
              have left := indexedMarker 0 t.val (by omega) (by omega)
              have right := indexedMarker 0 (t.val + 1) (by omega) upper
              simp only [Nat.cast_zero, neg_zero, zero_add] at left right
              have shift : (t.val : ZMod (k + 1)) + 1 =
                  ((t.val + 1 : ℕ) : ZMod (k + 1)) := by push_cast; rfl
              have quiet : coefficient k (t.val : ZMod (k + 1)) = 0 := by
                rw [edge, left, shift, right]
                simp [first, show t.val + 1 ≠ 0 by omega]
              simp only [quiet, ite_self]
          have indist (i l : Fin (k + 1)) (same : δ i = δ l) :
              (if i.val = j then B else A) = (if l.val = j then B else A) := by
            have left := correct i.val 0 (by omega) (by omega)
            have right := correct l.val 0 (by omega) (by omega)
            have equal : (AcquisitionTree.step action next).result
                (some ⟨v, -(i.val : ZMod (k + 1)), 0⟩) =
                (AcquisitionTree.step action next).result
                  (some ⟨v, -(l.val : ZMod (k + 1)), 0⟩) := by
              simp only [AcquisitionTree.result, run, endpointReading, same]
              exact leafConstant _ _ _
            exact left.symm.trans (equal.trans right)
          have binary (x : ZMod 2) : x = 0 ∨ x = 1 := by
            fin_cases x
            · exact Or.inl rfl
            · exact Or.inr rfl
          have targetOne : δ target = 1 := by
            apply (binary (δ target)).resolve_left
            intro quiet
            have impossible := indist target origin (quiet.trans originQuiet.symm)
            simp only [target, origin, if_pos rfl, if_neg (by omega : ¬ 0 = j)] at impossible
            exact hAB impossible.symm
          have onlyTarget (i : Fin (k + 1)) : δ i = if i = target then 1 else 0 := by
            by_cases isTarget : i = target
            · subst i
              rw [if_pos rfl]
              exact targetOne
            · rw [if_neg isTarget]
              apply (binary (δ i)).resolve_right
              intro positive
              have impossible := indist i target (positive.trans targetOne.symm)
              have indexDifferent : i.val ≠ j := by
                intro eq
                exact isTarget (Fin.ext eq)
              simp only [target, if_pos rfl, if_neg indexDifferent] at impossible
              exact hAB impossible
          have sumMarker (t : ℕ) (ht : t ≤ k) :
              (∑ i : Fin (k + 1), marker (-(i.val : ZMod (k + 1)) + (t : ℕ))) = 1 := by
            calc
              _ = ∑ i : Fin (k + 1),
                  if (⟨t, by omega⟩ : Fin (k + 1)) = i then (1 : ZMod 2) else 0 := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [indexedMarker i.val t (by omega) ht]
                simp only [Fin.ext_iff]
              _ = 1 := by simp
          have evenCharge : (∑ i : Fin (k + 1), δ i) = 0 := by
            simp only [δ, wordIncrement]
            rw [Finset.sum_comm]
            apply Finset.sum_eq_zero
            intro t ht
            cases bit : action.val t with
            | false => simp [bit]
            | true =>
                simp only [bit, if_true]
                simp_rw [edge]
                have shift (i : Fin (k + 1)) :
                    -(i.val : ZMod (k + 1)) + (t.val : ℕ) + 1 =
                      -(i.val : ZMod (k + 1)) + ((t.val + 1 : ℕ) : ZMod (k + 1)) := by
                  push_cast; abel
                simp_rw [shift]
                rw [Finset.sum_add_distrib, sumMarker t.val (by omega),
                  sumMarker (t.val + 1) (by omega)]
                exact CharTwo.add_self_eq_zero 1
          have chargeOne : (∑ i : Fin (k + 1), δ i) = 1 := by
            simp_rw [onlyTarget]
            simp
          have impossible : (1 : ZMod 2) = 0 := chargeOne.symm.trans evenCharge
          exact one_ne_zero impossible
  have lowerAll (n : ℕ)
      (feasible : NarrowWindowCost.Feasible k m (by omega) localAlphabet
        (fun i => if i.val = j then B else A) bottom v n) : max 2 (j ⌈/⌉ m) ≤ n := by
    obtain ⟨tree, correct⟩ := feasibleTree n feasible
    exact max_le (twoLower n tree correct) (arrivalLower n tree correct)

  have waitNative (remote : m < j) :
      ∀ n t (phi : ZMod (k + 1)) s, t + n = d - 2 →
        NativeExecute π (n + 2) (some ⟨v, phi, s⟩) (some v)
            (List.replicate t (zeroWord, some v)) =
          (NativeExecute π 2
            (some ⟨v, phi + ((n * m : ℕ) : ZMod (k + 1)), if n = 0 then s else 0⟩)
            (some v) (List.replicate (d - 2) (zeroWord, some v))).map
              (fun result => (result.1, result.2 + n)) ∧
        ((SelectorTree bottom π πlegal (n + 2) (some v)
          (List.replicate t (zeroWord, some v))).archive (some ⟨v, phi, s⟩)).map
            (fun entry => (entry.1.val, entry.2)) =
          List.replicate n (zeroWord, some v) ++
          ((SelectorTree bottom π πlegal 2 (some v)
            (List.replicate (d - 2) (zeroWord, some v))).archive
            (some ⟨v, phi + ((n * m : ℕ) : ZMod (k + 1)), if n = 0 then s else 0⟩)).map
              (fun entry => (entry.1.val, entry.2)) := by
    intro n
    induction n with
    | zero =>
        intro t phi s count
        have same : t = d - 2 := by omega
        simp only [same, Nat.zero_mul, Nat.cast_zero, add_zero, if_pos rfl, Nat.add_zero]
        constructor
        · change _ = Option.map id _
          rw [Option.map_id]
          rfl
        · rfl
    | succ n ih =>
        intro t phi s count
        have earlier : t < d - 2 := by omega
        have selected : π (some v) (List.replicate t (zeroWord, some v)) = .inr zeroWord := by
          simp only [π, if_neg (by omega : ¬ j ≤ m), List.length_replicate, if_pos earlier]
        have runZero : runBits k zeroWord (some ⟨v, phi, s⟩) = some ⟨v, phi + (m : ℕ), 0⟩ := by
          simp only [runBits, zeroWord, List.ofFn_const, zeros,
            if_neg (by omega : m ≠ 0)]
        have nextArchive : List.replicate t (zeroWord, some v) ++ [(zeroWord, some v)] =
            List.replicate (t + 1) (zeroWord, some v) := by
          rw [List.replicate_succ']
        have phase : phi + (m : ℕ) + ((n * m : ℕ) : ZMod (k + 1)) =
            phi + (((n + 1) * m : ℕ) : ZMod (k + 1)) := by
          push_cast
          ring
        constructor
        · rw [show n + 1 + 2 = (n + 2) + 1 by omega]
          rw [nativeStep π (n + 2) (some ⟨v, phi, s⟩) (some v)
            (List.replicate t (zeroWord, some v)), selected]
          simp only [runZero, endpointReading, nextArchive]
          rw [(ih (t + 1) (phi + (m : ℕ)) 0 (by omega)).1]
          simp only [phase, ite_self, if_neg (by omega : n + 1 ≠ 0), Option.map_map]
          congr 1
        · have expanded :
              SelectorTree bottom π πlegal ((n + 2) + 1) (some v)
                (List.replicate t (zeroWord, some v)) =
              AcquisitionTree.step ⟨zeroWord, πlegal (some v)
                  (List.replicate t (zeroWord, some v)) zeroWord selected⟩
                (fun reply => SelectorTree bottom π πlegal (n + 2) (some v)
                  (List.replicate t (zeroWord, some v) ++ [(zeroWord, reply)])) := by
              simp only [SelectorTree, Nat.rec_add_one]
              split
              · rename_i label chosen
                cases chosen.symm.trans selected
              · rename_i word chosen
                have same : word = zeroWord := Sum.inr.inj (chosen.symm.trans selected)
                subst word
                rfl
          rw [show n + 1 + 2 = (n + 2) + 1 by omega, expanded]
          simp only [AcquisitionTree.archive, runZero, endpointReading, nextArchive, List.map_cons]
          rw [(ih (t + 1) (phi + (m : ℕ)) 0 (by omega)).2]
          simp only [phase, ite_self, if_neg (by omega : n + 1 ≠ 0),
            List.replicate_succ, List.cons_append]

  have pulseAfterWait (remote : m < j) (i s : ℕ) (hi : i ≤ k) (hs : s < k) :
      runBits k pulseWord
        (some ⟨v, -(i : ZMod (k + 1)) + (((d - 2) * m : ℕ) : ZMod (k + 1)),
          if d - 2 = 0 then s else 0⟩) =
      some ⟨v + (if a - 1 = i then 1 else 0) + (if a = i then 1 else 0),
        -(i : ZMod (k + 1)) + (a : ℕ), 1⟩ := by
    have combined := remotePulse remote i s hi hs
    dsimp only at combined
    rw [appendRun, zeros] at combined
    have countZero : (d - 2) * m = 0 ↔ d - 2 = 0 := by
      simp only [Nat.mul_eq_zero, show m ≠ 0 by omega, or_false]
    simpa only [runBits, pulseWord, asWordLiteral, d, a, countZero] using combined

  have remoteTwo (remote : m < j) (i s : ℕ) (hi : i ≤ k) (hs : s < k) :
      NativeExecute π 2
        (some ⟨v, -(i : ZMod (k + 1)) + (((d - 2) * m : ℕ) : ZMod (k + 1)),
          if d - 2 = 0 then s else 0⟩)
        (some v) (List.replicate (d - 2) (zeroWord, some v)) =
        some (if i = j then B else A, if i = a - 1 ∨ i = a then 1 else 2) := by
    obtain ⟨hd, ha, hr, hrm, sum, seam⟩ := remoteArithmetic remote
    change 2 ≤ d at hd
    change a < j at ha
    change 1 ≤ r at hr
    change r ≤ m at hrm
    change a + r = j at sum
    change 1 + r < k at seam
    have aPositive : 2 ≤ a := by
      have hcount : 1 ≤ d - 1 := by omega
      have bound := Nat.mul_le_mul_right m hcount
      simp only [Nat.one_mul] at bound
      change m ≤ a at bound
      omega
    have penultimate : d - 2 + 1 = d - 1 := by omega
    have notLast : d - 2 ≠ d - 1 := by omega
    have notLast' : d - 1 ≠ d - 2 := by omega
    have notWaiting : ¬ d - 1 < d - 2 := by omega
    have completed : d - 2 + 2 = d := by omega
    have finalDifferent : d ≠ d - 1 := by omega
    have finishedWaiting : ¬ d < d - 2 := by omega
    have finishedPulse : d ≠ d - 2 := by omega
    have root := pulseAfterWait remote i s hi hs
    have final := remoteFinal remote i hi v
    dsimp only at final
    have finalRun : runBits k finalWord
        (some ⟨v, -(i : ZMod (k + 1)) + (a : ℕ), 1⟩) =
      some ⟨v + (if a = i then 1 else 0) + (if j = i then 1 else 0),
        -(i : ZMod (k + 1)) + ((d * m : ℕ) : ZMod (k + 1)),
        if r = m then 1 + r else 0⟩ := by
      simpa only [runBits, finalWord, asWordLiteral, min_eq_left hrm, d, a, r] using final
    have selectedRoot : π (some v) (List.replicate (d - 2) (zeroWord, some v)) = .inr pulseWord := by
      simp [π, show ¬ j ≤ m by omega]
    simp only [nativeStep, nativeZero]
    rw [selectedRoot]
    simp only [root, endpointReading]
    by_cases excluded : i = a - 1 ∨ i = a
    · rcases excluded with first | second
      · simp [π, show ¬ j ≤ m by omega, penultimate, notLast, notLast', notWaiting, completed,
          finalDifferent, finishedWaiting, finishedPulse,
          root, endpointReading, first, show a ≠ a - 1 by omega,
          show a - 1 ≠ j by omega]
      · simp [π, show ¬ j ≤ m by omega, penultimate, notLast, notLast', notWaiting, completed,
          finalDifferent, finishedWaiting, finishedPulse,
          root, endpointReading, second, show a - 1 ≠ a by omega,
          show a ≠ j by omega]
    · have notFirst : i ≠ a - 1 := fun eq => excluded (Or.inl eq)
      have notSecond : i ≠ a := fun eq => excluded (Or.inr eq)
      simp only [if_neg (Ne.symm notFirst), if_neg (Ne.symm notSecond), add_zero]
      have choice : π (some v)
          (List.replicate (d - 2) (zeroWord, some v) ++ [(pulseWord, some v)]) = .inr finalWord := by
        simp [π, show ¬ j ≤ m by omega, penultimate, notLast', notWaiting]
      rw [choice]
      simp only [finalRun, endpointReading]
      by_cases target : i = j
      · subst i
        simp [π, show ¬ j ≤ m by omega, penultimate, notLast, notLast', notWaiting, completed,
          finalDifferent, finishedWaiting, finishedPulse,
          notFirst, notSecond, Ne.symm notFirst, Ne.symm notSecond]
      · simp [π, show ¬ j ≤ m by omega, penultimate, notLast, notLast', notWaiting, completed,
          finalDifferent, finishedWaiting, finishedPulse,
          notFirst, notSecond, Ne.symm notFirst, Ne.symm notSecond, target, Ne.symm target]

  have nativeCorrect (i s : ℕ) (hi : i ≤ k) (hs : s < k) :
      ∃ c ≤ max 2 d, NativeExecute π (max 2 d)
        (some ⟨v, -(i : ZMod (k + 1)), s⟩) (some v) [] =
          some (if i = j then B else A, c) := by
    by_cases near : j ≤ m
    · have hd : d ≤ 1 := (ceilDiv_le_iff_le_mul (by omega : 0 < m)).mpr
        (by simpa only [Nat.mul_one] using near)
      have budget : max 2 d = 2 := max_eq_left (by omega)
      rw [budget]
      by_cases below : j < m
      · refine ⟨if i = j ∨ i = m then 2 else 1, ?_, belowNative below i s hi hs⟩
        split_ifs <;> omega
      · have atIndex : j = m := by omega
        refine ⟨if i = m - 1 ∨ i = m then 2 else 1, ?_, atNative atIndex i s hi hs⟩
        split_ifs <;> omega
    · have remote : m < j := by omega
      obtain ⟨hd, rest⟩ := remoteArithmetic remote
      change 2 ≤ d at hd
      have budget : max 2 d = d := max_eq_right hd
      have waiting := (waitNative remote (d - 2) 0 (-(i : ZMod (k + 1))) s (by omega)).1
      rw [remoteTwo remote i s hi hs] at waiting
      simp only [List.replicate_zero, Option.map_some] at waiting
      have count : d - 2 + 2 = d := by omega
      rw [count] at waiting
      rw [budget]
      refine ⟨(if i = a - 1 ∨ i = a then 1 else 2) + (d - 2), ?_, waiting⟩
      split_ifs <;> omega
  have attainingRaw (w : List Bool) (i : Fin ((k + 1) / Nat.gcd m (k + 1)))
      (width : m ∣ w.length)
      (observed : NarrowWindowCost.output k (by omega) w = some v)
      (indexed : k + 1 ∣ w.length + i.val * Nat.gcd m (k + 1)) :
      ∃ c ≤ max 2 d,
        NarrowWindowCost.execute k (by omega) π (max 2 d) w (some v) [] =
          some (if i.val = j then B else A, c) ∧
        (trees (some v)).result (OriginalRecord k (by omega) w) =
          (if i.val = j then B else A) ∧
        ((trees (some v)).archive (OriginalRecord k (by omega) w)).length = c := by
    obtain ⟨s, hs, record⟩ := rawRecord w i observed indexed
    have bound : i.val < k + 1 := by simpa only [hg, Nat.div_one] using i.isLt
    obtain ⟨c, bounded, native⟩ := nativeCorrect i.val s (by omega) hs
    have linked := selectorTreeSuccess k m localAlphabet bottom π πlegal (max 2 d)
      (some ⟨v, -(i.val : ZMod (k + 1)), s⟩) (some v) [] _ c native
    refine ⟨c, bounded, ?_, ?_, ?_⟩
    · rw [execute_same k m hk, record]
      exact native
    · simpa only [trees, record] using linked.1
    · simpa only [trees, record] using linked.2.1
  have upperRaw : NarrowWindowCost.Feasible k m (by omega) localAlphabet
      (fun i => if i.val = j then B else A) bottom v (max 2 d) := by
    refine ⟨π, πlegal, ?_, ?_⟩
    · intro w width rejected
      cases budget : max 2 d <;> simp only [NarrowWindowCost.execute, π]
    · intro w i width observed indexed
      obtain ⟨c, bounded, executed, result, archive⟩ := attainingRaw w i width observed indexed
      exact ⟨c, bounded, executed⟩
  refine ⟨⟨upperRaw, ?_⟩, π, trees, πlegal, πbottom, treeBottom.1, treeBottom.2, ?_, ?_⟩
  · intro n feasible
    exact lowerAll n feasible
  · intro i s hs
    have bound : i.val < k + 1 := by simpa only [hg, Nat.div_one] using i.isLt
    obtain ⟨c, bounded, native⟩ := nativeCorrect i.val s (by omega) hs
    have linked := selectorTreeSuccess k m localAlphabet bottom π πlegal (max 2 d)
      (some ⟨v, -(i.val : ZMod (k + 1)), s⟩) (some v) [] _ c native
    refine ⟨linked.1, ?_, ?_, ?_, ?_⟩
    · exact linked.2.1.trans_le bounded
    · by_cases near : j ≤ m
      · have hd : d ≤ 1 := (ceilDiv_le_iff_le_mul (by omega : 0 < m)).mpr
          (by simpa only [Nat.mul_one] using near)
        have budget : max 2 d = 2 := max_eq_left (by omega)
        change ∀ entry ∈ (SelectorTree bottom π πlegal (max 2 d) (some v) []).archive
          (some ⟨v, -(i.val : ZMod (k + 1)), s⟩), entry.2 ≠ none
        rw [budget]
        by_cases below : j < m
        · have root := rootBelow i.val s (by omega) hs below
          have rootRun : runBits k belowWord
              (some ⟨v, -(i.val : ZMod (k + 1)), s⟩) =
            some ⟨v + (if j = i.val then 1 else 0) + (if m = i.val then 1 else 0),
              -(i.val : ZMod (k + 1)) + (m : ℕ), m - j⟩ := by
            simpa only [runBits, belowWord, asWordLiteral, min_eq_left below.le] using root
          have second := repair i.val (m - j) (by omega) (by omega)
            (v + (if j = i.val then 1 else 0) + (if m = i.val then 1 else 0))
          have secondRun : runBits k repairWord
              (some ⟨v + (if j = i.val then 1 else 0) + (if m = i.val then 1 else 0),
                -(i.val : ZMod (k + 1)) + (m : ℕ), m - j⟩) =
            some ⟨v + (if j = i.val then 1 else 0) + (if m = i.val then 1 else 0) +
                (if m = i.val then 1 else 0) + (if m + 1 = i.val then 1 else 0),
              -(i.val : ZMod (k + 1)) + ((2 * m : ℕ) : ZMod (k + 1)), 0⟩ := by
            simpa only [runBits, repairWord, asWordLiteral] using second
          have selectedRoot : π (some v) [] = .inr belowWord := by simp [π, near, below]
          generalize scalarEq :
            v + (if j = i.val then 1 else 0) + (if m = i.val then 1 else 0) = value
            at rootRun secondRun
          have expanded : SelectorTree bottom π πlegal 2 (some v) [] =
              (match selected : π (some v) [] with
              | .inl label => AcquisitionTree.stop label
              | .inr word => AcquisitionTree.step ⟨word, πlegal (some v) [] word selected⟩
                  (fun reply => SelectorTree bottom π πlegal 1 (some v) [(word, reply)])) := rfl
          rw [expanded]
          split
          · rename_i label chosen
            cases chosen.symm.trans selectedRoot
          · rename_i word chosen
            have same : word = belowWord := Sum.inr.inj (chosen.symm.trans selectedRoot)
            subst word
            have tailExpanded (reply : Option (ZMod 2)) :
                SelectorTree bottom π πlegal 1 (some v) [(belowWord, reply)] =
                (match selected : π (some v) [(belowWord, reply)] with
                | .inl label => AcquisitionTree.stop label
                | .inr word => AcquisitionTree.step ⟨word,
                    πlegal (some v) [(belowWord, reply)] word selected⟩
                    (fun reply' => SelectorTree bottom π πlegal 0 (some v)
                      [(belowWord, reply), (word, reply')])) := rfl
            simp only [AcquisitionTree.archive, rootRun, endpointReading, tailExpanded]
            split
            · simp [AcquisitionTree.archive]
            · rename_i word chosen
              have selected : π (some v) [(belowWord, some value)] = .inr word := chosen
              simp only [π, if_pos near] at selected
              split_ifs at selected with positive
              · have same : word = repairWord := Sum.inr.inj selected.symm
                subst word
                simp [SelectorTree, Nat.rec_zero, AcquisitionTree.archive, secondRun, endpointReading]
        · have root := rootAt i.val s (by omega) hs
          have rootRun : runBits k pulseWord
              (some ⟨v, -(i.val : ZMod (k + 1)), s⟩) =
            some ⟨v + (if m - 1 = i.val then 1 else 0) + (if m = i.val then 1 else 0),
              -(i.val : ZMod (k + 1)) + (m : ℕ), 1⟩ := by
            simpa only [runBits, pulseWord, asWordLiteral] using root
          have second := repair i.val 1 (by omega) (by omega)
            (v + (if m - 1 = i.val then 1 else 0) + (if m = i.val then 1 else 0))
          have secondRun : runBits k repairWord
              (some ⟨v + (if m - 1 = i.val then 1 else 0) + (if m = i.val then 1 else 0),
                -(i.val : ZMod (k + 1)) + (m : ℕ), 1⟩) =
            some ⟨v + (if m - 1 = i.val then 1 else 0) + (if m = i.val then 1 else 0) +
                (if m = i.val then 1 else 0) + (if m + 1 = i.val then 1 else 0),
              -(i.val : ZMod (k + 1)) + ((2 * m : ℕ) : ZMod (k + 1)), 0⟩ := by
            simpa only [runBits, repairWord, asWordLiteral] using second
          have selectedRoot : π (some v) [] = .inr pulseWord := by simp [π, near, below]
          generalize scalarEq :
            v + (if m - 1 = i.val then 1 else 0) + (if m = i.val then 1 else 0) = value
            at rootRun secondRun
          have expanded : SelectorTree bottom π πlegal 2 (some v) [] =
              (match selected : π (some v) [] with
              | .inl label => AcquisitionTree.stop label
              | .inr word => AcquisitionTree.step ⟨word, πlegal (some v) [] word selected⟩
                  (fun reply => SelectorTree bottom π πlegal 1 (some v) [(word, reply)])) := rfl
          rw [expanded]
          split
          · rename_i label chosen
            cases chosen.symm.trans selectedRoot
          · rename_i word chosen
            have same : word = pulseWord := Sum.inr.inj (chosen.symm.trans selectedRoot)
            subst word
            have tailExpanded (reply : Option (ZMod 2)) :
                SelectorTree bottom π πlegal 1 (some v) [(pulseWord, reply)] =
                (match selected : π (some v) [(pulseWord, reply)] with
                | .inl label => AcquisitionTree.stop label
                | .inr word => AcquisitionTree.step ⟨word,
                    πlegal (some v) [(pulseWord, reply)] word selected⟩
                    (fun reply' => SelectorTree bottom π πlegal 0 (some v)
                      [(pulseWord, reply), (word, reply')])) := rfl
            simp only [AcquisitionTree.archive, rootRun, endpointReading, tailExpanded]
            split
            · simp [AcquisitionTree.archive]
            · rename_i word chosen
              have selected : π (some v) [(pulseWord, some value)] = .inr word := chosen
              simp only [π, if_pos near] at selected
              split_ifs at selected with positive
              · have same : word = repairWord := Sum.inr.inj selected.symm
                subst word
                simp [SelectorTree, Nat.rec_zero, AcquisitionTree.archive, secondRun, endpointReading]
      · have remote : m < j := by omega
        obtain ⟨hd, ha, hr, hrm, sum, seam⟩ := remoteArithmetic remote
        change 2 ≤ d at hd
        change a < j at ha
        change 1 ≤ r at hr
        change r ≤ m at hrm
        change a + r = j at sum
        change 1 + r < k at seam
        have aPositive : 2 ≤ a := by
          have hcount : 1 ≤ d - 1 := by omega
          have h := Nat.mul_le_mul_right m hcount
          simp only [Nat.one_mul] at h
          change m ≤ a at h
          omega
        have budget : max 2 d = d := max_eq_right hd
        have count : d - 2 + 2 = d := by omega
        have waiting := (waitNative remote (d - 2) 0
          (-(i.val : ZMod (k + 1))) s (by omega)).2
        rw [count] at waiting
        simp only [List.replicate_zero] at waiting
        have root := pulseAfterWait remote i.val s (by omega) hs
        have final := remoteFinal remote i.val (by omega) v
        dsimp only at final
        have finalRun : runBits k finalWord
            (some ⟨v, -(i.val : ZMod (k + 1)) + (a : ℕ), 1⟩) =
          some ⟨v + (if a = i.val then 1 else 0) + (if j = i.val then 1 else 0),
            -(i.val : ZMod (k + 1)) + ((d * m : ℕ) : ZMod (k + 1)),
            if r = m then 1 + r else 0⟩ := by
          simpa only [runBits, finalWord, asWordLiteral, min_eq_left hrm, d, a, r] using final
        have tailSafe : ∀ entry ∈
            ((SelectorTree bottom π πlegal 2 (some v)
              (List.replicate (d - 2) (zeroWord, some v))).archive
              (some ⟨v, -(i.val : ZMod (k + 1)) + (((d - 2) * m : ℕ) : ZMod (k + 1)),
                if d - 2 = 0 then s else 0⟩)).map
                  (fun entry => (entry.1.val, entry.2)), entry.2 ≠ none := by
          have selectedRoot : π (some v) (List.replicate (d - 2) (zeroWord, some v)) =
              .inr pulseWord := by simp [π, show ¬ j ≤ m by omega]
          have expanded : SelectorTree bottom π πlegal 2 (some v)
                (List.replicate (d - 2) (zeroWord, some v)) =
              (match selected : π (some v) (List.replicate (d - 2) (zeroWord, some v)) with
              | .inl label => AcquisitionTree.stop label
              | .inr word => AcquisitionTree.step ⟨word,
                  πlegal (some v) (List.replicate (d - 2) (zeroWord, some v)) word selected⟩
                  (fun reply => SelectorTree bottom π πlegal 1 (some v)
                    (List.replicate (d - 2) (zeroWord, some v) ++ [(word, reply)]))) := rfl
          generalize scalarEq :
            v + (if a - 1 = i.val then 1 else 0) + (if a = i.val then 1 else 0) = value
            at root
          rw [expanded]
          split
          · rename_i label chosen
            cases chosen.symm.trans selectedRoot
          · rename_i word chosen
            have same : word = pulseWord := Sum.inr.inj (chosen.symm.trans selectedRoot)
            subst word
            have tailExpanded (reply : Option (ZMod 2)) :
                SelectorTree bottom π πlegal 1 (some v)
                  (List.replicate (d - 2) (zeroWord, some v) ++ [(pulseWord, reply)]) =
                (match selected : π (some v)
                    (List.replicate (d - 2) (zeroWord, some v) ++ [(pulseWord, reply)]) with
                | .inl label => AcquisitionTree.stop label
                | .inr word => AcquisitionTree.step ⟨word,
                    πlegal (some v)
                      (List.replicate (d - 2) (zeroWord, some v) ++ [(pulseWord, reply)]) word selected⟩
                    (fun reply' => SelectorTree bottom π πlegal 0 (some v)
                      ((List.replicate (d - 2) (zeroWord, some v) ++
                        [(pulseWord, reply)]) ++ [(word, reply')]))) := rfl
            simp only [AcquisitionTree.archive, root, endpointReading, List.map_cons, tailExpanded]
            split
            · simp [AcquisitionTree.archive]
            · rename_i word chosen
              have selected : π (some v)
                  (List.replicate (d - 2) (zeroWord, some v) ++
                    [(pulseWord, some value)]) = .inr word := chosen
              simp only [π, if_neg (by omega : ¬ j ≤ m), List.length_append,
                List.length_replicate, List.length_singleton,
                show ¬ d - 2 + 1 < d - 2 by omega,
                show d - 2 + 1 ≠ d - 2 by omega,
                show d - 2 + 1 = d - 1 by omega, if_pos rfl,
                show ¬ d - 1 < d - 2 by omega,
                show d - 1 ≠ d - 2 by omega,
                List.getLast?_append, List.getLast?_singleton, Option.bind_some] at selected
              have valueSame : value = v := by
                by_cases excluded : i.val = a - 1 ∨ i.val = a
                · have valuePositive : value = v + 1 := by
                    rcases excluded with first | second
                    · simpa [first, show a ≠ a - 1 by omega] using scalarEq.symm
                    · simpa [second, show a - 1 ≠ a by omega] using scalarEq.symm
                  simp [valuePositive] at selected
                · have notFirst : i.val ≠ a - 1 := fun eq => excluded (Or.inl eq)
                  have notSecond : i.val ≠ a := fun eq => excluded (Or.inr eq)
                  simpa only [if_neg (Ne.symm notFirst), if_neg (Ne.symm notSecond),
                    add_zero] using scalarEq.symm
              clear scalarEq
              subst value
              have different : v ≠ v + 1 := by
                intro eq
                have : (0 : ZMod 2) = 1 := (add_left_cancel (show v + 0 = v + 1 by simpa using eq))
                exact zero_ne_one this
              have same : word = finalWord := by
                simpa [different] using selected.symm
              subst word
              simp [SelectorTree, Nat.rec_zero, AcquisitionTree.archive, finalRun, endpointReading]
        intro entry member
        have mapped : (entry.1.val, entry.2) ∈
            ((trees (some v)).archive
              (some ⟨v, -(i.val : ZMod (k + 1)), s⟩)).map
                (fun entry => (entry.1.val, entry.2)) := List.mem_map_of_mem member
        change (entry.1.val, entry.2) ∈
          ((SelectorTree bottom π πlegal (max 2 d) (some v) []).archive
            (some ⟨v, -(i.val : ZMod (k + 1)), s⟩)).map
              (fun entry => (entry.1.val, entry.2)) at mapped
        rw [budget, waiting] at mapped
        rcases List.mem_append.mp mapped with early | late
        · have eq := (List.mem_replicate.mp early).2
          have reply := congrArg Prod.snd eq
          exact reply.symm ▸ Option.some_ne_none v
        · exact tailSafe _ late
    · simpa only [List.nil_append] using linked.2.2.1
    · simpa only [List.nil_append] using linked.2.2.2
  · exact attainingRaw

#print axioms coprime_nonzero_singleton_cost

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.CoprimeSingletonCost
