/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CoprimeSingletonCost
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CoprimeSingletonCost
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Coprime nonzero initial phase singletons have exact safe complete-block cost. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.CoprimeSingletonLower

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
  obtain ⟨edge, indexedMarker, absorbed, treeLower⟩ :=
    CoprimeSingletonLower.singleton_tree_obstruction k m j hk hm hshort
      hj hjk A B hAB v localAlphabet
  change ∀ (i t : ℕ), i ≤ k → t ≤ k →
    marker (-(i : ZMod (k + 1)) + (t : ℕ)) = if t = i then 1 else 0 at indexedMarker
  have appendRun (left right : List Bool) (q : Option (LiveRecord k)) :
      runWord (bitUpdate k) (left ++ right) q =
        runWord (bitUpdate k) right (runWord (bitUpdate k) left q) := by
    induction left generalizing q with
    | nil => rfl
    | cons bit left ih => simpa only [List.cons_append, runWord] using ih (bitUpdate k bit q)
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
  have treeStep {Y' : Type z} {k' m' : ℕ} {alphabet : Bool}
      (fallback : Y') (selector : NarrowWindowCost.Selector m' Y')
      (legal : ∀ initial archive word, selector initial archive = .inr word →
        alphabet = true → DBonacciAdmissible k' m' word)
      (n : ℕ) initial archive word (selected : selector initial archive = .inr word) :
      SelectorTree fallback selector legal (n + 1) initial archive =
        AcquisitionTree.step ⟨word, legal initial archive word selected⟩
          (fun reply => SelectorTree fallback selector legal n initial
            (archive ++ [(word, reply)])) := by
    simp only [SelectorTree, Nat.rec_add_one]
    split
    · rename_i label chosen
      cases chosen.symm.trans selected
    · rename_i word' chosen
      have same : word' = word := Sum.inr.inj (chosen.symm.trans selected)
      subst word'
      rfl
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
            rw [treeStep fallback π legal d y₀ archive B eq]
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
                    have length := nextProof.2.1
                    dsimp only [SelectorTree] at length ⊢
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

  have scanner_value_joint :
      ∀ (w : List Bool) (n : ℕ) (a : ZMod 2) (s : Fin k),
        runWord (bitUpdate k) w (some ⟨a,(n : ZMod (k+1)),s.val⟩) =
          ((D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.scanner k (by omega)).evalFrom s w).map
            (fun tail => ⟨a+D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.value k n w,((n+w.length : ℕ) : ZMod (k+1)),tail.val⟩) := by
    intro w
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
            · simp only [runWord,bitUpdate,if_true,safe,if_false,dite_false,absorbed,
                PartialDFA.evalFrom,runTransition,D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.scanner,dif_neg safe,Option.map_none]

  have record_run (w : List Bool) :
      OriginalRecord k (by omega) w = runWord (bitUpdate k) w (some ⟨0, 0, 0⟩) := by
    have h := scanner_value_joint w 0 0 ⟨0, by omega⟩
    simpa only [OriginalRecord, PartialDFA.eval, NarrowWindowCost.scanner, Nat.cast_zero,
      Nat.zero_add, zero_add] using h.symm
  have record_append (w b : List Bool) :
      OriginalRecord k (by omega) (w ++ b) =
        runWord (bitUpdate k) b (OriginalRecord k (by omega) w) := by
    rw [record_run, appendRun, record_run]
  have output_record : ∀ (k : ℕ) (hk : 0<k) (w : List Bool),
      D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.output k hk w = endpointReading (OriginalRecord k hk w) := by
    intro k hk w
    unfold D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.output OriginalRecord
    cases (D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.scanner k hk).eval w <;> rfl

  have execute_same : ∀ {Y : Type z} (m : ℕ)
      (π : D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.Selector m Y) (d : ℕ) (w : List Bool) (y₀ : Option (ZMod 2)) (archive : D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.Archive m),
      D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.execute k (by omega) π d w y₀ archive =
        NativeExecute π d (OriginalRecord k (by omega) w) y₀ archive := by
    intro Y m π d
    induction d with
    | zero => intros; rfl
    | succ d ih =>
        intro w y₀ archive
        cases selected : π y₀ archive with
        | inl label => simp only [D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.execute,NativeExecute,selected]
        | inr B =>
            simp only [D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.NarrowWindowCost.execute,NativeExecute,selected]
            rw [ih,output_record,record_append]
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
  have twoSafe (q : Option (LiveRecord k)) initial archive word
      (selected : π initial archive = .inr word)
      (firstSafe : endpointReading (runBits k word q) ≠ none)
      (secondSafe : ∀ nextWord,
        π initial (archive ++ [(word, endpointReading (runBits k word q))]) = .inr nextWord →
        endpointReading (runBits k nextWord (runBits k word q)) ≠ none) :
      ∀ entry ∈ (SelectorTree bottom π πlegal 2 initial archive).archive q,
        entry.2 ≠ none := by
    have expanded := treeStep bottom π πlegal 1 initial archive word selected
    change SelectorTree bottom π πlegal 2 initial archive = _ at expanded
    rw [expanded]
    simp only [AcquisitionTree.archive]
    intro entry member
    rcases List.mem_cons.mp member with same | later
    · subst entry
      exact firstSafe
    · have expandedOne (archive' : NarrowWindowCost.Archive m) :
          SelectorTree bottom π πlegal 1 initial archive' =
            (match selected : π initial archive' with
            | .inl label => AcquisitionTree.stop label
            | .inr nextWord => AcquisitionTree.step
                ⟨nextWord, πlegal initial archive' nextWord selected⟩
                (fun reply => SelectorTree bottom π πlegal 0 initial
                  (archive' ++ [(nextWord, reply)]))) := rfl
      rw [expandedOne] at later
      split at later
      · simpa only [AcquisitionTree.archive, List.not_mem_nil] using later
      · rename_i nextWord chosen
        simp only [AcquisitionTree.archive, SelectorTree, Nat.rec_zero, List.mem_cons,
          List.not_mem_nil, or_false] at later
        subst entry
        exact secondSafe nextWord chosen
  have belowNative (below : j < m) (i s : ℕ) (hi : i ≤ k) (hs : s < k) :
      NativeExecute π 2 (some ⟨v, -(i : ZMod (k + 1)), s⟩) (some v) [] =
        some (if i = j then B else A, if i = j ∨ i = m then 2 else 1) ∧
      (∀ entry ∈ (SelectorTree bottom π πlegal 2 (some v) []).archive
        (some ⟨v, -(i : ZMod (k + 1)), s⟩), entry.2 ≠ none) := by
    constructor
    ·
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
    · have root := rootBelow i s hi hs below
      have second := repair i (m - j) hi (by omega)
      apply twoSafe _ (some v) [] belowWord
      · simp [π, below, below.le]
      · simp only [runBits, belowWord, asWordLiteral, min_eq_left below.le, root, endpointReading]
        exact Option.some_ne_none _
      · intro word selected
        have selected' := selected
        simp only [List.nil_append, π, if_pos below.le] at selected'
        split at selected'
        · have same : word = repairWord := Sum.inr.inj selected'.symm
          subst word
          simp only [runBits, belowWord, repairWord, asWordLiteral, min_eq_left below.le, root,
            second, endpointReading]
          exact Option.some_ne_none _
        · cases selected'

  have atNative (atIndex : j = m) (i s : ℕ) (hi : i ≤ k) (hs : s < k) :
      NativeExecute π 2 (some ⟨v, -(i : ZMod (k + 1)), s⟩) (some v) [] =
        some (if i = j then B else A, if i = m - 1 ∨ i = m then 2 else 1) ∧
      (∀ entry ∈ (SelectorTree bottom π πlegal 2 (some v) []).archive
        (some ⟨v, -(i : ZMod (k + 1)), s⟩), entry.2 ≠ none) := by
    constructor
    ·
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
    · have root := rootAt i s hi hs
      have second := repair i (1) hi (by omega)
      apply twoSafe _ (some v) [] pulseWord
      · simp [π, atIndex]
      · simp only [runBits, pulseWord, asWordLiteral, root, endpointReading]
        exact Option.some_ne_none _
      · intro word selected
        have selected' := selected
        simp only [List.nil_append, π, atIndex, le_refl, ↓reduceIte] at selected'
        split at selected'
        · have same : word = repairWord := Sum.inr.inj selected'.symm
          subst word
          simp only [runBits, pulseWord, repairWord, asWordLiteral, root,
            second, endpointReading]
          exact Option.some_ne_none _
        · cases selected'

  have actualSource (i s : ℕ) (hi : i ≤ k) (hs : s < k) :
      ∃ w : List Bool, m ∣ w.length ∧
        OriginalRecord k (by omega) w = some ⟨v, -(i : ZMod (k + 1)), s⟩ ∧
        NarrowWindowCost.output k (by omega) w = some v ∧ k + 1 ∣ w.length + i := by
    obtain ⟨N, word, width, admissible, realized, rest⟩ :=
      joint_history_realization k m hk (by omega) v (-(i : ZMod (k + 1))) s hs
        (by rw [hg]; exact one_dvd _)
    let w := List.ofFn word
    have record : OriginalRecord k (by omega) w = some ⟨v, -(i : ZMod (k + 1)), s⟩ := by
      rw [record_run]
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
    rw [execute_same m σ n, record] at success
    exact (selectorTreeSuccess k m localAlphabet bottom σ legal n
      (some ⟨v, -(i : ZMod (k + 1)), s⟩) (some v) [] _ c success).1

  have lowerAll (n : ℕ)
      (feasible : NarrowWindowCost.Feasible k m (by omega) localAlphabet
        (fun i => if i.val = j then B else A) bottom v n) : max 2 (j ⌈/⌉ m) ≤ n := by
    obtain ⟨tree, correct⟩ := feasibleTree n feasible
    exact treeLower n tree correct

  have waitNative (remote : m < j) :
      ∀ n t (phi : ZMod (k + 1)) s, t + n = d - 2 →
        NativeExecute π (n + 2) (some ⟨v, phi, s⟩) (some v)
            (List.replicate t (zeroWord, some v)) =
          (NativeExecute π 2
            (some ⟨v, phi + ((n * m : ℕ) : ZMod (k + 1)), if n = 0 then s else 0⟩)
            (some v) (List.replicate (d - 2) (zeroWord, some v))).map
              (fun result => (result.1, result.2 + n)) ∧
        ((∀ entry ∈ (SelectorTree bottom π πlegal (n + 2) (some v)
          (List.replicate t (zeroWord, some v))).archive (some ⟨v, phi, s⟩),
            entry.2 ≠ none) ↔
          ∀ entry ∈ (SelectorTree bottom π πlegal 2 (some v)
            (List.replicate (d - 2) (zeroWord, some v))).archive
            (some ⟨v, phi + ((n * m : ℕ) : ZMod (k + 1)), if n = 0 then s else 0⟩),
              entry.2 ≠ none) := by
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
        · rw [show n + 1 + 2 = (n + 2) + 1 by omega,
            treeStep bottom π πlegal (n + 2) (some v)
              (List.replicate t (zeroWord, some v)) zeroWord selected]
          simp only [AcquisitionTree.archive, runZero, endpointReading, nextArchive,
            List.forall_mem_cons, Option.some_ne_none, true_and]
          rw [(ih (t + 1) (phi + (m : ℕ)) 0 (by omega)).2]
          simp only [phase, ite_self, if_neg (by omega : n + 1 ≠ 0)]
          simp

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
        some (if i = j then B else A, if i = a - 1 ∨ i = a then 1 else 2) ∧
      (∀ entry ∈ (SelectorTree bottom π πlegal 2 (some v)
        (List.replicate (d - 2) (zeroWord, some v))).archive
        (some ⟨v, -(i : ZMod (k + 1)) + (((d - 2) * m : ℕ) : ZMod (k + 1)),
          if d - 2 = 0 then s else 0⟩), entry.2 ≠ none) := by
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
    constructor
    ·
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
    · apply twoSafe _ (some v) (List.replicate (d - 2) (zeroWord, some v)) pulseWord selectedRoot
      · rw [root]
        exact Option.some_ne_none _
      · intro word selected
        rw [root]
        simp only [π, if_neg (by omega : ¬ j ≤ m), List.length_append,
          List.length_replicate, List.length_singleton, penultimate,
          if_neg notWaiting, if_neg notLast', if_pos rfl,
          List.getLast?_append, List.getLast?_singleton, Option.or_some,
          Option.bind_some, ↓reduceIte] at selected
        have same : word = finalWord := by
          split_ifs at selected <;> simp_all only [Sum.inl_ne_inr, Sum.inr.injEq]
        subst word
        have final := remoteFinal remote i hi
          (v + (if a - 1 = i then 1 else 0) + (if a = i then 1 else 0))
        simp only [runBits, finalWord, asWordLiteral, min_eq_left hrm]
        rw [final]
        exact Option.some_ne_none _

  have nativeCorrect (i s : ℕ) (hi : i ≤ k) (hs : s < k) :
      ∃ c ≤ max 2 d, NativeExecute π (max 2 d)
        (some ⟨v, -(i : ZMod (k + 1)), s⟩) (some v) [] =
          some (if i = j then B else A, c) ∧
        (∀ entry ∈ (trees (some v)).archive
          (some ⟨v, -(i : ZMod (k + 1)), s⟩), entry.2 ≠ none) := by
    change ∃ c ≤ max 2 d, NativeExecute π (max 2 d)
      (some ⟨v, -(i : ZMod (k + 1)), s⟩) (some v) [] =
        some (if i = j then B else A, c) ∧
      ∀ entry ∈ (SelectorTree bottom π πlegal (max 2 d) (some v) []).archive
        (some ⟨v, -(i : ZMod (k + 1)), s⟩), entry.2 ≠ none
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
      have waiting := waitNative remote (d - 2) 0 (-(i : ZMod (k + 1))) s (by omega)
      have ending := remoteTwo remote i s hi hs
      rw [ending.1] at waiting
      simp only [List.replicate_zero, Option.map_some] at waiting
      have count : d - 2 + 2 = d := by omega
      rw [count] at waiting
      rw [budget]
      refine ⟨(if i = a - 1 ∨ i = a then 1 else 2) + (d - 2), ?_, waiting.1, ?_⟩
      · split_ifs <;> omega
      · exact waiting.2.mpr ending.2

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
      (some ⟨v, -(i.val : ZMod (k + 1)), s⟩) (some v) [] _ c native.1
    refine ⟨c, bounded, ?_, ?_, ?_⟩
    · rw [execute_same m, record]
      exact native.1
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
      (some ⟨v, -(i.val : ZMod (k + 1)), s⟩) (some v) [] _ c native.1
    refine ⟨linked.1, ?_, ?_, ?_, ?_⟩
    · exact linked.2.1.trans_le bounded
    · exact native.2
    · simpa only [List.nil_append] using linked.2.2.1
    · simpa only [List.nil_append] using linked.2.2.2
  · exact attainingRaw

#print axioms coprime_nonzero_singleton_cost

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.CoprimeSingletonCost
