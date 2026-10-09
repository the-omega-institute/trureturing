/- GID: D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CoprimeSingletonLower
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CoprimeSingletonLower
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Binary initial phase singletons require at least two complete blocks and paid arrival. -/

import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalNarrowCost

set_option autoImplicit false
noncomputable section
universe z

namespace D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.CoprimeSingletonLower

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition
open LiteralModel EndpointCells OriginalNarrowCost
open D5.S0.Automata.TypedPartialDFAOOverBase
open D5.S0.Tower.DBonacciGeneral.UniformBaseGap
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S0.Tower.DBonacci.Names
open scoped BigOperators

set_option maxHeartbeats 1500000 in
/-- A binary singleton target cannot be distinguished before paid arrival.
A correct endpoint tree needs at least two blocks; the marker equations and
absorbing rejection describe the same literal bit transitions. -/
theorem singleton_tree_obstruction {Y : Type z}
    (k m j : ℕ) (hk : 2 ≤ k) (hm : 2 ≤ m) (hshort : m < k)
    (hj : 1 ≤ j) (hjk : j ≤ k)
    (A B : Y) (hAB : A ≠ B) (v : ZMod 2) (localAlphabet : Bool) :
    let marker (phi : ZMod (k + 1)) : ZMod 2 := if phi = 0 then 1 else 0
    (∀ phi, coefficient k phi = marker phi + marker (phi + 1)) ∧
    (∀ (i t : ℕ), i ≤ k → t ≤ k →
      marker (-(i : ZMod (k + 1)) + (t : ℕ)) = if t = i then 1 else 0) ∧
    (∀ bits : List Bool, runWord (bitUpdate k) bits none = none) ∧
    (∀ (n : ℕ) (tree : AcquisitionTree k m localAlphabet Y n),
      (∀ i s : ℕ, i ≤ k → s < k →
        tree.result (some ⟨v, -(i : ZMod (k + 1)), s⟩) =
          if i = j then B else A) →
      max 2 (j ⌈/⌉ m) ≤ n) := by
  classical
  dsimp only
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
  have absorbed (bits : List Bool) : runWord (bitUpdate k) bits none = none := by
    induction bits with
    | nil => rfl
    | cons bit bits ih => simpa only [runWord, bitUpdate] using ih
  have indexedMarker (i t : ℕ) (hi : i ≤ k) (ht : t ≤ k) :
      marker (-(i : ZMod (k + 1)) + (t : ℕ)) = if t = i then 1 else 0 := by
    have eq : -(i : ZMod (k + 1)) + (t : ℕ) = 0 ↔ t = i := by
      rw [neg_add_eq_zero, ZMod.natCast_eq_natCast_iff']
      rw [Nat.mod_eq_of_lt (by omega : t < k + 1), Nat.mod_eq_of_lt (by omega : i < k + 1)]
      exact eq_comm
    simp only [marker, eq]
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
  have quietZero (t : ℕ) (lo : 1 ≤ t) (hi : t + 1 ≤ k) :
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
                  quietZero t lo (by omega), add_zero, phase, List.length_cons,
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
            cases next reply <;> rfl
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
            · simp [quietZero t.val (by omega) (by omega)]
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
  refine ⟨edge, indexedMarker, absorbed, ?_⟩
  intro n tree correct
  exact max_le (twoLower n tree correct) (arrivalLower n tree correct)

#print axioms singleton_tree_obstruction

end D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.CoprimeSingletonLower
