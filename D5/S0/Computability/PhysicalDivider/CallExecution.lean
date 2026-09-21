/- GID: D5/S0/Computability/PhysicalDivider/CallExecution
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete physical positive calls with exact outputs and every-prefix coordinate bounds. -/

/- Arithmetic source: szymtor/RAM-TM, commit
6fe5a3d94f6c2da46cc2c5ab98cd36997b130737, Apache-2.0.
Authors: Szymon Toruńczyk and Codex 5.6. The padding proof uses the original
WordOperations.lean:37-41 argument inline and the retained fixed-word inverse.
Full license and source mapping: Library/Computability/ramtm2026divider.md. -/

import D5.S0.Computability.PhysicalDivider.ArithmeticExecution
import D5.S0.Computability.PhysicalDivider.Return
import Mathlib.Data.Nat.Size
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S0.Computability.PhysicalDivider
open Turing Lax51Proofs.RamToTM

/-- A common spatial interval for preparation, arithmetic and return. -/
def callRadius (w : ℕ) : ℕ :=
  2 * arithmeticStackBound w + sourceStepBudget + 400 * (w + 1) + 3

/-- The initial charged interval and every visited position remain charged.
This observer is external to the physical machine and never supplies an instruction. -/
def prefixCharge (initial : LocatedCfg) (charged : ActiveTape → Extent) :
    ℕ → ActiveTape → Extent
  | 0 => charged
  | i + 1 =>
    let c := (((fun o : Option LocatedCfg => o.bind locatedStep)^[i + 1])
      (some initial)).getD initial
    fun k => ⟨c.2 k, min (prefixCharge initial charged i k).low (c.2 k),
      max (prefixCharge initial charged i k).high (c.2 k)⟩

set_option maxHeartbeats 2400000 in
/-- A complete call reaches the actual reusable return state. Every bit-action
prefix has bounded support and absolute head positions, including erased regions
through the union of these prefixes. -/
theorem positive_call_execution (w a d : ℕ) (hw : 1 ≤ w)
    (ha : a < 2 ^ w) (hd0 : 0 < d) (hd : d < 2 ^ w)
    (capacity oldQ oldR : List Bool) (hcap : capacity.length = w)
    (hq : oldQ.length ≤ w) (hr : oldR.length ≤ w + 1) :
    ∃ n ≤ sourceStepBudget * (divPositiveRunTime w + 2) + 300 * (w + 1),
      ((fun o : Option LocatedCfg => o.bind locatedStep)^[n])
        (some (callEntry (fixedBits w a) (fixedBits w d) capacity oldQ oldR, fun _ => 0)) =
        some (callReturned (fixedBits w a) (fixedBits w d) capacity
          (fixedBits w (a / d)) (fixedBits (w + 1) (a % d)), fun _ => 0) ∧
      (∀ i ≤ n, ∃ c,
        ((fun o : Option LocatedCfg => o.bind locatedStep)^[i])
          (some (callEntry (fixedBits w a) (fixedBits w d) capacity oldQ oldR, fun _ => 0)) = some c ∧
        ((fun o : Option PhysicalCfg => o.bind physicalStep)^[i])
          (some (callEntry (fixedBits w a) (fixedBits w d) capacity oldQ oldR)) = some c.1 ∧
        LocatedWithin c (fun _ => -(callRadius w : ℤ)) (fun _ => callRadius w)) ∧
      callAgain (callReturned (fixedBits w a) (fixedBits w d) capacity
        (fixedBits w (a / d)) (fixedBits (w + 1) (a % d))) =
        some (callEntry (fixedBits w a) (fixedBits w d) capacity
          (fixedBits w (a / d)) (fixedBits (w + 1) (a % d))) ∧
      (∀ charged : ActiveTape → Extent,
        (∀ k, -(callRadius w : ℤ) ≤ (charged k).low ∧
          (charged k).low ≤ 0 ∧ (charged k).head = 0 ∧
          2 * (w + 1 : ℤ) + 1 ≤ (charged k).high ∧
          (charged k).high ≤ callRadius w) →
        ∀ (F C i : ℕ), i ≤ n →
          F + C + ∑ k, extentCost (prefixCharge
            (callEntry (fixedBits w a) (fixedBits w d) capacity oldQ oldR, fun _ => 0)
            charged i k) ≤ F + C + Fintype.card ActiveTape * (3 * callRadius w + 3)) := by
  let run := fun o : Option LocatedCfg => o.bind locatedStep
  let W := w + 1
  let radius := callRadius w
  let entry : LocatedCfg :=
    (callEntry (fixedBits w a) (fixedBits w d) capacity oldQ oldR, fun _ => 0)
  let prepared := locatedSourceCfg
    (divInitialCfg (fixedBits w a).reverse (fixedBits W d) (fixedBits W 0))
    (preparedFrame (fixedBits w a) (fixedBits w d) capacity)
    (preparedHeads (fixedBits w a) (fixedBits w d) capacity)
  let done := locatedSourceCfg
    (divDoneCfg true (fixedBits W d) (fixedBits W (a % d)) (fixedBits w (a / d)))
    (preparedFrame (fixedBits w a) (fixedBits w d) capacity)
    (preparedHeads (fixedBits w a) (fixedBits w d) capacity)
  let returned : LocatedCfg :=
    (callReturned (fixedBits w a) (fixedBits w d) capacity
      (fixedBits w (a / d)) (fixedBits W (a % d)), fun _ => 0)
  have hL : W ≤ arithmeticStackBound w := by dsimp [W, arithmeticStackBound]; omega
  have hC : 1 ≤ sourceStepBudget := by dsimp [sourceStepBudget]; omega
  have hrad : 2 * arithmeticStackBound w + sourceStepBudget + 400 * W + 3 = radius := rfl
  have enlarge (c : LocatedCfg) (low high : ActiveTape → ℤ)
      (hwithin : LocatedWithin c low high)
      (hl : ∀ k, -(radius : ℤ) ≤ low k) (hh : ∀ k, high k ≤ radius) :
      LocatedWithin c (fun _ => -(radius : ℤ)) (fun _ => radius) := by
    intro k
    rcases hwithin k with ⟨hlo, hhi, hs⟩
    have hlow := hl k
    have hhigh := hh k
    dsimp only [Within] at hlo hhi hs ⊢
    refine ⟨by omega, by omega, ?_⟩
    intro i hi
    have := hs i hi
    constructor <;> omega
  have topWithin (bs : List Bool) : Within (stackAtTop bs) (topExtent bs) := by
    have lengthBelow (bs : List Bool) : (cellsBelow bs).length = 2 * bs.length + 2 := by
      induction bs with
      | nil => rfl
      | cons b bs ih => simp [cellsBelow, ih]; omega
    have getBound (bs : List Bool) (i : ℕ) (h : bs.getI i = true) : i < bs.length := by
      by_contra hn
      rw [List.getI_eq_default _ (by omega)] at h
      cases h
    cases bs with
    | nil =>
      refine ⟨by simp [topExtent], by simp [topExtent], ?_⟩
      intro i hi
      cases i with
      | ofNat n =>
        change (Tape.mk₂ [] [false, true]).nth (n : ℤ) = true at hi
        rw [Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk] at hi
        have hn := getBound [false, true] n hi
        simp only [List.length_cons, List.length_nil] at hn
        dsimp [topExtent]; constructor <;> omega
      | negSucc n =>
        change ([] : List Bool).getI n = true at hi
        have hn := getBound [] n hi
        simp at hn
    | cons b bs =>
      refine ⟨by simp [topExtent]; omega, by simp [topExtent], ?_⟩
      intro i hi
      cases i with
      | ofNat n =>
        change (Tape.mk₂ (cellsBelow bs) [true, b]).nth (n : ℤ) = true at hi
        rw [Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk] at hi
        have hn := getBound [true, b] n hi
        simp only [List.length_cons, List.length_nil] at hn
        dsimp [topExtent]; try simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        constructor <;> omega
      | negSucc n =>
        change (cellsBelow bs).getI n = true at hi
        have hn := getBound (cellsBelow bs) n hi
        rw [lengthBelow] at hn
        dsimp [topExtent]; try simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        constructor <;> omega
  have originWithin (bs : List Bool) :
      Within (stackAtOrigin bs) ⟨0, 0, 2 * bs.length + 1⟩ := by
    dsimp only [Within]
    refine ⟨by omega, by omega, ?_⟩
    intro i hi
    cases i with
    | ofNat n =>
      change (stackAtOrigin bs).nth (n : ℤ) = true at hi
      rw [stackAtOrigin, Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk] at hi
      have hlen : ([false, true] ++ bs.reverse.flatMap (fun b => [true, b])).length =
          2 * bs.length + 2 := by simp [List.length_flatMap]; omega
      have hn : n < ([false, true] ++ bs.reverse.flatMap (fun b => [true, b])).length := by
        by_contra hn
        rw [List.getI_eq_default _ (by omega)] at hi
        cases hi
      rw [hlen] at hn
      simp only [Int.zero_add, Int.ofNat_eq_natCast]
      constructor <;> omega
    | negSucc n =>
      change ([] : List Bool).getI n = true at hi
      simp at hi
  have padded : fixedBits w d ++ [false] = fixedBits W d := by
    -- Original argument: WordOperations.lean:37-41, retained inline.
    have appendFalse (bits : List Bool) : bitsValue (bits ++ [false]) = bitsValue bits := by
      induction bits with
      | nil => rfl
      | cons b bits ih => simp [bitsValue, ih]
    have hv := fixedBits_bitsValue (fixedBits w d ++ [false])
    simpa [W, appendFalse, bitsValue_fixedBits, Nat.mod_eq_of_lt hd] using hv.symm
  let preTime := 132 * w + 13 * (oldQ.length + oldR.length) + 69
  have hp : (run^[preTime]) (some entry) = some prepared := by
    have h := preparation_execution (fixedBits w a) (fixedBits w d) capacity oldQ oldR
    simp only [fixedBits_length, hcap] at h
    have ht : 44 * (w + w + w) + 13 * (oldQ.length + oldR.length) + 69 = preTime := by
      dsimp [preTime]; ring
    rw [ht] at h
    simpa only [run, entry, prepared, padded, hcap, W, fixedBits_zero] using h
  have hpreTime : preTime ≤ 200 * W := by dsimp [preTime, W]; omega
  have hiw : LocatedWithin entry (fun _ => 0) (fun _ => 2 * W + 1) := by
    intro k
    have hm : (boundaryWords (fixedBits w a) (fixedBits w d) capacity oldQ oldR k).length ≤ W := by
      cases k <;> rename_i k <;> cases k <;>
        simp [boundaryWords, W] <;> omega
    have h := originWithin (boundaryWords (fixedBits w a) (fixedBits w d) capacity oldQ oldR k)
    have ht : entry.1.tapes k =
        stackAtOrigin (boundaryWords (fixedBits w a) (fixedBits w d) capacity oldQ oldR k) := by
      cases k <;> rename_i k <;> cases k <;> rfl
    change Within (entry.1.tapes k) ⟨0, 0, 2 * W + 1⟩
    rw [ht]
    rcases h with ⟨hl, hh, hs⟩
    dsimp only [Within] at hl hh hs ⊢
    refine ⟨by omega, by omega, ?_⟩
    intro i hi
    have := hs i hi
    constructor <;> omega
  have preBounds : ∀ i ≤ preTime, ∃ c, (run^[i]) (some entry) = some c ∧
      LocatedWithin c (fun _ => -(radius : ℤ)) (fun _ => radius) := by
    intro i hi
    obtain ⟨c, hc, _, hb, he⟩ := located_run_bounds entry prepared preTime hp _ _ hiw i hi
    refine ⟨c, hc, enlarge c _ _ he ?_ ?_⟩ <;> intro k <;>
      have hzero : entry.2 k = 0 := rfl
    · rw [hzero]; omega
    · rw [hzero]; omega
  have layout (c : divMachine.Cfg) (hlen : ∀ k, (c.stk k).length ≤ W) :
      LocatedWithin (locatedSourceCfg c
        (preparedFrame (fixedBits w a) (fixedBits w d) capacity)
        (preparedHeads (fixedBits w a) (fixedBits w d) capacity))
        (fun _ => 0) (fun _ => 2 * W + 1) ∧
      (∀ k, 0 ≤ (locatedSourceCfg c
        (preparedFrame (fixedBits w a) (fixedBits w d) capacity)
        (preparedHeads (fixedBits w a) (fixedBits w d) capacity)).2 k ∧
        (locatedSourceCfg c
        (preparedFrame (fixedBits w a) (fixedBits w d) capacity)
        (preparedHeads (fixedBits w a) (fixedBits w d) capacity)).2 k ≤ 2 * W) := by
    have frameLen : ∀ k, (boundaryWords (fixedBits w a) (fixedBits w d) capacity [] [] (.inr k)).length ≤ W := by
      intro k; cases k <;> simp [boundaryWords, W, hcap]
    constructor
    · intro k
      have support (bs : List Bool) (hlen : bs.length ≤ W) :
          Within (stackAtTop bs) ⟨2 * bs.length, 0, 2 * W + 1⟩ := by
        rcases topWithin bs with ⟨hl, hh, hs⟩
        dsimp [topExtent] at hl hh hs
        dsimp only [Within]
        refine ⟨by omega, by omega, ?_⟩
        intro i hi
        have := hs i hi
        constructor <;> omega
      cases k with
      | inl k => exact support (c.stk k) (hlen k)
      | inr k => exact support _ (frameLen k)
    · intro k
      cases k with
      | inl k =>
        have h := hlen k
        dsimp [locatedSourceCfg, logicalHeads]
        constructor <;> omega
      | inr k =>
        have h := frameLen k
        dsimp [locatedSourceCfg, logicalHeads, preparedHeads]
        constructor <;> omega
  have preparedLen : ∀ k,
      ((divInitialCfg (fixedBits w a).reverse (fixedBits W d) (fixedBits W 0)).stk k).length ≤ W := by
    intro k
    cases k <;> simp [divMachine, divInitialCfg, divCfg, divStacks, W]
  have prepLayout := layout _ preparedLen
  have harithWithin : LocatedWithin prepared (fun _ => -(sourceStepBudget : ℤ))
      (fun _ => 2 * arithmeticStackBound w + sourceStepBudget) := by
    intro k
    have hhprep : LocatedWithin prepared (fun _ => 0) (fun _ => 2 * W + 1) := prepLayout.1
    rcases hhprep k with ⟨hl, hh, hs⟩
    dsimp only [Within] at hl hh hs ⊢
    change - (sourceStepBudget : ℤ) ≤ prepared.2 k ∧
      prepared.2 k ≤ 2 * arithmeticStackBound w + sourceStepBudget ∧ _
    refine ⟨by omega, by omega, ?_⟩
    intro i hi
    have := hs i hi
    constructor <;> omega
  have hframe : ∀ k, 0 ≤ preparedHeads (fixedBits w a) (fixedBits w d) capacity k ∧
      preparedHeads (fixedBits w a) (fixedBits w d) capacity k ≤ 2 * arithmeticStackBound w := by
    intro k
    have h := prepLayout.2 (.inr k)
    change 0 ≤ preparedHeads _ _ _ k ∧ preparedHeads _ _ _ k ≤ 2 * W at h
    constructor <;> omega
  obtain ⟨m, hm, harith, arithBounds⟩ := positive_physical_arithmetic w a d ha hd0 hd
    (preparedFrame (fixedBits w a) (fixedBits w d) capacity)
    (preparedHeads (fixedBits w a) (fixedBits w d) capacity) hframe harithWithin
  let retTime := 93 * w + 92
  have hret : (run^[retTime]) (some done) = some returned := by
    have h := (return_execution (fixedBits w a) (fixedBits w d) capacity
      (fixedBits W d) (fixedBits w (a / d)) (fixedBits W (a % d))).1
    simp only [fixedBits_length, hcap] at h
    have ht : 37 * (w + W) + 10 * W + 3 * (w + w + w) + 45 = retTime := by
      dsimp [retTime, W]; ring
    rw [ht] at h
    exact h
  have hretTime : retTime ≤ 100 * W := by dsimp [retTime, W]; omega
  have doneLen : ∀ k,
      ((divDoneCfg true (fixedBits W d) (fixedBits W (a % d)) (fixedBits w (a / d))).stk k).length ≤ W := by
    intro k
    cases k <;> simp [divMachine, divDoneCfg, divCfg, divStacks, W]
  have doneLayout := layout _ doneLen
  have retBounds : ∀ i ≤ retTime, ∃ c, (run^[i]) (some done) = some c ∧
      LocatedWithin c (fun _ => -(radius : ℤ)) (fun _ => radius) := by
    intro i hi
    obtain ⟨c, hc, _, hb, he⟩ := located_run_bounds done returned retTime hret _ _ doneLayout.1 i hi
    refine ⟨c, hc, enlarge c _ _ he ?_ ?_⟩ <;> intro k <;>
      have hk := doneLayout.2 k
    · change 0 ≤ done.2 k ∧ done.2 k ≤ 2 * W at hk
      omega
    · change 0 ≤ done.2 k ∧ done.2 k ≤ 2 * W at hk
      omega
  have project : Function.Semiconj (Option.map Prod.fst)
      (fun o : Option LocatedCfg => o.bind locatedStep)
      (fun o : Option PhysicalCfg => o.bind physicalStep) := by
    intro o
    cases o with
    | none => rfl
    | some c => simp [locatedStep, physicalStep, Option.map_map, Function.comp_def]
  have allBounds : ∀ i ≤ retTime + (m + preTime), ∃ c, (run^[i]) (some entry) = some c ∧
      LocatedWithin c (fun _ => -(radius : ℤ)) (fun _ => radius) := by
    intro i hi
    by_cases hip : i ≤ preTime
    · exact preBounds i hip
    · by_cases hia : i ≤ m + preTime
      · obtain ⟨c, hc, he⟩ := arithBounds (i - preTime) (by omega)
        refine ⟨c, ?_, enlarge c _ _ he (by intro k; omega) (by intro k; omega)⟩
        rw [show i = (i-preTime) + preTime by omega, Function.iterate_add_apply]
        change (run^[i-preTime]) ((run^[preTime]) (some entry)) = _
        rw [hp]
        exact hc
      · obtain ⟨c, hc, he⟩ := retBounds (i - (m + preTime)) (by omega)
        refine ⟨c, ?_, he⟩
        rw [show i = (i-(m+preTime)) + (m+preTime) by omega,
          Function.iterate_add_apply run (i-(m+preTime)) (m+preTime),
          Function.iterate_add_apply run m preTime]
        rw [hp, harith]
        exact hc
  refine ⟨retTime + (m + preTime), ?_, ?_, ?_, ?_, ?_⟩
  · have hmul := Nat.mul_le_mul_left sourceStepBudget
      (show divPositiveRunTime w ≤ divPositiveRunTime w + 2 by omega)
    change retTime + (m + preTime) ≤ _
    omega
  · change (run^[retTime + (m + preTime)]) (some entry) = some returned
    rw [Function.iterate_add_apply run retTime (m + preTime),
      Function.iterate_add_apply run m preTime, hp, harith, hret]
  · intro i hi
    obtain ⟨c, hc, he⟩ := allBounds i hi
    refine ⟨c, hc, ?_, he⟩
    have h := (project.iterate_right i) (some entry)
    rw [hc] at h
    exact h.symm
  · exact (return_execution (fixedBits w a) (fixedBits w d) capacity
      (fixedBits W d) (fixedBits w (a / d)) (fixedBits W (a % d))).2
  · intro charged hcharged F C i hi
    have chargeBounds : ∀ j ≤ retTime + (m + preTime), ∀ k,
        -(radius : ℤ) ≤ (prefixCharge entry charged j k).low ∧
        (prefixCharge entry charged j k).high ≤ radius ∧
        -(radius : ℤ) ≤ (prefixCharge entry charged j k).head ∧
        (prefixCharge entry charged j k).head ≤ radius := by
      intro j hj
      induction j with
      | zero =>
        intro k
        have h := hcharged k
        simp only [prefixCharge]
        exact ⟨h.1, h.2.2.2.2, by rw [h.2.2.1]; omega, by rw [h.2.2.1]; omega⟩
      | succ j ih =>
        obtain ⟨c, hc, he⟩ := allBounds (j+1) hj
        intro k
        have hprev := ih (by omega) k
        have hk := he k
        dsimp only [Within] at hk
        change (run^[j+1]) (some entry) = some c at hc
        simp only [prefixCharge, show
          ((fun o : Option LocatedCfg => o.bind locatedStep)^[j+1]) (some entry) = some c from hc,
          Option.getD_some]
        exact ⟨by omega, by omega, hk.1, hk.2.1⟩
    have costBound : ∀ k, extentCost (prefixCharge entry charged i k) ≤ 3 * radius + 3 := by
      intro k
      let e := prefixCharge entry charged i k
      obtain ⟨hl, hh, hp, hq⟩ := chargeBounds i hi k
      change -(radius : ℤ) ≤ e.low at hl
      change e.high ≤ radius at hh
      change -(radius : ℤ) ≤ e.head at hp
      change e.head ≤ radius at hq
      have habs : e.head.natAbs ≤ radius := by
        by_cases hn : 0 ≤ e.head
        · have he := Int.natAbs_of_nonneg hn
          omega
        · have he := Int.ofNat_natAbs_of_nonpos (show e.head ≤ 0 by omega)
          omega
      have hsize : (e.head.natAbs + 1).size ≤ e.head.natAbs + 1 :=
        Nat.size_le.mpr Nat.lt_two_pow_self
      have hspan : (e.high - e.low + 1).toNat ≤ 2 * radius + 1 := by omega
      change extentCost e ≤ _
      dsimp only [extentCost]
      omega
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (f := fun k => extentCost (prefixCharge entry charged i k))
      (g := fun _ : ActiveTape => 3 * radius + 3) (fun k _ => costBound k)
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul] using
      Nat.add_le_add_left hsum (F+C)

end D5.S0.Computability.PhysicalDivider
