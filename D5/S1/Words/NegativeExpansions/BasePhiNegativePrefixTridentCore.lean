/- GID: D5/S1/Words/NegativeExpansions/BasePhiNegativePrefixTridentCore
   generality: I
   mirror-B: none(waiver:negative-prefix-trident-core-classification)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Canonical negative-prefix Core sets are exact Lucas-gap sequence ranges. -/

import D5.S1.Words.NegativeExpansions.BasePhiNegativeTailWords

namespace D5.X_Frontier.BasePhiNegativePrefixTrident

open D5.S0.Carrier
open D5.S1.Scale
open D5.S1.Words.Expansions.BasePhiCanonicalExpansion
open D5.S1.Words.Expansions.BasePhiCarryTransducer
open D5.S1.Words.Expansions.BasePhiNegative
open D5.S1.Words.Expansions.BasePhiRecursiveStructure
open D5.S1.Words.Expansions.BasePhiTailBounds
open D5.S1.Words.NegativeExpansions.NegaFibonacci
open D5.S1.Words.NegativeExpansions.BasePhiNegativeTailWords

noncomputable section

private noncomputable def completeDepth (q : Nat) : Nat :=
  let raw := negativeDigits canonicalExpansion q
  if h : raw.support.Nonempty then raw.support.max' h + 1 else 0

private def completeWordFrom (q start depth : Nat) : List Nat :=
  List.ofFn fun i : Fin depth =>
    negativeDigits canonicalExpansion q (start + i.1)

def completeWord (q : Nat) : List Nat :=
  completeWordFrom q 0 (completeDepth q)

@[simp] private theorem completeWordFrom_length (q start depth : Nat) :
    (completeWordFrom q start depth).length = depth := by
  simp [completeWordFrom]

private theorem completeWordFrom_succ (q start depth : Nat) :
    completeWordFrom q start (depth + 1) =
      negativeDigits canonicalExpansion q start ::
        completeWordFrom q (start + 1) depth := by
  rw [completeWordFrom, List.ofFn_succ]
  congr 1
  apply congrArg List.ofFn
  funext i
  congr 1
  rw [Fin.val_succ]
  omega

private theorem completeWordFrom_canonical (q start : Nat) :
    ∀ depth : Nat, Canonical (completeWordFrom q start depth)
  | 0 => by simp [completeWordFrom, Canonical]
  | depth + 1 => by
      rw [completeWordFrom_succ]
      have hbinary := canonicalExpansion.binary q
        (-((start + 1 : Nat) : Int))
      refine ⟨(by simpa only [negativeDigits_apply] using hbinary), ?_,
        completeWordFrom_canonical q (start + 1) depth⟩
      cases depth with
      | zero => trivial
      | succ depth =>
          rw [completeWordFrom_succ]
          dsimp
          intro hcurrent
          by_contra hnext
          have hnextOne : negativeDigits canonicalExpansion q (start + 1) = 1 := by
            have hnextLe := canonicalExpansion.binary q
              (-(((start + 1) + 1 : Nat) : Int))
            rw [← negativeDigits_apply] at hnextLe
            omega
          have hzero := canonicalExpansion.canonical q
            (-(((start + 1) + 1 : Nat) : Int)) hnextOne
          have hindex : -(((start + 1) + 1 : Nat) : Int) + 1 =
              -((start + 1 : Nat) : Int) := by
            push_cast
            ring
          rw [hindex, ← negativeDigits_apply] at hzero
          omega

private theorem raw_nonempty_of_reaches {q depth : Nat}
    (hreaches : reachesNegativeDepth canonicalExpansion q depth) :
    (negativeDigits canonicalExpansion q).support.Nonempty := by
  obtain ⟨hdepth, i, hiSupport, hiDepth⟩ := hreaches
  have hiNeg : i < 0 := by
    have hcast : (0 : Int) < (depth : Int) := by exact_mod_cast hdepth
    omega
  let k : Nat := (-i).toNat - 1
  have hminusPos : 0 < (-i).toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  have hcast : ((-i).toNat : Int) = -i := Int.toNat_of_nonneg (by omega)
  have hk : k + 1 = (-i).toNat := Nat.sub_add_cancel (by omega)
  have hindex : -((k + 1 : Nat) : Int) = i := by
    rw [hk, hcast]
    ring
  refine ⟨k, ?_⟩
  rw [Finsupp.mem_support_iff, negativeDigits_apply, hindex]
  exact Finsupp.mem_support_iff.mp hiSupport

private theorem completeDepth_eq_max_add_one {q : Nat}
    (hnonempty : (negativeDigits canonicalExpansion q).support.Nonempty) :
    completeDepth q =
      (negativeDigits canonicalExpansion q).support.max' hnonempty + 1 := by
  simp [completeDepth, hnonempty]

theorem completeWord_canonical (q : Nat) : Canonical (completeWord q) :=
  completeWordFrom_canonical q 0 (completeDepth q)

theorem completeWord_last_one {q depth : Nat}
    (hreaches : reachesNegativeDepth canonicalExpansion q depth) :
    (completeWord q).getLast? = some 1 := by
  let raw := negativeDigits canonicalExpansion q
  have hnonempty : raw.support.Nonempty := raw_nonempty_of_reaches hreaches
  let last := raw.support.max' hnonempty
  have hdepth : completeDepth q = last + 1 := by
    exact completeDepth_eq_max_add_one hnonempty
  have hlastMem : last ∈ raw.support := Finset.max'_mem _ _
  have hlastNonzero : raw last ≠ 0 := Finsupp.mem_support_iff.mp hlastMem
  have hlastLe : raw last ≤ 1 := by
    simpa [raw] using canonicalExpansion.binary q (-((last + 1 : Nat) : Int))
  have hlastOne : raw last = 1 := by omega
  rw [show completeWord q = completeWordFrom q 0 (last + 1) by
    simp [completeWord, hdepth]]
  rw [List.getLast?_eq_getLast_of_ne_nil (by
    intro hzero
    have := congrArg List.length hzero
    simp [completeWordFrom] at this)]
  simp only [completeWordFrom]
  rw [List.getLast_ofFn_succ]
  simpa [completeWordFrom, raw] using hlastOne

private theorem raw_eq_zero_above_depth {q k : Nat}
    (hk : completeDepth q ≤ k) : negativeDigits canonicalExpansion q k = 0 := by
  let raw := negativeDigits canonicalExpansion q
  by_cases hnonempty : raw.support.Nonempty
  · have hdepth := completeDepth_eq_max_add_one hnonempty
    by_contra hnonzero
    have hmem : k ∈ raw.support := Finsupp.mem_support_iff.mpr hnonzero
    have hle := Finset.le_max' raw.support k hmem
    dsimp [raw] at hdepth hle ⊢
    omega
  · have hzero : raw.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    have hrawZero : raw = 0 := Finsupp.support_eq_empty.mp hzero
    dsimp [raw] at hrawZero ⊢
    rw [hrawZero]
    rfl

private theorem completeWord_getD (q k : Nat) :
    (completeWord q).getD k 0 = negativeDigits canonicalExpansion q k := by
  by_cases hk : k < completeDepth q
  · rw [List.getD_eq_getElem?_getD]
    have hget : (completeWord q)[k]? =
        some (negativeDigits canonicalExpansion q k) := by
      simp [completeWord, completeWordFrom, hk]
    rw [hget]
    rfl
  · have hle : completeDepth q ≤ k := Nat.le_of_not_gt hk
    have hzero := raw_eq_zero_above_depth (q := q) (k := k) hle
    rw [List.getD_eq_getElem?_getD]
    have hout : (completeWord q)[k]? = none := by
      rw [List.getElem?_eq_none_iff]
      simpa [completeWord] using hle
    rw [hout, hzero]
    rfl

theorem completeWord_value (q : Nat) :
    basePhiValue (wordDigits (completeWord q)) =
      basePhiValue (negativePart canonicalExpansion q) := by
  congr 1
  apply Finsupp.ext
  intro i
  by_cases hi : i < 0
  · let k : Nat := (-i).toNat - 1
    have hminusPos : 0 < (-i).toNat := by
      apply Nat.pos_of_ne_zero
      intro hzero
      have := Int.toNat_eq_zero.mp hzero
      omega
    have hcast : ((-i).toNat : Int) = -i := Int.toNat_of_nonneg (by omega)
    have hk : k + 1 = (-i).toNat := Nat.sub_add_cancel (by omega)
    have hindex : -((k + 1 : Nat) : Int) = i := by rw [hk, hcast]; ring
    rw [← hindex, wordDigits_apply_neg, completeWord_getD,
      negativePart_apply, ← negativeDigits_apply]
  · rw [wordDigits_nonnegative (completeWord q) i (le_of_not_gt hi),
      negativePart_eq_zero_of_nonnegative canonicalExpansion q (le_of_not_gt hi)]

def prefixWord (w : List Bool) : List Nat :=
  w.map fun bit => if bit then 1 else 0

@[simp] theorem prefixWord_length (w : List Bool) :
    (prefixWord w).length = w.length := by simp [prefixWord]

private theorem completeDepth_ge_of_reaches {q depth : Nat}
    (hreaches : reachesNegativeDepth canonicalExpansion q depth) :
    depth ≤ completeDepth q := by
  obtain ⟨hdepth, i, hiSupport, hiBound⟩ := hreaches
  have hiNeg : i < 0 := by
    have : (0 : Int) < (depth : Int) := by exact_mod_cast hdepth
    omega
  let k : Nat := (-i).toNat - 1
  have hminusPos : 0 < (-i).toNat := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have := Int.toNat_eq_zero.mp hzero
    omega
  have hcast : ((-i).toNat : Int) = -i := Int.toNat_of_nonneg (by omega)
  have hk : k + 1 = (-i).toNat := Nat.sub_add_cancel (by omega)
  have hindex : -((k + 1 : Nat) : Int) = i := by rw [hk, hcast]; ring
  have hkMem : k ∈ (negativeDigits canonicalExpansion q).support := by
    rw [Finsupp.mem_support_iff, negativeDigits_apply, hindex]
    exact Finsupp.mem_support_iff.mp hiSupport
  have hnonempty : (negativeDigits canonicalExpansion q).support.Nonempty := ⟨k, hkMem⟩
  have hkMax := Finset.le_max' (negativeDigits canonicalExpansion q).support k hkMem
  have hdepthEq := completeDepth_eq_max_add_one hnonempty
  have hdepthK : depth ≤ k + 1 := by
    have hcastDepth : (depth : Int) ≤ (k + 1 : Nat) := by
      rw [← hindex] at hiBound
      omega
    exact_mod_cast hcastDepth
  omega

private theorem completeWord_getElem {q i : Nat}
    (hi : i < (completeWord q).length) :
    (completeWord q)[i] = negativeDigits canonicalExpansion q i := by
  have h := completeWord_getD q i
  rw [List.getD_eq_getElem _ _ hi] at h
  exact h

private theorem completeWord_take_prefix {w : List Bool} {q : Nat}
    (hoccurs : NegativePrefixOccurs canonicalExpansion w q) :
    (completeWord q).take w.length = prefixWord w := by
  have hdepth : w.length ≤ completeDepth q :=
    completeDepth_ge_of_reaches hoccurs.1
  apply List.ext_getElem
  · simp [completeWord, hdepth]
  · intro i hiLeft hiRight
    have hi : i < w.length := by simpa using hiRight
    rw [List.getElem_take, completeWord_getElem (by simpa [completeWord] using
      (show i < completeDepth q by omega))]
    change negativeDigits canonicalExpansion q i =
      (w.map fun bit => if bit then 1 else 0)[i]
    have hbit := hoccurs.2 ⟨i, hi⟩
    unfold negativeDigit at hbit
    rw [← negativeDigits_apply] at hbit
    have hdigitLe := canonicalExpansion.binary q (-((i + 1 : Nat) : Int))
    rw [← negativeDigits_apply] at hdigitLe
    cases hvalue : w[i] with
    | false =>
        have hvalue' : w.get ⟨i, hi⟩ = false := by simpa using hvalue
        have hne : negativeDigits canonicalExpansion q i ≠ 1 := by
          intro hone
          have : decide (negativeDigits canonicalExpansion q i = 1) = true :=
            decide_eq_true hone
          rw [hbit, hvalue'] at this
          contradiction
        have hzero : negativeDigits canonicalExpansion q i = 0 := by omega
        have hiMap : i < (w.map (fun bit : Bool => if bit then 1 else 0)).length := by
          simp [hi]
        change negativeDigits canonicalExpansion q i =
          (w.map (fun bit : Bool => if bit then 1 else 0))[i]'hiMap
        rw [List.getElem_map]
        simp [hzero]
        exact hvalue
    | true =>
        have hvalue' : w.get ⟨i, hi⟩ = true := by simpa using hvalue
        have hone : negativeDigits canonicalExpansion q i = 1 := by
          apply of_decide_eq_true
          rw [hbit, hvalue']
        have hiMap : i < (w.map (fun bit : Bool => if bit then 1 else 0)).length := by
          simp [hi]
        change negativeDigits canonicalExpansion q i =
          (w.map (fun bit : Bool => if bit then 1 else 0))[i]'hiMap
        rw [List.getElem_map]
        simp [hone]
        exact hvalue

theorem completeWord_split_prefix {w : List Bool} {q : Nat}
    (hoccurs : NegativePrefixOccurs canonicalExpansion w q) :
    completeWord q = prefixWord w ++ (completeWord q).drop w.length := by
  rw [← completeWord_take_prefix hoccurs]
  exact (List.take_append_drop w.length (completeWord q)).symm

private theorem complete_tail_b_nonpositive (q : Nat) :
    (basePhiValue (negativePart canonicalExpansion q)).b ≤ 0 := by
  have hsum := negativeValue_add_positiveValue canonicalExpansion q
  have hpositive := positiveValue_coordinates canonicalExpansion q
  have hcoordNonneg :
      0 ≤ positiveCoordinate (positiveIndex canonicalExpansion q) := by
    rw [positiveCoordinate, div_eq_mul_inv]
    apply Int.floor_nonneg.mpr
    positivity
  have hb := congrArg GoldenInt.b hsum
  rw [b_add, hpositive.2] at hb
  simp at hb
  omega

private theorem completeWord_reverse_weight_pos {w : List Bool} {q : Nat}
    (hoccurs : NegativePrefixOccurs canonicalExpansion w q) :
    0 < weight (completeWord q).reverse := by
  have hlast := completeWord_last_one hoccurs.1
  have hcanonical := completeWord_canonical q
  have hweight := reverse_weight_eq_neg_b (completeWord q).reverse
  simp only [List.reverse_reverse] at hweight
  rw [completeWord_value] at hweight
  have hnonnegative := complete_tail_b_nonpositive q
  have hnonzero :
      (basePhiValue (negativePart canonicalExpansion q)).b ≠ 0 := by
    intro hbzero
    have hbounds := negative_tail_real_bounds canonicalExpansion q ⟨w.length, hoccurs.1⟩
    have hembedding := embedding_basePhiValue_negativePart canonicalExpansion q
    have haReal :
        embedding (basePhiValue (negativePart canonicalExpansion q)) =
          ((basePhiValue (negativePart canonicalExpansion q)).a : Real) := by
      rw [embedding_apply, hbzero]
      ring
    rw [← hembedding, haReal] at hbounds
    have haInt : (0 : Int) < (basePhiValue
        (negativePart canonicalExpansion q)).a := by exact_mod_cast hbounds.1
    have haLt : (basePhiValue
        (negativePart canonicalExpansion q)).a < (1 : Int) := by exact_mod_cast hbounds.2.1
    omega
  omega

theorem completeWord_length_even {w : List Bool} {q : Nat}
    (hoccurs : NegativePrefixOccurs canonicalExpansion w q) :
    Even (completeWord q).length := by
  have hcanonical := canonical_reverse (completeWord_canonical q)
  have hhead : (completeWord q).reverse.head? = some 1 := by
    simpa using completeWord_last_one hoccurs.1
  have := even_length_of_head_one hcanonical hhead
    (completeWord_reverse_weight_pos hoccurs)
  simpa using this

private def traceA (m : Nat) : Int :=
  2 * (Nat.fib (m + 1) : Int) - Nat.fib m

private def traceC (m : Nat) : Int :=
  (Nat.fib (m + 1) : Int) - 3 * Nat.fib m

private theorem traceA_sub_traceC (m : Nat) :
    traceA m - traceC m = goldenLucas (m + 1) := by
  rw [golden_lucas_succ_eq_fib_add_fib, Nat.fib_add_two]
  simp only [traceA, traceC]
  push_cast
  ring

private theorem two_traceA_sub_traceC (m : Nat) :
    2 * traceA m - traceC m = goldenLucas (m + 2) := by
  rw [show m + 2 = (m + 1) + 1 by omega,
    golden_lucas_succ_eq_fib_add_fib,
    show m + 1 + 2 = (m + 1) + 2 by rfl,
    Nat.fib_add_two, Nat.fib_add_two]
  simp only [traceA, traceC]
  push_cast
  ring

private theorem shifted_trace (m : Nat) (x : GoldenInt) :
    trace
        ((((phiUnit ^ (-(m : Int)) : GoldenIntˣ) : GoldenInt)) * x) =
      (-1 : Int) ^ m * (traceA m * x.a + traceC m * x.b) := by
  have hcoordinates := negative_phiUnit_coordinates m
  dsimp at hcoordinates
  rw [trace, a_mul, b_mul, hcoordinates.1, hcoordinates.2, pow_succ]
  simp only [traceA, traceC]
  ring

private theorem trace_wordDigits_append (left right : List Nat) :
    trace (basePhiValue (wordDigits (left ++ right))) =
      trace (basePhiValue (wordDigits left)) +
        (-1 : Int) ^ left.length *
          (traceA left.length * (basePhiValue (wordDigits right)).a +
            traceC left.length * (basePhiValue (wordDigits right)).b) := by
  rw [wordDigits_append, basePhiValue_add, shiftDigits_eval]
  rw [show ∀ x y : GoldenInt, trace (x + y) = trace x + trace y by
    intro x y; simp [trace]; ring]
  rw [shifted_trace]

private theorem floor_goldenRatio : ⌊Real.goldenRatio⌋ = (1 : Int) := by
  have hsquare : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsnonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hslowTwo : 2 ≤ Real.sqrt 5 := by nlinarith
  have hshighThree : Real.sqrt 5 < 3 := by nlinarith
  rw [Int.floor_eq_iff]
  constructor <;> simp [Real.goldenRatio] <;> nlinarith

private theorem fibonacci_floor_gap (n : Nat) :
    (⌊((n + 2 : Nat) : Real) * Real.goldenRatio⌋ : Int) -
        ⌊((n + 1 : Nat) : Real) * Real.goldenRatio⌋ =
      if fibonacciGapLetter n then 2 else 1 := by
  let x : Real := ((n + 1 : Nat) : Real) * Real.goldenRatio
  have hlower := Int.le_floor_add x Real.goldenRatio
  have hupper := Int.le_floor_add_floor x Real.goldenRatio
  rw [floor_goldenRatio] at hlower hupper
  have harg : ((n + 2 : Nat) : Real) * Real.goldenRatio =
      x + Real.goldenRatio := by
    dsimp [x]
    push_cast
    ring
  have hlower' :
      (⌊((n + 1 : Nat) : Real) * Real.goldenRatio⌋ : Int) + 1 ≤
        ⌊((n + 2 : Nat) : Real) * Real.goldenRatio⌋ := by
    rw [harg]
    exact hlower
  have hupper' :
      (⌊((n + 2 : Nat) : Real) * Real.goldenRatio⌋ : Int) - 1 ≤
        ⌊((n + 1 : Nat) : Real) * Real.goldenRatio⌋ + 1 := by
    rw [harg]
    exact hupper
  have hbounds :
      (⌊((n + 2 : Nat) : Real) * Real.goldenRatio⌋ : Int) -
          ⌊((n + 1 : Nat) : Real) * Real.goldenRatio⌋ = 1 ∨
        (⌊((n + 2 : Nat) : Real) * Real.goldenRatio⌋ : Int) -
          ⌊((n + 1 : Nat) : Real) * Real.goldenRatio⌋ = 2 := by
    omega
  by_cases htwo :
      (⌊((n + 2 : Nat) : Real) * Real.goldenRatio⌋ : Int) -
          ⌊((n + 1 : Nat) : Real) * Real.goldenRatio⌋ = 2
  · push_cast at htwo ⊢
    simp [fibonacciGapLetter, htwo]
  · have hone := hbounds.resolve_right htwo
    push_cast at htwo hone ⊢
    simp [fibonacciGapLetter, hone]

noncomputable def positiveSuffixSequence (m : Nat) (T : Int) (n : Nat) : Int :=
  T + traceA m * ⌊((n + 1 : Nat) : Real) * Real.goldenRatio⌋ + traceA m -
    traceC m * (n + 1 : Nat) - 1

noncomputable def negativeSuffixSequence (m : Nat) (T : Int) (n : Nat) : Int :=
  T + traceA m * ⌊((n + 1 : Nat) : Real) * Real.goldenRatio⌋ -
    traceC m * (n + 1 : Nat) - 1

theorem positiveSuffixSequence_zero (m : Nat) (T : Int) :
    positiveSuffixSequence m T 0 = T + goldenLucas (m + 2) - 1 := by
  norm_num [positiveSuffixSequence, floor_goldenRatio]
  have h := two_traceA_sub_traceC m
  omega

theorem negativeSuffixSequence_zero (m : Nat) (T : Int) :
    negativeSuffixSequence m T 0 = T + goldenLucas (m + 1) - 1 := by
  norm_num [negativeSuffixSequence, floor_goldenRatio]
  have h := traceA_sub_traceC m
  omega

private theorem positiveSuffixSequence_succ (m : Nat) (T : Int) (n : Nat) :
    positiveSuffixSequence m T (n + 1) = positiveSuffixSequence m T n +
      if familyLetter .F n then goldenLucas (m + 2) else goldenLucas (m + 1) := by
  change positiveSuffixSequence m T (n + 1) = positiveSuffixSequence m T n +
    if fibonacciGapLetter n then goldenLucas (m + 2) else goldenLucas (m + 1)
  have hgap := fibonacci_floor_gap n
  by_cases hletter : fibonacciGapLetter n
  · rw [if_pos hletter] at hgap ⊢
    have hfloor :
        (⌊((n + 2 : Nat) : Real) * Real.goldenRatio⌋ : Int) =
          ⌊((n + 1 : Nat) : Real) * Real.goldenRatio⌋ + 2 := by omega
    simp only [positiveSuffixSequence, show n + 1 + 1 = n + 2 by omega]
    rw [hfloor, ← two_traceA_sub_traceC]
    push_cast
    ring
  · rw [if_neg hletter] at hgap ⊢
    have hfloor :
        (⌊((n + 2 : Nat) : Real) * Real.goldenRatio⌋ : Int) =
          ⌊((n + 1 : Nat) : Real) * Real.goldenRatio⌋ + 1 := by omega
    simp only [positiveSuffixSequence, show n + 1 + 1 = n + 2 by omega]
    rw [hfloor, ← traceA_sub_traceC]
    push_cast
    ring

private theorem negativeSuffixSequence_succ (m : Nat) (T : Int) (n : Nat) :
    negativeSuffixSequence m T (n + 1) = negativeSuffixSequence m T n +
      if familyLetter .F n then goldenLucas (m + 2) else goldenLucas (m + 1) := by
  change negativeSuffixSequence m T (n + 1) = negativeSuffixSequence m T n +
    if fibonacciGapLetter n then goldenLucas (m + 2) else goldenLucas (m + 1)
  have hgap := fibonacci_floor_gap n
  by_cases hletter : fibonacciGapLetter n
  · rw [if_pos hletter] at hgap ⊢
    have hfloor :
        (⌊((n + 2 : Nat) : Real) * Real.goldenRatio⌋ : Int) =
          ⌊((n + 1 : Nat) : Real) * Real.goldenRatio⌋ + 2 := by omega
    simp only [negativeSuffixSequence, show n + 1 + 1 = n + 2 by omega]
    rw [hfloor, ← two_traceA_sub_traceC]
    push_cast
    ring
  · rw [if_neg hletter] at hgap ⊢
    have hfloor :
        (⌊((n + 2 : Nat) : Real) * Real.goldenRatio⌋ : Int) =
          ⌊((n + 1 : Nat) : Real) * Real.goldenRatio⌋ + 1 := by omega
    simp only [negativeSuffixSequence, show n + 1 + 1 = n + 2 by omega]
    rw [hfloor, ← traceA_sub_traceC]
    push_cast
    ring

theorem positiveSuffixSequence_eq_vF (m : Nat) (T : Int) :
    positiveSuffixSequence m T =
      vF (goldenLucas (m + 2)) (goldenLucas (m + 1))
        (T + goldenLucas (m + 2) - 1) := by
  funext n
  induction n with
  | zero => rw [positiveSuffixSequence_zero]; rfl
  | succ n ih => rw [positiveSuffixSequence_succ, vF_succ, ih]

theorem negativeSuffixSequence_eq_vF (m : Nat) (T : Int) :
    negativeSuffixSequence m T =
      vF (goldenLucas (m + 2)) (goldenLucas (m + 1))
        (T + goldenLucas (m + 1) - 1) := by
  funext n
  induction n with
  | zero => rw [negativeSuffixSequence_zero]; rfl
  | succ n ih => rw [negativeSuffixSequence_succ, vF_succ, ih]

private theorem vG_succ_eq_vF (a b r : Int) (n : Nat) :
    vG a b r (n + 1) = vF a b (r + b) n := by
  induction n with
  | zero => simp [vG, vF, gapSequence, familyLetter]
  | succ n ih => rw [vG_succ, vF_succ, ih]; rfl

noncomputable def exactThenNegativeSequence (m : Nat) (T : Int) : Nat → Int
  | 0 => T - 1
  | n + 1 => negativeSuffixSequence m T n

theorem exactThenNegative_eq_vG (m : Nat) (T : Int) :
    exactThenNegativeSequence m T =
      vG (goldenLucas (m + 2)) (goldenLucas (m + 1)) (T - 1) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      change negativeSuffixSequence m T n = _
      rw [vG_succ_eq_vF]
      have h := congrFun (negativeSuffixSequence_eq_vF m T) n
      rw [h]
      congr 2
      ring

theorem trace_word_gt_one {word : List Nat}
    (hcanonical : Canonical word) (hlast : word.getLast? = some 1)
    (heven : Even word.length) :
    1 < trace (basePhiValue (wordDigits word)) := by
  have hreverseCanonical := canonical_reverse hcanonical
  have hhead : word.reverse.head? = some 1 := by simpa using hlast
  have hreverseEven : Even word.reverse.length := by simpa using heven
  have hweightPos := weight_pos_of_head_one_even hreverseCanonical hhead hreverseEven
  let k := (weight word.reverse).toNat
  have hkCast : (k : Int) = weight word.reverse :=
    Int.toNat_of_nonneg hweightPos.le
  have hkPos : 0 < k := by
    have : (0 : Int) < (k : Int) := by rw [hkCast]; exact hweightPos
    exact_mod_cast this
  have hcoordinates := positive_word_coordinates hreverseCanonical hhead
    hkCast.symm hkPos
  simp only [List.reverse_reverse] at hcoordinates
  have hfloorLower :
      (k : Int) ≤ ⌊(k : Real) * Real.goldenRatio⌋ := by
    apply Int.le_floor.mpr
    norm_num only [Int.cast_natCast]
    calc
      (k : Real) = (k : Real) * 1 := by ring
      _ ≤ (k : Real) * Real.goldenRatio :=
        mul_le_mul_of_nonneg_left Real.one_lt_goldenRatio.le (by positivity)
  omega

theorem trace_append_positive (left digits : List Nat) (n : Nat)
    (hcanonical : Canonical digits) (hhead : digits.head? = some 1)
    (hweight : weight digits = (n + 1 : Nat))
    (heven : Even left.length) :
    trace (basePhiValue (wordDigits (left ++ digits.reverse))) - 1 =
      positiveSuffixSequence left.length
        (trace (basePhiValue (wordDigits left))) n := by
  have hcoordinates := positive_word_coordinates hcanonical hhead hweight (by omega)
  dsimp at hcoordinates
  rw [trace_wordDigits_append, heven.neg_one_pow,
    hcoordinates.1, hcoordinates.2.1]
  simp only [positiveSuffixSequence]
  push_cast
  ring

theorem trace_append_negative (left digits : List Nat) (n : Nat)
    (hcanonical : Canonical digits) (hhead : digits.head? = some 1)
    (hweight : weight digits = -((n + 1 : Nat) : Int))
    (hodd : Odd left.length) :
    trace (basePhiValue (wordDigits (left ++ digits.reverse))) - 1 =
      negativeSuffixSequence left.length
        (trace (basePhiValue (wordDigits left))) n := by
  have hcoordinates := negative_word_coordinates hcanonical hhead hweight (by omega)
  dsimp at hcoordinates
  rw [trace_wordDigits_append, hodd.neg_one_pow,
    hcoordinates.1, hcoordinates.2.1]
  simp only [negativeSuffixSequence]
  push_cast
  ring

theorem prefixWord_canonical_of_occurs {w : List Bool} {q : Nat}
    (hoccurs : NegativePrefixOccurs canonicalExpansion w q) :
    Canonical (prefixWord w) := by
  have hcanonical := canonical_take w.length (completeWord_canonical q)
  rw [completeWord_take_prefix hoccurs] at hcanonical
  exact hcanonical

theorem core_of_suffix_word {w : List Bool} {suffix : List Nat}
    (hw : w ≠ [])
    (hcanonical : Canonical (prefixWord w ++ suffix))
    (hlast : (prefixWord w ++ suffix).getLast? = some 1)
    (heven : Even (prefixWord w ++ suffix).length) :
    let q :=
      (trace (basePhiValue (wordDigits (prefixWord w ++ suffix))) - 1).toNat
    q ∈ Core w := by
  let word := prefixWord w ++ suffix
  have htrace : 1 < trace (basePhiValue (wordDigits word)) :=
    trace_word_gt_one hcanonical hlast heven
  let q := (trace (basePhiValue (wordDigits word)) - 1).toNat
  have hword := fiberStart_of_word hcanonical hlast htrace
  change q ∈ Core w
  refine ⟨hword.1, ?_⟩
  have hwLength : 0 < w.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hw (List.eq_nil_of_length_eq_zero hzero)
  have hwordNonempty : word ≠ [] := by
    intro hnil
    have hlast' : word.getLast? = some 1 := hlast
    rw [hnil] at hlast'
    simp at hlast'
  obtain ⟨k, hlength⟩ := Nat.exists_eq_succ_of_ne_zero
    (by intro hzero; exact hwordNonempty (List.eq_nil_of_length_eq_zero hzero))
  have hdeep := wordDigits_deepest hlast
  have hone : canonicalExpansion.digit q (-((k + 1 : Nat) : Int)) = 1 := by
    rw [← negativePart_apply canonicalExpansion q k, hword.2]
    simpa [word, hlength] using hdeep
  refine ⟨⟨hwLength, -((k + 1 : Nat) : Int),
    Finsupp.mem_support_iff.mpr (by omega), ?_⟩, ?_⟩
  · have hwordLength : w.length ≤ word.length := by simp [word]
    rw [hlength] at hwordLength
    push_cast
    omega
  · intro i
    unfold negativeDigit
    rw [← negativePart_apply canonicalExpansion q i.1, hword.2,
      wordDigits_apply_neg]
    have hiPrefix : i.1 < (prefixWord w).length := by
      rw [prefixWord_length]
      exact i.2
    rw [List.getD_append _ _ _ _ hiPrefix,
      List.getD_eq_getElem _ _ hiPrefix]
    change decide ((w.map fun bit => if bit then 1 else 0)[i.1] = 1) = w.get i
    cases hbit : w.get i with
    | false =>
        have hbit' : w[i.1] = false := by simpa using hbit
        have hiMap : (i : ℕ) < (w.map (fun bit : Bool => if bit then 1 else 0)).length := by
          simp [hiPrefix]
        change decide ((w.map (fun bit : Bool => if bit then 1 else 0))[i.1]'hiMap = 1) = false
        rw [List.getElem_map]
        simp [hbit']
    | true =>
        have hbit' : w[i.1] = true := by simpa using hbit
        have hiMap : (i : ℕ) < (w.map (fun bit : Bool => if bit then 1 else 0)).length := by
          simp [hiPrefix]
        change decide ((w.map (fun bit : Bool => if bit then 1 else 0))[i.1]'hiMap = 1) = true
        rw [List.getElem_map]
        simp [hbit']

end

end D5.X_Frontier.BasePhiNegativePrefixTrident
