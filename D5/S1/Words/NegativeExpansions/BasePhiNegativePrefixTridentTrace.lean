/- GID: D5/S1/Words/NegativeExpansions/BasePhiNegativePrefixTridentTrace
   generality: I
   mirror-B: none(waiver:negative-prefix-trident-trace-support)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: A negative-tail fiber start is one below the integral trace of its complete tail. -/

import D5.S1.Words.Expansions.BasePhiNegativePrefixTridentSupport

namespace D5.X_Frontier.BasePhiNegativePrefixTrident

open D5.S0.Carrier
open D5.S1.Scale
open D5.S1.Words.Expansions.BasePhiCanonicalExpansion
open D5.S1.Words.Expansions.BasePhiCarryTransducer
open D5.S1.Words.Expansions.BasePhiNegative
open D5.S1.Words.Expansions.BasePhiRecursiveStructure
open D5.S1.Words.Expansions.BasePhiTailBounds

noncomputable section

private theorem tail_coordinates (q : Nat) :
    let tail := basePhiValue (negativePart canonicalExpansion q)
    let v := positiveIndex canonicalExpansion q
    let B := positiveCoordinate v
    tail.b = -B ∧ (q : Int) = tail.a + (v : Int) - 2 * B := by
  let tail := basePhiValue (negativePart canonicalExpansion q)
  let v := positiveIndex canonicalExpansion q
  let B := positiveCoordinate v
  have hsum := negativeValue_add_positiveValue canonicalExpansion q
  have hpositive := positiveValue_coordinates canonicalExpansion q
  have hb := congrArg GoldenInt.b hsum
  have ha := congrArg GoldenInt.a hsum
  dsimp [tail, v, B] at hpositive hb ha ⊢
  constructor <;> omega

private theorem same_tail_coordinates {m q : Nat} (hsame : SameNegativeTail m q) :
    positiveCoordinate (positiveIndex canonicalExpansion m) =
        positiveCoordinate (positiveIndex canonicalExpansion q) ∧
      (m : Int) =
        (basePhiValue (negativePart canonicalExpansion q)).a +
          (positiveIndex canonicalExpansion m : Int) -
            2 * positiveCoordinate (positiveIndex canonicalExpansion q) := by
  have htail :
      basePhiValue (negativePart canonicalExpansion m) =
        basePhiValue (negativePart canonicalExpansion q) := by
    apply (sameNegativeTail_iff_negativeValue_eq canonicalExpansion m q).mp
    exact hsame
  have hm := tail_coordinates m
  have hq := tail_coordinates q
  dsimp at hm hq ⊢
  have ha := congrArg GoldenInt.a htail
  have hb := congrArg GoldenInt.b htail
  constructor <;> omega

theorem fiberStart_trace {q : Nat}
    (hreaches : ∃ depth, reachesNegativeDepth canonicalExpansion q depth)
    (hstart : fiberStart q) :
    trace (basePhiValue (negativePart canonicalExpansion q)) = (q : Int) + 1 := by
  let tail := basePhiValue (negativePart canonicalExpansion q)
  let v := positiveIndex canonicalExpansion q
  let B := positiveCoordinate v
  let start := fiberStartInt tail B
  have hcoords := tail_coordinates q
  have hreal := negative_tail_real_bounds canonicalExpansion q hreaches
  have hembedding := embedding_basePhiValue_negativePart canonicalExpansion q
  have hformula : embedding tail = (tail.a : Real) - (B : Real) * Real.goldenRatio := by
    have hb : tail.b = -B := by
      simpa [tail, B, v] using hcoords.1
    rw [embedding_apply, hb]
    push_cast
    ring
  have htailPos : 0 < embedding tail := by
    simpa [tail, hembedding] using hreal.1
  have htailLtOne : embedding tail < 1 := by
    simpa [tail, hembedding] using hreal.2.1
  have hvCoordinate : positiveCoordinate v = B := rfl
  have hvStart : (v : Int) = start := by
    cases hhead : negativeDigit canonicalExpansion q 0 with
    | true =>
        have hlarge : Real.goldenRatio⁻¹ ≤ embedding tail := by
          have := hreal.2.2.1 hhead
          simpa [tail, hembedding] using this
        have hvBounds :=
          (positiveCoordinate_fiber_large tail B hformula hlarge htailLtOne v).mp
            hvCoordinate
        have hminusOne : canonicalExpansion.digit q (-1) = 1 :=
          of_decide_eq_true hhead
        have hzero := canonicalExpansion.canonical q (-1) hminusOne
        norm_num at hzero
        have hrawZero : nonnegativeDigits canonicalExpansion q 0 = 0 := by
          simpa [nonnegativeDigits_apply] using hzero
        have hsuccCoordinate : positiveCoordinate (v + 1) = B := by
          have hsucc := (canonical_zero_digit_iff_coordinate_succ
            (nonnegativeDigits_canonical canonicalExpansion q)).mp hrawZero
          exact hsucc.trans hvCoordinate
        have hsuccBounds :=
          (positiveCoordinate_fiber_large tail B hformula hlarge htailLtOne
            (v + 1)).mp hsuccCoordinate
        dsimp [start]
        omega
    | false =>
        have hsmall : embedding tail < Real.goldenRatio⁻¹ := by
          have := hreal.2.2.2 hhead
          simpa [tail, hembedding] using this
        have hvBounds :=
          (positiveCoordinate_fiber_small tail B hformula htailPos hsmall v).mp
            hvCoordinate
        have hqPositive : 0 < q := hstart.1.1
        have hfiber :=
          (D5.S1.Words.Expansions.BasePhiTailFiber.negative_tail_fiber_shape
            canonicalExpansion q hqPositive hreaches).2 hhead
        obtain ⟨s, hs, _⟩ := hfiber
        have hsMemRecursive :
            s ∈ D5.S1.Words.Expansions.BasePhiRecursiveStructure.negativeTailFiber
              canonicalExpansion q := by
          rw [hs.2.2]
          simp
        have hsMem : s ∈ negativeTailFiber q := hsMemRecursive
        have hsEq : s = q := by
          have := hstart.2 s hsMem
          omega
        have hqOneMemRecursive :
            q + 1 ∈ D5.S1.Words.Expansions.BasePhiRecursiveStructure.negativeTailFiber
              canonicalExpansion q := by
          rw [hs.2.2, hsEq]
          simp
        have hqTwoMemRecursive :
            q + 2 ∈ D5.S1.Words.Expansions.BasePhiRecursiveStructure.negativeTailFiber
              canonicalExpansion q := by
          rw [hs.2.2, hsEq]
          simp
        have hqOneMem : q + 1 ∈ negativeTailFiber q := hqOneMemRecursive
        have hqTwoMem : q + 2 ∈ negativeTailFiber q := hqTwoMemRecursive
        have hcoordOne := (same_tail_coordinates hqOneMem.2).1
        have hcoordTwo := (same_tail_coordinates hqTwoMem.2).1
        have hvalueOne := (same_tail_coordinates hqOneMem.2).2
        have hvalueTwo := (same_tail_coordinates hqTwoMem.2).2
        have hvOne : positiveIndex canonicalExpansion (q + 1) = v + 1 := by
          dsimp [tail, v, B] at hcoords hvalueOne
          exact_mod_cast (show
            (positiveIndex canonicalExpansion (q + 1) : Int) = (v : Int) + 1 by
              omega)
        have hvTwo : positiveIndex canonicalExpansion (q + 2) = v + 2 := by
          dsimp [tail, v, B] at hcoords hvalueTwo
          exact_mod_cast (show
            (positiveIndex canonicalExpansion (q + 2) : Int) = (v : Int) + 2 by
              omega)
        have hboundsTwo :=
          (positiveCoordinate_fiber_small tail B hformula htailPos hsmall
            (v + 2)).mp (by simpa [hvTwo] using hcoordTwo)
        dsimp [start]
        omega
  dsimp [tail, v, B, start] at hcoords hvStart ⊢
  simp only [trace, fiberStartInt] at hvStart ⊢
  omega

private theorem natLift_eq_zero_of_negative
    (digits : D5.S1.Digit.RawDigits) {i : Int} (hi : i < 0) :
    natLift digits i = 0 := by
  rw [natLift, Finsupp.embDomain_apply]
  split
  · rename_i h
    obtain ⟨j, hj⟩ := h
    change (j : Int) = i at hj
    have : (0 : Int) ≤ (j : Int) := by positivity
    omega
  · rfl

private noncomputable def glueTail (digits : Int →₀ Nat) (v : Nat) : Int →₀ Nat :=
  digits + natLift (D5.S1.Digit.toRaw (D5.S1.Digit.Z v))

private theorem glueTail_binary {digits : Int →₀ Nat} {v : Nat}
    (hnegative : ∀ i : Int, 0 ≤ i → digits i = 0)
    (hbinary : ∀ i : Int, digits i ≤ 1) :
    ∀ i : Int, glueTail digits v i ≤ 1 := by
  intro i
  by_cases hi : i < 0
  · rw [glueTail, Finsupp.add_apply,
      natLift_eq_zero_of_negative _ hi, add_zero]
    exact hbinary i
  · have hiNonnegative : 0 ≤ i := le_of_not_gt hi
    have hcast : (i.toNat : Int) = i := Int.toNat_of_nonneg hiNonnegative
    rw [glueTail, Finsupp.add_apply, hnegative i hiNonnegative, zero_add, ← hcast,
      natLift_apply]
    exact (D5.S1.Digit.canonicalRaw_toRaw (D5.S1.Digit.Z v)).1 i.toNat

private theorem glueTail_canonical {digits : Int →₀ Nat} {v : Nat}
    (hnegative : ∀ i : Int, 0 ≤ i → digits i = 0)
    (hcanonical : ∀ i : Int, digits i = 1 → digits (i + 1) = 0)
    (hboundary : digits (-1) = 1 →
      D5.S1.Digit.toRaw (D5.S1.Digit.Z v) 0 = 0) :
    ∀ i : Int, glueTail digits v i = 1 →
      glueTail digits v (i + 1) = 0 := by
  intro i hone
  by_cases hi : i < 0
  · have hiDigit : digits i = 1 := by
      simpa [glueTail, Finsupp.add_apply,
        natLift_eq_zero_of_negative _ hi] using hone
    by_cases hnext : i + 1 < 0
    · rw [glueTail, Finsupp.add_apply,
        natLift_eq_zero_of_negative _ hnext, add_zero]
      exact hcanonical i hiDigit
    · have hiNegOne : i = -1 := by omega
      subst i
      norm_num [glueTail, Finsupp.add_apply, hnegative 0 (by omega)]
      change natLift (D5.S1.Digit.toRaw (D5.S1.Digit.Z v)) 0 = 0
      exact (natLift_apply (D5.S1.Digit.toRaw (D5.S1.Digit.Z v)) 0).trans
        (hboundary hiDigit)
  · have hiNonnegative : 0 ≤ i := le_of_not_gt hi
    have hcast : (i.toNat : Int) = i := Int.toNat_of_nonneg hiNonnegative
    have hnextCast : ((i.toNat + 1 : Nat) : Int) = i + 1 := by
      rw [Nat.cast_add, Nat.cast_one, hcast]
    rw [glueTail, Finsupp.add_apply, hnegative (i + 1) (by omega), zero_add,
      ← hnextCast, natLift_apply]
    apply (D5.S1.Digit.canonicalRaw_toRaw (D5.S1.Digit.Z v)).2 i.toNat
    rw [glueTail, Finsupp.add_apply, hnegative i hiNonnegative, zero_add,
      ← hcast, natLift_apply] at hone
    exact hone

private theorem negativePart_glueTail {digits : Int →₀ Nat} {v : Nat} :
    ∀ i : Int, i < 0 → glueTail digits v i = digits i := by
  intro i hi
  simp [glueTail, Finsupp.add_apply, natLift_eq_zero_of_negative _ hi]

theorem fiberStart_of_complete_tail
    (digits : Int →₀ Nat)
    (hnegative : ∀ i : Int, 0 ≤ i → digits i = 0)
    (hbinary : ∀ i : Int, digits i ≤ 1)
    (hcanonical : ∀ i : Int, digits i = 1 → digits (i + 1) = 0)
    (htailPos : 0 < embedding (basePhiValue digits))
    (htailLtOne : embedding (basePhiValue digits) < 1)
    (hcutOne : digits (-1) = 1 →
      Real.goldenRatio⁻¹ ≤ embedding (basePhiValue digits))
    (hcutZero : digits (-1) = 0 →
      embedding (basePhiValue digits) < Real.goldenRatio⁻¹)
    (htrace : 1 < trace (basePhiValue digits)) :
    let q := (trace (basePhiValue digits) - 1).toNat
    fiberStart q ∧
      basePhiValue (negativePart canonicalExpansion q) = basePhiValue digits := by
  let tail := basePhiValue digits
  let B := -tail.b
  let start := fiberStartInt tail B
  let q := (trace tail - 1).toNat
  change 0 < embedding tail at htailPos
  change embedding tail < 1 at htailLtOne
  change 1 < trace tail at htrace
  have htracePos : 0 < trace tail - 1 := by omega
  have hqCast : (q : Int) = trace tail - 1 := by
    exact Int.toNat_of_nonneg htracePos.le
  have hBpositive : 0 < B := by
    by_contra hnot
    have hbNonnegative : 0 ≤ tail.b := by dsimp [B] at hnot; omega
    have hab : 1 ≤ tail.a + tail.b := by
      simp only [trace] at htrace
      omega
    have habReal : (1 : Real) ≤ tail.a + tail.b := by exact_mod_cast hab
    have hbReal : (0 : Real) ≤ tail.b := by exact_mod_cast hbNonnegative
    rw [embedding_apply] at htailLtOne
    nlinarith [Real.one_lt_goldenRatio]
  have hformula : embedding tail = (tail.a : Real) - (B : Real) * Real.goldenRatio := by
    dsimp [B]
    push_cast
    ring
  have haLarge : B + 1 ≤ tail.a := by
    have hBReal : (0 : Real) < B := by exact_mod_cast hBpositive
    have hpositive := htailPos
    rw [hformula] at hpositive
    have hstrict : (B : Real) < (tail.a : Real) := by
      nlinarith [Real.one_lt_goldenRatio]
    exact_mod_cast hstrict
  have hstartNonnegative : 0 ≤ start := by
    dsimp [start, fiberStartInt]
    omega
  let v := start.toNat
  have hvCast : (v : Int) = start := Int.toNat_of_nonneg hstartNonnegative
  have hcoordinate : positiveCoordinate v = B := by
    by_cases hone : digits (-1) = 1
    · apply (positiveCoordinate_fiber_large tail B hformula
        (hcutOne hone) htailLtOne v).mpr
      rw [hvCast]
      constructor <;> omega
    · have hzero : digits (-1) = 0 := by
        have := hbinary (-1)
        omega
      apply (positiveCoordinate_fiber_small tail B hformula htailPos
        (hcutZero hzero) v).mpr
      rw [hvCast]
      constructor <;> omega
  have hboundary : digits (-1) = 1 →
      D5.S1.Digit.toRaw (D5.S1.Digit.Z v) 0 = 0 := by
    intro hone
    have hcoordinateSucc : positiveCoordinate (v + 1) = B := by
      apply (positiveCoordinate_fiber_large tail B hformula
        (hcutOne hone) htailLtOne (v + 1)).mpr
      push_cast
      rw [hvCast]
      constructor <;> omega
    apply (canonical_zero_digit_iff_coordinate_succ
      (D5.S1.Digit.canonicalRaw_toRaw (D5.S1.Digit.Z v))).mpr
    simpa only [D5.S1.Digit.rawValue_toRaw_Z] using
      hcoordinateSucc.trans hcoordinate.symm
  let candidate := glueTail digits v
  have hcandidateBinary : ∀ i : Int, candidate i ≤ 1 :=
    glueTail_binary hnegative hbinary
  have hcandidateCanonical : ∀ i : Int, candidate i = 1 →
      candidate (i + 1) = 0 :=
    glueTail_canonical hnegative hcanonical hboundary
  have hpositiveCoordinates := positive_value_coordinates v
  have hcandidateValue : basePhiValue candidate = (q : GoldenInt) := by
    rw [show candidate = glueTail digits v by rfl, glueTail, basePhiValue_add]
    apply GoldenInt.ext
    · rw [a_add]
      change tail.a + (basePhiValue
        (natLift (D5.S1.Digit.toRaw (D5.S1.Digit.Z v)))).a = (q : Int)
      rw [hpositiveCoordinates.1, hcoordinate, hvCast, hqCast]
      simp only [start, fiberStartInt, trace]
      dsimp [B]
      ring
    · rw [b_add]
      change tail.b + (basePhiValue
        (natLift (D5.S1.Digit.toRaw (D5.S1.Digit.Z v)))).b = 0
      rw [hpositiveCoordinates.2, hcoordinate]
      dsimp [B]
      ring
  have hcanonicalDigits : canonicalExpansion.digit q = candidate := by
    apply bilateral_basePhi_injective
      (canonicalExpansion.binary q) (canonicalExpansion.canonical q)
      hcandidateBinary hcandidateCanonical
    rw [canonicalExpansion.value_equation q, hcandidateValue]
  have hqIndex : positiveIndex canonicalExpansion q = v := by
    rw [positiveIndex]
    have hnonnegative : nonnegativeDigits canonicalExpansion q =
        D5.S1.Digit.toRaw (D5.S1.Digit.Z v) := by
      apply Finsupp.ext
      intro k
      rw [nonnegativeDigits_apply, hcanonicalDigits]
      simp [candidate, glueTail, Finsupp.add_apply,
        hnegative (k : Int) (by positivity), natLift_apply]
    rw [hnonnegative, D5.S1.Digit.rawValue_toRaw_Z]
  have htailValue :
      basePhiValue (negativePart canonicalExpansion q) = tail := by
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
      have hcast : ((-i).toNat : Int) = -i :=
        Int.toNat_of_nonneg (by omega)
      have hk : k + 1 = (-i).toNat := Nat.sub_add_cancel (by omega)
      have hindex : -((k + 1 : Nat) : Int) = i := by
        rw [hk, hcast]
        omega
      rw [← hindex, negativePart_apply, hcanonicalDigits]
      exact negativePart_glueTail _ (by omega)
    · rw [negativePart_eq_zero_of_nonnegative canonicalExpansion q
          (le_of_not_gt hi), hnegative i (le_of_not_gt hi)]
  have hqPositive : 0 < q := by
    have : (0 : Int) < (q : Int) := by rw [hqCast]; exact htracePos
    exact_mod_cast this
  have hqSame : SameNegativeTail q q := fun _ => rfl
  have hqStart : fiberStart q := by
    refine ⟨⟨hqPositive, hqSame⟩, ?_⟩
    intro M hM
    have hqcoords := tail_coordinates q
    have htailA := congrArg GoldenInt.a htailValue
    have htailB := congrArg GoldenInt.b htailValue
    have hqCoordinate : positiveCoordinate (positiveIndex canonicalExpansion q) = B := by
      dsimp [tail, B] at hqcoords htailA htailB ⊢
      omega
    have hMdata := same_tail_coordinates hM.2
    have hMCoordinate : positiveCoordinate (positiveIndex canonicalExpansion M) = B := by
      exact hMdata.1.trans hqCoordinate
    have hMlower : start ≤ (positiveIndex canonicalExpansion M : Int) := by
      by_cases hone : digits (-1) = 1
      · exact ((positiveCoordinate_fiber_large tail B hformula
          (hcutOne hone) htailLtOne _).mp hMCoordinate).1
      · have hzero : digits (-1) = 0 := by
          have := hbinary (-1)
          omega
        exact ((positiveCoordinate_fiber_small tail B hformula htailPos
          (hcutZero hzero) _).mp hMCoordinate).1
    have hMvalue := hMdata.2
    dsimp [tail, B, start] at hMvalue hMlower hvCast hqCast hqIndex htailA
    simp only [fiberStartInt] at hvCast hMlower
    rw [hqIndex] at hqCoordinate
    dsimp [B] at hqCoordinate
    simp only [trace] at hqCast
    have htailA' :
        (basePhiValue (negativePart canonicalExpansion q)).a = tail.a := htailA
    rw [htailA'] at hMvalue
    omega
  exact ⟨hqStart, by simpa [q, tail] using htailValue⟩

end

end D5.X_Frontier.BasePhiNegativePrefixTrident
