/- GID: D5/S1/Words/Expansions/BasePhiTailFiber
   generality: I
   mirror-B: D5/B/S1/Words/Expansions/BasePhiTailFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Negative base-phi tails have singleton or three-consecutive positive-integer fibers. -/

import D5.S1.Words.Expansions.BasePhiRecursiveStructure

namespace D5.S1.Words.Expansions.BasePhiTailFiber

open D5.S0.Carrier
open D5.S0.Conventions
open D5.S1.Digit
open D5.S1.Scale
open D5.S1.Words
open D5.S1.Words.Expansions.BasePhiCanonicalExpansion
open D5.S1.Words.Expansions.BasePhiCarryTransducer
open D5.S1.Words.Expansions.BasePhiNegative
open D5.S1.Words.Expansions.BasePhiRecursiveStructure
open D5.S1.Words.Expansions.BasePhiTailBounds

noncomputable section

local instance (priority := low) (p : Prop) : Decidable p :=
  Classical.propDecidable p

private theorem natLift_eq_zero_of_negative
    (digits : RawDigits) {i : Int} (hi : i < 0) : natLift digits i = 0 := by
  rw [natLift, Finsupp.embDomain_apply]
  split
  · rename_i h
    obtain ⟨j, hj⟩ := h
    change (j : Int) = i at hj
    have : (0 : Int) ≤ (j : Int) := by positivity
    omega
  · rfl

private noncomputable def gluedDigits
    (expansion : BasePhiNegativeExpansion) (N v : Nat) : Int →₀ Nat :=
  negativePart expansion N + natLift (toRaw (Z v))

private theorem gluedDigits_eq_negativePart_of_negative
    (expansion : BasePhiNegativeExpansion) (N v : Nat) {i : Int}
    (hi : i < 0) : gluedDigits expansion N v i = negativePart expansion N i := by
  rw [gluedDigits, Finsupp.add_apply,
    natLift_eq_zero_of_negative (toRaw (Z v)) hi, add_zero]

private theorem gluedDigits_apply_nonnegative
    (expansion : BasePhiNegativeExpansion) (N v k : Nat) :
    gluedDigits expansion N v (k : Int) = toRaw (Z v) k := by
  rw [gluedDigits, Finsupp.add_apply,
    negativePart_eq_zero_of_nonnegative expansion N (by positivity),
    natLift_apply, zero_add]

private theorem gluedDigits_binary
    (expansion : BasePhiNegativeExpansion) (N v : Nat) :
    ∀ i : Int, gluedDigits expansion N v i ≤ 1 := by
  intro i
  by_cases hi : i < 0
  · rw [gluedDigits_eq_negativePart_of_negative expansion N v hi]
    exact negativePart_binary expansion N i
  · have hcast : (i.toNat : Int) = i := Int.toNat_of_nonneg (le_of_not_gt hi)
    rw [← hcast, gluedDigits_apply_nonnegative]
    exact (canonicalRaw_toRaw (Z v)).1 i.toNat

private theorem gluedDigits_canonical_of_first_negative_zero
    (expansion : BasePhiNegativeExpansion) (N v : Nat)
    (hzero : negativeDigit expansion N 0 = false) :
    ∀ i : Int, gluedDigits expansion N v i = 1 →
      gluedDigits expansion N v (i + 1) = 0 := by
  intro i hone
  by_cases hi : i < 0
  · have hnegative : negativePart expansion N i = 1 := by
      simpa [gluedDigits_eq_negativePart_of_negative expansion N v hi] using hone
    by_cases hnext : i + 1 < 0
    · rw [gluedDigits_eq_negativePart_of_negative expansion N v hnext]
      exact negativePart_canonical expansion N i hnegative
    · have hiNegOne : i = -1 := by omega
      have hdigit : expansion.digit N (-1) = 1 := by
        have happly := negativePart_apply expansion N 0
        rw [hiNegOne] at hnegative
        norm_num at happly
        exact happly.symm.trans hnegative
      have : negativeDigit expansion N 0 = true := by
        simp [negativeDigit, hdigit]
      rw [hzero] at this
      contradiction
  · have hnonnegative : 0 ≤ i := le_of_not_gt hi
    have hcast : (i.toNat : Int) = i := Int.toNat_of_nonneg hnonnegative
    have hnextCast : ((i.toNat + 1 : Nat) : Int) = i + 1 := by
      rw [Nat.cast_add, Nat.cast_one, hcast]
    rw [← hnextCast, gluedDigits_apply_nonnegative]
    apply (canonicalRaw_toRaw (Z v)).2 i.toNat
    rw [← hcast, gluedDigits_apply_nonnegative] at hone
    exact hone

private theorem embedding_basePhiValue_nonnegative (digits : Int →₀ Nat) :
    0 ≤ embedding (basePhiValue digits) := by
  have hunit : ∀ i : Int,
      embedding (((phiUnit ^ i : GoldenIntˣ) : GoldenInt)) =
        Real.goldenRatio ^ i := by
    intro i
    simpa [phiUnitZPowMul] using
      (embedding_phiUnitZPowMul i (1 : GoldenInt))
  rw [basePhiValue, map_sum]
  apply Finset.sum_nonneg
  intro i hi
  rw [map_mul, hunit, map_natCast]
  exact mul_nonneg (by positivity) (le_of_lt (zpow_pos Real.goldenRatio_pos i))

private theorem gluedDigits_value
    (expansion : BasePhiNegativeExpansion) (N v : Nat) :
    basePhiValue (gluedDigits expansion N v) =
      basePhiValue (negativePart expansion N) +
        basePhiValue (natLift (toRaw (Z v))) := by
  rw [gluedDigits, basePhiValue_add]

private theorem tail_value_coordinates
    (expansion : BasePhiNegativeExpansion) (N : Nat) :
    let tail := basePhiValue (negativePart expansion N)
    let v := positiveIndex expansion N
    let B := positiveCoordinate v
    tail.b = -B ∧
      (N : Int) = tail.a + (v : Int) - 2 * B := by
  let tail := basePhiValue (negativePart expansion N)
  let v := positiveIndex expansion N
  let B := positiveCoordinate v
  have hsum := negativeValue_add_positiveValue expansion N
  have hpositive := positiveValue_coordinates expansion N
  have hb := congrArg GoldenInt.b hsum
  have ha := congrArg GoldenInt.a hsum
  dsimp [tail, v, B] at hpositive hb ha ⊢
  constructor
  · omega
  · omega

private theorem tail_embedding_formula
    (expansion : BasePhiNegativeExpansion) (N : Nat) :
    let tail := basePhiValue (negativePart expansion N)
    let B := positiveCoordinate (positiveIndex expansion N)
    embedding tail = (tail.a : Real) - (B : Real) * Real.goldenRatio := by
  have hb := (tail_value_coordinates expansion N).1
  dsimp at hb ⊢
  rw [hb]
  push_cast
  ring

private theorem tail_parameter_bounds
    (expansion : BasePhiNegativeExpansion) (N : Nat)
    (hreaches : ∃ depth, reachesNegativeDepth expansion N depth) :
    let tail := basePhiValue (negativePart expansion N)
    let v := positiveIndex expansion N
    let B := positiveCoordinate v
    0 < B ∧ 0 ≤ fiberStartInt tail B ∧
      0 < embedding tail ∧ embedding tail < 1 := by
  let tail := basePhiValue (negativePart expansion N)
  let v := positiveIndex expansion N
  let B := positiveCoordinate v
  have hreal := negative_tail_real_bounds expansion N hreaches
  have hembedding := embedding_basePhiValue_negativePart expansion N
  have htailPos : 0 < embedding tail := by
    simpa [tail, hembedding] using hreal.1
  have htailLtOne : embedding tail < 1 := by
    simpa [tail, hembedding] using hreal.2.1
  have hBnonnegative : 0 ≤ B := by
    dsimp [B, v, positiveCoordinate]
    apply Int.floor_nonneg.mpr
    positivity
  have htailB : tail.b = -B := by
    simpa [tail, v, B] using (tail_value_coordinates expansion N).1
  have hBpositive : 0 < B := by
    by_contra hnot
    have hBzero : B = 0 := by omega
    have htailBzero : tail.b = 0 := by omega
    have haPosReal : (0 : Real) < tail.a := by
      simpa [embedding_apply, htailBzero] using htailPos
    have haLtOneReal : (tail.a : Real) < 1 := by
      simpa [embedding_apply, htailBzero] using htailLtOne
    have haPos : 0 < tail.a := by exact_mod_cast haPosReal
    have haLtOne : tail.a < 1 := by exact_mod_cast haLtOneReal
    omega
  have haPosReal : (0 : Real) < tail.a := by
    have hformula : embedding tail =
        (tail.a : Real) - (B : Real) * Real.goldenRatio := by
      simpa [tail, v, B] using tail_embedding_formula expansion N
    rw [hformula] at htailPos
    have hBReal : (0 : Real) < B := by exact_mod_cast hBpositive
    nlinarith [Real.goldenRatio_pos]
  have haPos : 0 < tail.a := by exact_mod_cast haPosReal
  have hstart : 0 ≤ fiberStartInt tail B := by
    rw [fiberStartInt]
    omega
  exact ⟨hBpositive, hstart, htailPos, htailLtOne⟩

private theorem gluedDigits_realizes_small_coordinate
    (expansion : BasePhiNegativeExpansion) (N v : Nat)
    (hreaches : ∃ depth, reachesNegativeDepth expansion N depth)
    (hzero : negativeDigit expansion N 0 = false)
    (hcoordinate : positiveCoordinate v =
      positiveCoordinate (positiveIndex expansion N)) :
    ∃ M : Nat,
      0 < M ∧ SameNegativeTail expansion M N ∧
        positiveIndex expansion M = v ∧
        (M : Int) =
          (basePhiValue (negativePart expansion N)).a + (v : Int) -
            2 * positiveCoordinate (positiveIndex expansion N) := by
  let tail := basePhiValue (negativePart expansion N)
  let B := positiveCoordinate (positiveIndex expansion N)
  let candidate := gluedDigits expansion N v
  let value := basePhiValue candidate
  have htailPos := (tail_parameter_bounds expansion N hreaches).2.2.1
  have htailB : tail.b = -B := by
    simpa [tail, B] using (tail_value_coordinates expansion N).1
  have hpositive := positive_value_coordinates v
  dsimp at hpositive
  have hsplit : value = tail + basePhiValue (natLift (toRaw (Z v))) := by
    simpa [value, candidate, tail] using gluedDigits_value expansion N v
  have hvalueA : value.a = tail.a + (v : Int) - 2 * B := by
    rw [hsplit, a_add, hpositive.1, hcoordinate]
    ring
  have hvalueB : value.b = 0 := by
    rw [hsplit, b_add, htailB, hpositive.2, hcoordinate]
    omega
  have hvaluePos : 0 < embedding value := by
    rw [hsplit, map_add]
    exact add_pos_of_pos_of_nonneg htailPos
      (embedding_basePhiValue_nonnegative (natLift (toRaw (Z v))))
  have hvalueAPosReal : (0 : Real) < value.a := by
    simpa [embedding_apply, hvalueB] using hvaluePos
  have hvalueAPos : 0 < value.a := by exact_mod_cast hvalueAPosReal
  let M := value.a.toNat
  have hMcast : (M : Int) = value.a := by
    exact Int.toNat_of_nonneg hvalueAPos.le
  have hMpositive : 0 < M := by
    have hMpositiveInt : (0 : Int) < (M : Int) := by
      rw [hMcast]
      exact hvalueAPos
    exact_mod_cast hMpositiveInt
  have hvalueNat : value = (M : GoldenInt) := by
    apply GoldenInt.ext
    · exact hMcast.symm
    · simpa using hvalueB
  obtain ⟨chosen, _, hunique⟩ := basePhiExpansion_existsUnique M
  have hactual : expansion.digit M = chosen :=
    hunique (expansion.digit M)
      ⟨expansion.binary M, expansion.canonical M,
        expansion.value_equation M⟩
  have hcandidate : candidate = chosen :=
    hunique candidate
      ⟨gluedDigits_binary expansion N v,
        gluedDigits_canonical_of_first_negative_zero expansion N v hzero,
        by
          dsimp [value] at hvalueNat
          exact hvalueNat⟩
  have hdigit : expansion.digit M = candidate := hactual.trans hcandidate.symm
  have htail : SameNegativeTail expansion M N := by
    intro i
    unfold negativeDigit
    rw [hdigit]
    have hi : -((i + 1 : Nat) : Int) < 0 := by omega
    rw [gluedDigits_eq_negativePart_of_negative expansion N v hi,
      negativePart_apply]
  have hnonnegative : nonnegativeDigits expansion M = toRaw (Z v) := by
    apply Finsupp.ext
    intro k
    rw [nonnegativeDigits_apply, hdigit, gluedDigits_apply_nonnegative]
  have hindex : positiveIndex expansion M = v := by
    rw [positiveIndex, hnonnegative, rawValue_toRaw_Z]
  refine ⟨M, hMpositive, htail, hindex, ?_⟩
  rw [hMcast, hvalueA]

private theorem same_tail_coordinate_and_value
    (expansion : BasePhiNegativeExpansion) (M N : Nat)
    (hsame : SameNegativeTail expansion M N) :
    let tail := basePhiValue (negativePart expansion N)
    let B := positiveCoordinate (positiveIndex expansion N)
    positiveCoordinate (positiveIndex expansion M) = B ∧
      (M : Int) = tail.a + (positiveIndex expansion M : Int) - 2 * B := by
  have htailEq :=
    (sameNegativeTail_iff_negativeValue_eq expansion M N).mp hsame
  have hM := tail_value_coordinates expansion M
  have hN := tail_value_coordinates expansion N
  dsimp at htailEq hM hN ⊢
  have haEq := congrArg GoldenInt.a htailEq
  have hbEq := congrArg GoldenInt.b htailEq
  constructor <;> omega

private theorem positiveIndex_eq_start_of_first_negative_one
    (expansion : BasePhiNegativeExpansion) (M N : Nat)
    (hreaches : ∃ depth, reachesNegativeDepth expansion N depth)
    (hsame : SameNegativeTail expansion M N)
    (hone : negativeDigit expansion N 0 = true) :
    (positiveIndex expansion M : Int) =
      fiberStartInt (basePhiValue (negativePart expansion N))
        (positiveCoordinate (positiveIndex expansion N)) := by
  let tail := basePhiValue (negativePart expansion N)
  let B := positiveCoordinate (positiveIndex expansion N)
  let start := fiberStartInt tail B
  have hparameters := tail_parameter_bounds expansion N hreaches
  have hformula : embedding tail =
      (tail.a : Real) - (B : Real) * Real.goldenRatio := by
    simpa [tail, B] using tail_embedding_formula expansion N
  have hlarge : Real.goldenRatio⁻¹ ≤ embedding tail := by
    have hreal := negative_tail_real_bounds expansion N hreaches
    have := hreal.2.2.1 hone
    simpa [tail, embedding_basePhiValue_negativePart expansion N] using this
  have hltOne : embedding tail < 1 := by
    simpa [tail, B] using hparameters.2.2.2
  have hcoordinate := (same_tail_coordinate_and_value expansion M N hsame).1
  have hbounds :=
    (positiveCoordinate_fiber_large tail B hformula hlarge hltOne
      (positiveIndex expansion M)).mp hcoordinate
  have hMone : negativeDigit expansion M 0 = true :=
    (hsame 0).trans hone
  have hMnegOne : expansion.digit M (-1) = 1 :=
    of_decide_eq_true hMone
  have hMzero := expansion.canonical M (-1) hMnegOne
  norm_num at hMzero
  have hrawZero : nonnegativeDigits expansion M 0 = 0 := by
    simpa [nonnegativeDigits_apply] using hMzero
  have hcoordinateSucc :
      positiveCoordinate (positiveIndex expansion M + 1) = B := by
    have hsucc := (canonical_zero_digit_iff_coordinate_succ
      (nonnegativeDigits_canonical expansion M)).mp hrawZero
    exact hsucc.trans hcoordinate
  have hboundsSucc :=
    (positiveCoordinate_fiber_large tail B hformula hlarge hltOne
      (positiveIndex expansion M + 1)).mp hcoordinateSucc
  change (positiveIndex expansion M : Int) = start
  omega

/-- Complete negative tails of positive natural base-phi expansions are exactly
singletons when `d_-1 = 1`, and exactly three consecutive inputs when
`d_-1 = 0`. This is the cropped singleton/trident consequence of Dekking's
recursive structure theorem. -/
theorem negative_tail_fiber_shape
    (expansion : BasePhiNegativeExpansion) (N : Nat)
    (hpositive : 0 < N)
    (hreaches : ∃ depth, reachesNegativeDepth expansion N depth) :
    (negativeDigit expansion N 0 = true →
      negativeTailFiber expansion N = ({N} : Set Nat)) ∧
    (negativeDigit expansion N 0 = false →
      ∃! q : Nat, q ≤ N ∧ N ≤ q + 2 ∧
        negativeTailFiber expansion N =
          {M | M = q ∨ M = q + 1 ∨ M = q + 2}) := by
  constructor
  · intro hone
    apply Set.ext
    intro M
    constructor
    · rintro ⟨hMpositive, hsame⟩
      have hMindex := positiveIndex_eq_start_of_first_negative_one
        expansion M N hreaches hsame hone
      have hNindex := positiveIndex_eq_start_of_first_negative_one
        expansion N N hreaches (fun _ => rfl) hone
      have hMvalue := (same_tail_coordinate_and_value expansion M N hsame).2
      have hNvalue :=
        (same_tail_coordinate_and_value expansion N N (fun _ => rfl)).2
      have : M = N := by
        exact_mod_cast (show (M : Int) = (N : Int) by omega)
      simpa only [Set.mem_singleton_iff] using this
    · intro hM
      have hMN : M = N := by
        simpa only [Set.mem_singleton_iff] using hM
      subst M
      exact ⟨hpositive, fun _ => rfl⟩
  · intro hzero
    let tail := basePhiValue (negativePart expansion N)
    let B := positiveCoordinate (positiveIndex expansion N)
    let start := fiberStartInt tail B
    have hparameters := tail_parameter_bounds expansion N hreaches
    have hstartNonnegative : 0 ≤ start := by
      simpa [tail, B, start] using hparameters.2.1
    let startNat := start.toNat
    have hstartCast : (startNat : Int) = start := by
      exact Int.toNat_of_nonneg hstartNonnegative
    have hformula : embedding tail =
        (tail.a : Real) - (B : Real) * Real.goldenRatio := by
      simpa [tail, B] using tail_embedding_formula expansion N
    have htailPos : 0 < embedding tail := by
      simpa [tail, B] using hparameters.2.2.1
    have hsmall : embedding tail < Real.goldenRatio⁻¹ := by
      have hreal := negative_tail_real_bounds expansion N hreaches
      have := hreal.2.2.2 hzero
      simpa [tail, embedding_basePhiValue_negativePart expansion N] using this
    have hcoordinate0 : positiveCoordinate startNat = B := by
      apply (positiveCoordinate_fiber_small tail B hformula htailPos hsmall
        startNat).mpr
      constructor <;> omega
    have hcoordinate1 : positiveCoordinate (startNat + 1) = B := by
      apply (positiveCoordinate_fiber_small tail B hformula htailPos hsmall
        (startNat + 1)).mpr
      constructor <;> push_cast <;> omega
    have hcoordinate2 : positiveCoordinate (startNat + 2) = B := by
      apply (positiveCoordinate_fiber_small tail B hformula htailPos hsmall
        (startNat + 2)).mpr
      constructor <;> push_cast <;> omega
    obtain ⟨M0, hM0positive, hM0tail, hM0index, hM0value⟩ :=
      gluedDigits_realizes_small_coordinate expansion N startNat hreaches hzero
        (by simpa [B] using hcoordinate0)
    obtain ⟨M1, hM1positive, hM1tail, hM1index, hM1value⟩ :=
      gluedDigits_realizes_small_coordinate expansion N (startNat + 1)
        hreaches hzero (by simpa [B] using hcoordinate1)
    obtain ⟨M2, hM2positive, hM2tail, hM2index, hM2value⟩ :=
      gluedDigits_realizes_small_coordinate expansion N (startNat + 2)
        hreaches hzero (by simpa [B] using hcoordinate2)
    have hM1eq : M1 = M0 + 1 := by
      exact_mod_cast (show (M1 : Int) = (M0 : Int) + 1 by
        dsimp [tail, B] at hM0value hM1value
        omega)
    have hM2eq : M2 = M0 + 2 := by
      exact_mod_cast (show (M2 : Int) = (M0 : Int) + 2 by
        dsimp [tail, B] at hM0value hM2value
        omega)
    have hfiber : negativeTailFiber expansion N =
        {M | M = M0 ∨ M = M0 + 1 ∨ M = M0 + 2} := by
      apply Set.ext
      intro M
      constructor
      · rintro ⟨hMpositive, hsame⟩
        have hdata := same_tail_coordinate_and_value expansion M N hsame
        have hbounds :=
          (positiveCoordinate_fiber_small tail B hformula htailPos hsmall
            (positiveIndex expansion M)).mp (by simpa [B] using hdata.1)
        have hindexCases :
            positiveIndex expansion M = startNat ∨
              positiveIndex expansion M = startNat + 1 ∨
              positiveIndex expansion M = startNat + 2 := by
          omega
        dsimp [tail, B] at hdata
        rcases hindexCases with hindex | hindex | hindex
        · left
          exact_mod_cast (show (M : Int) = (M0 : Int) by
            have hMvalue := hdata.2
            rw [hindex] at hMvalue
            omega)
        · right; left
          rw [← hM1eq]
          exact_mod_cast (show (M : Int) = (M1 : Int) by
            have hMvalue := hdata.2
            rw [hindex] at hMvalue
            omega)
        · right; right
          rw [← hM2eq]
          exact_mod_cast (show (M : Int) = (M2 : Int) by
            have hMvalue := hdata.2
            rw [hindex] at hMvalue
            omega)
      · rintro (rfl | hM | hM)
        · exact ⟨hM0positive, hM0tail⟩
        · rw [← hM1eq] at hM
          subst M
          exact ⟨hM1positive, hM1tail⟩
        · rw [← hM2eq] at hM
          subst M
          exact ⟨hM2positive, hM2tail⟩
    have hNmem : N ∈ negativeTailFiber expansion N :=
      ⟨hpositive, fun _ => rfl⟩
    rw [hfiber] at hNmem
    change N = M0 ∨ N = M0 + 1 ∨ N = M0 + 2 at hNmem
    refine ⟨M0, ⟨?_, ?_, hfiber⟩, ?_⟩
    · omega
    · omega
    · intro q hq
      have hM0mem : M0 ∈ negativeTailFiber expansion N :=
        ⟨hM0positive, hM0tail⟩
      rw [hq.2.2] at hM0mem
      change M0 = q ∨ M0 = q + 1 ∨ M0 = q + 2 at hM0mem
      have hqmem : q ∈ negativeTailFiber expansion N := by
        rw [hq.2.2]
        simp
      rw [hfiber] at hqmem
      change q = M0 ∨ q = M0 + 1 ∨ q = M0 + 2 at hqmem
      omega

end

end D5.S1.Words.Expansions.BasePhiTailFiber
