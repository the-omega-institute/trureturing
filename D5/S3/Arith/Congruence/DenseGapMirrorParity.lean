/- GID: D5/S3/Arith/Congruence/DenseGapMirrorParity
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/DenseGapMirrorParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Point-count parity controls reflection of alternating finite gap codes. -/

import D5.S3.Arith.Congruence.EvenDenseConstellationMirrorCode
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Dense gap mirror parity

A dense admissible configuration has a Boolean gap code whose adjacent bits
alternate. Reversing that source code preserves it when the configuration has
an even number of points and complements it when the point count is odd.
-/

/- Search and duplication audit (2026-09-03):
   * D5 searches for normalized gap bits, alternating configuration codes,
     reverse-complement parity, and constellation mirror laws found no
     whole-statement owner. `EvenDenseConstellationMirrorCode` owns the even
     child clause on lists and is applied below after a carrier-preserving
     conversion; existing golden-word modules concern different source families.
   * Body-shape searches for the odd reverse-complement law, `Fin.induction`
     with parity, and `Fin.rev` with `Nat.even_sub` found no D5 or pinned-Mathlib
     owner for the remaining private finite-index argument.
   * Pinned Mathlib supplies `Bool.not_eq`, `Nat.even_sub`, `Fin.rev`,
     `List.isChain_iff_getElem`, and `List.getElem_reverse`; each is applied
     below. Its Boolean-count module has no mirror-parity theorem.
   * GitHub Lean-code searches for alternating Boolean reverse parity,
     complementary mirror codes, and prime-constellation gap codes found no
     exact theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.DenseGapMirrorParity

open D5.S3.Arith.Congruence.EvenDenseConstellationMirrorCode

private theorem alternating_value
    {n : Nat} (gapCode : Fin (n + 1) -> Bool)
    (alternating : forall i : Fin n,
      Not (gapCode i.castSucc = gapCode i.succ)) (i : Fin (n + 1)) :
    gapCode i = if Even i.val then gapCode 0 else !gapCode 0 := by
  refine Fin.induction ?_ ?_ i
  · simp
  · intro j ih
    rw [← Bool.not_eq.mpr (alternating j), ih]
    rcases Nat.even_or_odd j.val with heven | hodd
    · simp [Fin.succ, heven]
    · have hnotEven : Not (Even j.val) := by
        rintro ⟨evenHalf, hEven⟩
        rcases hodd with ⟨oddHalf, hOdd⟩
        omega
      simp [Fin.succ, hodd, hnotEven]

private theorem finite_alternating_reverse_complement_of_odd
    (extraPoints : Nat) (gapCode : Fin (extraPoints + 1) -> Bool)
    (alternating : forall i : Fin extraPoints,
      Not (gapCode i.castSucc = gapCode i.succ))
    (hPointOdd : Odd (extraPoints + 2)) :
    gapCode ∘ Fin.rev = fun i => !gapCode i := by
  have hCodeLengthOdd : Odd extraPoints := by
    rcases hPointOdd with ⟨half, hhalf⟩
    refine ⟨half - 1, ?_⟩
    omega
  have hCodeLengthNotEven : Not (Even extraPoints) := by
    rintro ⟨evenHalf, hEven⟩
    rcases hCodeLengthOdd with ⟨oddHalf, hOdd⟩
    omega
  funext i
  change gapCode (Fin.rev i) = !gapCode i
  rw [alternating_value gapCode alternating (Fin.rev i),
    alternating_value gapCode alternating i]
  have hi : i.val <= extraPoints := Nat.le_of_lt_succ i.isLt
  have hrev : (Fin.rev i).val = extraPoints - i.val := by
    simp only [Fin.rev]
    omega
  rw [hrev]
  by_cases hiEven : Even i.val <;>
    simp [Nat.even_sub hi, hCodeLengthNotEven, hiEven]

private theorem alternating_gap_reverse_complement_of_odd
    (pointCount : Nat) (gapCode : List Bool)
    (codeLength : gapCode.length + 1 = pointCount)
    (alternating : gapCode.IsChain fun left right => Not (left = right))
    (hPointOdd : Odd pointCount) :
    gapCode.reverse = gapCode.map fun bit => !bit := by
  cases gapCode with
  | nil =>
      simp
  | cons first rest =>
      have pointCountEq : pointCount = rest.length + 2 := by
        simp only [List.length_cons] at codeLength
        omega
      let indexedCode : Fin (rest.length + 1) -> Bool := fun i =>
        (first :: rest)[i.val]'(by simp only [List.length_cons]; exact i.isLt)
      have indexedAlternating : forall i : Fin rest.length,
          Not (indexedCode i.castSucc = indexedCode i.succ) := by
        intro i
        rw [List.isChain_iff_getElem] at alternating
        exact alternating i.val (by simp only [List.length_cons]; omega)
      rw [pointCountEq] at hPointOdd
      have indexedComplement := finite_alternating_reverse_complement_of_odd
        rest.length indexedCode indexedAlternating hPointOdd
      apply List.ext_getElem (by simp)
      intro i hReverse hMap
      rw [List.getElem_reverse, List.getElem_map]
      have hi : i < rest.length + 1 := by
        simpa only [List.length_map, List.length_cons] using hMap
      let index : Fin (rest.length + 1) := ⟨i, hi⟩
      have hAtIndex := congrFun indexedComplement index
      change indexedCode (Fin.rev index) = !indexedCode index at hAtIndex
      have hIndexEq : rest.length + 1 - (i + 1) = rest.length - i := by
        omega
      simpa only [indexedCode, index, Fin.rev, List.length_cons,
        Nat.add_sub_cancel_left, Nat.add_sub_cancel, hIndexEq] using hAtIndex

/-- Construct the normalized gap code from a dense integer configuration.
Mod-three admissibility forces its adjacent bits to alternate, after which
point-count parity determines how reflection acts on the entire code. -/
theorem dense_gap_mirror_parity
    (gapCount : Nat) (offset : Fin (gapCount + 1) -> Int)
    (denseGaps : forall i : Fin gapCount,
      offset i.succ - offset i.castSucc = 2 \/
        offset i.succ - offset i.castSucc = 4)
    (modThreeAdmissible : Not (Function.Surjective fun i =>
      (offset i : ZMod 3))) :
    let gapCode := List.ofFn fun i : Fin gapCount =>
      decide (offset i.succ - offset i.castSucc = 4)
    (Even (gapCount + 1) -> gapCode.reverse = gapCode) /\
      (Odd (gapCount + 1) ->
        gapCode.reverse = gapCode.map fun bit => !bit) := by
  let gapBit : Fin gapCount -> Bool := fun i =>
    decide (offset i.succ - offset i.castSucc = 4)
  have bitAlternating : (List.ofFn gapBit).IsChain fun left right =>
      Not (left = right) := by
    rw [List.isChain_iff_getElem]
    intro j hj
    simp only [List.length_ofFn] at hj
    simp only [List.getElem_ofFn]
    let firstGap : Fin gapCount := ⟨j, by omega⟩
    let secondGap : Fin gapCount := ⟨j + 1, by omega⟩
    change Not (gapBit firstGap = gapBit secondGap)
    intro hBits
    have hGapEq :
        offset firstGap.succ - offset firstGap.castSucc =
          offset secondGap.succ - offset secondGap.castSucc := by
      rcases denseGaps firstGap with hFirst | hFirst <;>
        rcases denseGaps secondGap with hSecond | hSecond
      · exact hFirst.trans hSecond.symm
      · simp [gapBit, hFirst, hSecond] at hBits
      · simp [gapBit, hFirst, hSecond] at hBits
      · exact hFirst.trans hSecond.symm
    apply modThreeAdmissible
    intro residue
    let i0 : Fin (gapCount + 1) := ⟨j, by omega⟩
    let i1 : Fin (gapCount + 1) := ⟨j + 1, by omega⟩
    let i2 : Fin (gapCount + 1) := ⟨j + 2, by omega⟩
    have hFirstCast : firstGap.castSucc = i0 := by ext; rfl
    have hFirstSucc : firstGap.succ = i1 := by ext; rfl
    have hSecondCast : secondGap.castSucc = i1 := by ext; rfl
    have hSecondSucc : secondGap.succ = i2 := by ext; rfl
    rcases denseGaps firstGap with hFirstGap | hFirstGap
    · have hSecondGap :
          offset secondGap.succ - offset secondGap.castSucc = 2 := by
        omega
      have h01Int : offset i1 - offset i0 = 2 := by
        simpa only [hFirstCast, hFirstSucc] using hFirstGap
      have h12Int : offset i2 - offset i1 = 2 := by
        simpa only [hSecondCast, hSecondSucc] using hSecondGap
      have h01Sub : (offset i1 : ZMod 3) - (offset i0 : ZMod 3) = 2 := by
        simpa only [Int.cast_sub, Int.cast_ofNat] using
          congrArg (fun value : Int => (value : ZMod 3)) h01Int
      have h12Sub : (offset i2 : ZMod 3) - (offset i1 : ZMod 3) = 2 := by
        simpa only [Int.cast_sub, Int.cast_ofNat] using
          congrArg (fun value : Int => (value : ZMod 3)) h12Int
      have h01 := sub_eq_iff_eq_add.mp h01Sub
      have h12 := sub_eq_iff_eq_add.mp h12Sub
      let start : Fin 3 := (ZMod.finEquiv 3).symm (offset i0 : ZMod 3)
      have hstart : (ZMod.finEquiv 3) start = (offset i0 : ZMod 3) :=
        (ZMod.finEquiv 3).apply_symm_apply _
      change (start : ZMod 3) = (offset i0 : ZMod 3) at hstart
      clear_value start
      have hcover : residue = (offset i0 : ZMod 3) \/
          residue = (offset i1 : ZMod 3) \/
          residue = (offset i2 : ZMod 3) := by
        fin_cases residue <;> fin_cases start <;>
          rw [h12, h01, ← hstart] <;>
          first
          | exact Or.inl rfl
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr rfl)
      rcases hcover with hcover | hcover | hcover
      · exact ⟨i0, hcover.symm⟩
      · exact ⟨i1, hcover.symm⟩
      · exact ⟨i2, hcover.symm⟩
    · have hSecondGap :
          offset secondGap.succ - offset secondGap.castSucc = 4 := by
        omega
      have h01Int : offset i1 - offset i0 = 4 := by
        simpa only [hFirstCast, hFirstSucc] using hFirstGap
      have h12Int : offset i2 - offset i1 = 4 := by
        simpa only [hSecondCast, hSecondSucc] using hSecondGap
      have h01Sub : (offset i1 : ZMod 3) - (offset i0 : ZMod 3) = 4 := by
        simpa only [Int.cast_sub, Int.cast_ofNat] using
          congrArg (fun value : Int => (value : ZMod 3)) h01Int
      have h12Sub : (offset i2 : ZMod 3) - (offset i1 : ZMod 3) = 4 := by
        simpa only [Int.cast_sub, Int.cast_ofNat] using
          congrArg (fun value : Int => (value : ZMod 3)) h12Int
      have h01 := sub_eq_iff_eq_add.mp h01Sub
      have h12 := sub_eq_iff_eq_add.mp h12Sub
      let start : Fin 3 := (ZMod.finEquiv 3).symm (offset i0 : ZMod 3)
      have hstart : (ZMod.finEquiv 3) start = (offset i0 : ZMod 3) :=
        (ZMod.finEquiv 3).apply_symm_apply _
      change (start : ZMod 3) = (offset i0 : ZMod 3) at hstart
      clear_value start
      have hcover : residue = (offset i0 : ZMod 3) \/
          residue = (offset i1 : ZMod 3) \/
          residue = (offset i2 : ZMod 3) := by
        fin_cases residue <;> fin_cases start <;>
          rw [h12, h01, ← hstart] <;>
          first
          | exact Or.inl rfl
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr rfl)
      rcases hcover with hcover | hcover | hcover
      · exact ⟨i0, hcover.symm⟩
      · exact ⟨i1, hcover.symm⟩
      · exact ⟨i2, hcover.symm⟩
  dsimp only
  constructor
  · intro hEven
    let points := List.ofFn offset
    have hDensePoints : forall (i : Nat) (hi : i + 1 < points.length),
        points[i + 1] - points[i] = 2 \/
          points[i + 1] - points[i] = 4 := by
      intro i hi
      have hiGap : i < gapCount := by
        simp [points] at hi
        omega
      let gapIndex : Fin gapCount := ⟨i, hiGap⟩
      simp only [points, List.getElem_ofFn]
      simpa [gapIndex, Fin.succ, Fin.castSucc] using denseGaps gapIndex
    have hAdmissiblePoints : exists omitted : ZMod 3,
        forall (i : Nat) (hi : i < points.length),
          (points[i] : ZMod 3) ≠ omitted := by
      simp only [Function.Surjective] at modThreeAdmissible
      push Not at modThreeAdmissible
      obtain ⟨omitted, homitted⟩ := modThreeAdmissible
      refine ⟨omitted, ?_⟩
      intro i hi
      have hiFin : i < gapCount + 1 := by simpa [points] using hi
      rw [show points[i] = offset ⟨i, hiFin⟩ by
        exact List.getElem_ofFn hi]
      exact homitted ⟨i, hiFin⟩
    have hOwner := even_dense_constellation_gap_code_self
      points hDensePoints hAdmissiblePoints (by simpa [points])
    have hCode :
        points.zipWith (fun left right => decide (right - left = 4)) points.tail =
          List.ofFn gapBit := by
      apply List.ext_getElem
      · simp [points]
      · intro i hleft hright
        rw [List.getElem_zipWith]
        rw [List.getElem_tail]
        have hiGap : i < gapCount := by simpa using hright
        have hiPoint : i < points.length := by simp [points]; omega
        have hiSuccPoint : i + 1 < points.length := by simp [points]; omega
        conv_lhs =>
          rw [show points[i + 1] = offset ⟨i + 1, by omega⟩ by
            exact List.getElem_ofFn hiSuccPoint]
          rw [show points[i] = offset ⟨i, by omega⟩ by
            exact List.getElem_ofFn hiPoint]
        conv_rhs => rw [List.getElem_ofFn]
        rfl
    rw [hCode] at hOwner
    simpa only [gapBit] using hOwner
  · intro hOdd
    simpa only [gapBit] using
      alternating_gap_reverse_complement_of_odd
        (gapCount + 1) (List.ofFn gapBit) (by simp) bitAlternating hOdd

#print axioms dense_gap_mirror_parity

end D5.S3.Arith.Congruence.DenseGapMirrorParity
