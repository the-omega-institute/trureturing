/- GID: D5/S3/Topology/FourBraidKhovanovQuantum21
   generality: I
   mirror-B: D5/B/S3/Topology/FourBraidKhovanovQuantum21
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Finsupp.LinearCombination]
   utility: none
   digest: Degree 21 of the signed integral Khovanov cube. -/

import D5.S3.Topology.FourBraidKhovanovIntegralRow


/-! Exact coefficients and contraction identities in the signed integral cube. -/

set_option autoImplicit false

namespace D5.S3.Topology.FourBraidKhovanovCube


set_option maxRecDepth 8192
set_option linter.style.setOption false
set_option maxHeartbeats 3500000

private def b21_10 : Array Enhanced := #[
    (1021, 0), (1533, 0), (1534, 0)
  ]
private def b21_11 : Array Enhanced := #[
    (1023, 0), (1535, 0), (2045, 0), (2046, 0)
  ]
private def b21_12 : Array Enhanced := #[
    (2047, 0)
  ]
private def b21Data : Nat → Array Enhanced
  | 10 => b21_10
  | 11 => b21_11
  | 12 => b21_12
  | _ => #[]

private def b21 (t : Nat) : Array Enhanced := if t < 13 then b21Data t else #[]

private def d21_10 : RawColumns := #[
    [(0, -1), (2, -1)], [(1, -1), (2, 1)], [(1, 1), (3, 1)]
  ]
private def d21_11 : RawColumns := #[
    [(0, 1)], [(0, -1)], [(0, -1)], [(0, 1)]
  ]
private def d21Data : Nat → RawColumns
  | 10 => d21_10
  | 11 => d21_11
  | _ => #[]

private def d21 (t : Nat) : RawColumns := if t < 13 then d21Data t else #[]

private def p21Data : Nat → RawColumns
  | _ => #[]

private def p21 (t : Nat) : RawColumns := if t < 13 then p21Data t else #[]

private def i21Data : Nat → RawColumns
  | _ => #[]

private def i21 (t : Nat) : RawColumns := if t < 13 then i21Data t else #[]

private def h21_11 : RawColumns := #[
    [(0, -1), (1, -1), (2, -1)], [(2, 1)], [(1, 1), (2, 1)], []
  ]
private def h21_12 : RawColumns := #[
    [(3, 1)]
  ]
private def h21Data : Nat → RawColumns
  | 11 => h21_11
  | 12 => h21_12
  | _ => #[]

private def h21 (t : Nat) : RawColumns := if t < 13 then h21Data t else #[]

private def rank21 (k : Nat) : Nat := 0

private def cached21 : IntegralRow :=
  ⟨b21, fun t => some (if (d21 t).isEmpty then
    Array.replicate (b21 t).size [] else d21 t)⟩

private def contraction21 : Contraction := ⟨rank21, p21, i21, h21⟩

private theorem basis21_0 : replayStageBasis 21 0 = b21 0 := by decide +kernel
private theorem matrix21_0 :
    calculateMatrix replayResolution (b21 0) (b21 (0 + 1)) =
      cached21.matrix 0 := rfl
private theorem check21_0 : contraction21.check cached21 0 = true := by decide +kernel
private theorem basis21_1 : replayStageBasis 21 1 = b21 1 := by decide +kernel
private theorem matrix21_1 :
    calculateMatrix replayResolution (b21 1) (b21 (1 + 1)) =
      cached21.matrix 1 := rfl
private theorem check21_1 : contraction21.check cached21 1 = true := by decide +kernel
private theorem basis21_2 : replayStageBasis 21 2 = b21 2 := by decide +kernel
private theorem matrix21_2 :
    calculateMatrix replayResolution (b21 2) (b21 (2 + 1)) =
      cached21.matrix 2 := rfl
private theorem check21_2 : contraction21.check cached21 2 = true := by decide +kernel
private theorem basis21_3 : replayStageBasis 21 3 = b21 3 := by decide +kernel
private theorem matrix21_3 :
    calculateMatrix replayResolution (b21 3) (b21 (3 + 1)) =
      cached21.matrix 3 := rfl
private theorem check21_3 : contraction21.check cached21 3 = true := by decide +kernel
private theorem basis21_4 : replayStageBasis 21 4 = b21 4 := by decide +kernel
private theorem matrix21_4 :
    calculateMatrix replayResolution (b21 4) (b21 (4 + 1)) =
      cached21.matrix 4 := rfl
private theorem check21_4 : contraction21.check cached21 4 = true := by decide +kernel
private theorem basis21_5 : replayStageBasis 21 5 = b21 5 := by decide +kernel
private theorem matrix21_5 :
    calculateMatrix replayResolution (b21 5) (b21 (5 + 1)) =
      cached21.matrix 5 := rfl
private theorem check21_5 : contraction21.check cached21 5 = true := by decide +kernel
private theorem basis21_6 : replayStageBasis 21 6 = b21 6 := by decide +kernel
private theorem matrix21_6 :
    calculateMatrix replayResolution (b21 6) (b21 (6 + 1)) =
      cached21.matrix 6 := rfl
private theorem check21_6 : contraction21.check cached21 6 = true := by decide +kernel
private theorem basis21_7 : replayStageBasis 21 7 = b21 7 := by decide +kernel
private theorem matrix21_7 :
    calculateMatrix replayResolution (b21 7) (b21 (7 + 1)) =
      cached21.matrix 7 := rfl
private theorem check21_7 : contraction21.check cached21 7 = true := by decide +kernel
private theorem basis21_8 : replayStageBasis 21 8 = b21 8 := by decide +kernel
private theorem matrix21_8 :
    calculateMatrix replayResolution (b21 8) (b21 (8 + 1)) =
      cached21.matrix 8 := rfl
private theorem check21_8 : contraction21.check cached21 8 = true := by decide +kernel
private theorem basis21_9 : replayStageBasis 21 9 = b21 9 := by decide +kernel
private theorem matrix21_9 :
    calculateMatrix replayResolution (b21 9) (b21 (9 + 1)) =
      cached21.matrix 9 := rfl
private theorem check21_9 : contraction21.check cached21 9 = true := by decide +kernel
private theorem basis21_10 : replayStageBasis 21 10 = b21 10 := by decide +kernel
private theorem matrix21_10 :
    calculateMatrix replayResolution (b21 10) (b21 (10 + 1)) =
      cached21.matrix 10 := rfl
private theorem check21_10 : contraction21.check cached21 10 = true := by decide +kernel
private theorem basis21_11 : replayStageBasis 21 11 = b21 11 := by decide +kernel
private theorem matrix21_11 :
    calculateMatrix replayResolution (b21 11) (b21 (11 + 1)) =
      cached21.matrix 11 := rfl
private theorem check21_11 : contraction21.check cached21 11 = true := by decide +kernel
private theorem basis21_12 : replayStageBasis 21 12 = b21 12 := by decide +kernel
private theorem matrix21_12 :
    calculateMatrix replayResolution (b21 12) (b21 (12 + 1)) =
      cached21.matrix 12 := rfl
private theorem check21_12 : contraction21.check cached21 12 = true := by decide +kernel
private theorem allBasis21 (t : Nat) : replayStageBasis 21 t = b21 t := by
  by_cases ht : t < 13
  · interval_cases t
    · exact basis21_0
    · exact basis21_1
    · exact basis21_2
    · exact basis21_3
    · exact basis21_4
    · exact basis21_5
    · exact basis21_6
    · exact basis21_7
    · exact basis21_8
    · exact basis21_9
    · exact basis21_10
    · exact basis21_11
    · exact basis21_12
  · have ht' : 13 ≤ t := by omega
    cases t with
    | zero => omega
    | succ k =>
      have hk : ¬ k < crossings + 1 := by norm_num [crossings, braid]; omega
      simp only [replayStageBasis, if_neg hk]
      simp [b21, show ¬k + 1 < 13 by omega]
private theorem allMatrix21 (t : Nat) : calculateMatrix replayResolution (b21 t) (b21 (t + 1)) = cached21.matrix t := by
  by_cases ht : t < 13
  · interval_cases t
    · exact matrix21_0
    · exact matrix21_1
    · exact matrix21_2
    · exact matrix21_3
    · exact matrix21_4
    · exact matrix21_5
    · exact matrix21_6
    · exact matrix21_7
    · exact matrix21_8
    · exact matrix21_9
    · exact matrix21_10
    · exact matrix21_11
    · exact matrix21_12
  · have h₀ : b21 t = #[] := by simp [b21, ht]
    have h₁ : d21 t = #[] := by simp [d21, ht]
    simp [cached21, calculateMatrix, h₀, h₁]
private theorem allChecks21 (t : Nat) : contraction21.check cached21 t = true := by
  by_cases ht : t < 13
  · interval_cases t
    · exact check21_0
    · exact check21_1
    · exact check21_2
    · exact check21_3
    · exact check21_4
    · exact check21_5
    · exact check21_6
    · exact check21_7
    · exact check21_8
    · exact check21_9
    · exact check21_10
    · exact check21_11
    · exact check21_12
  · have h₀ : (cached21.basis t).size = 0 := by simp [cached21, b21, ht]
    have h₁ : (cached21.basis (t + 1)).size = 0 := by
      simp [cached21, b21, show ¬ t + 1 < 13 by omega]
    have h₂ : contraction21.rank t = 0 := by
      simp [contraction21, rank21, show t ≠ 7 by omega, show t ≠ 8 by omega]
    exact Contraction.check_empty _ _ _ h₀ h₁ h₂
private theorem cached21_eq : cached21 = integralRow 21 := by
  have hb : replayStageBasis 21 = b21 := funext allBasis21
  have hs := replayStageBasis_eq 21 (by decide)
  have hm : (fun t => (cached21).matrix t) = stageMatrix 21 := by
    funext t
    rw [stageMatrix_eq_replay 21 t (by decide), hb]
    exact (allMatrix21 t).symm
  exact congrArg₂ IntegralRow.mk (hb.symm.trans hs) hm

theorem quantum21_integral : (integralRow 21).Computes
    (fun k => 0) := by
  rw [← cached21_eq]
  exact contraction21.sound _ (fun _ => rfl) allChecks21


end D5.S3.Topology.FourBraidKhovanovCube
