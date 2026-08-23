/- GID: D5/S1/Deficit/ModelSet/GoldenModelSetSelfSimilar
   generality: I
   mirror-B: D5/B/S1/Deficit/ModelSet/GoldenModelSetSelfSimilar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Unit window; disjoint B split. Cut-project, density, window bounds, recovery omitted. -/

import D5.S1.Deficit.Displacement.GoldenInverseRecurrence
import D5.S1.Deficit.DoubleFaceLength
import D5.S1.Digit.Admissibility.LeastDigitDecomposition

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'golden_model_set_self_similar' D5 Golden/Frozen/accepted`
     returned no matches.
   * `DeficitInteger` defines `betaGolden`; `DoubleFaceLength.betaGolden_b` supplies its
     public integer-coordinate certificate. Its exponent-recovery theorem is not repeated.
   * `ZeckendorfDisplacementReading.conjugate_error_bounds` has the requested window
     bounds, but it is private. This module does not repeat those bounds.
   * `MinkowskiModelSet` and `MinkowskiHarnessWindow` define general window model sets,
     but do not identify `Set.range betaGolden` with the golden window or split that range.
   * `LeastDigitDecomposition.canonical_raw_least_digit_decomposition` publicly gives
     the upstream canonical-tail split reused below; it does not state the beta-range split.
   * The repository already exposes the exact inverse-golden identity as
     `GoldenInverseRecurrence.inv_goldenRatio_sq_add_inv_goldenRatio`; it is reused.
   * Pinned mathlib provides `Real.volume_Icc`, `Finsupp.sum_mapDomain_index`, and the
     standard set image/union/disjointness machinery; no searched declaration states the
     golden beta-range self-similarity theorem.
   * The cut-and-project identification, density `1 / sqrt 5`, window bounds, and exponent
     recovery clauses of the source theorem are not covered by this module.
   -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Deficit.GoldenModelSetSelfSimilar

open D5.S0.Carrier
open D5.S1.Deficit
open D5.S1.Deficit.Displacement.GoldenInverseRecurrence
open D5.S1.Digit
open D5.S1.Digit.Admissibility.LeastDigitDecomposition
open D5.S1.Scale
open MeasureTheory

/-- The closed conjugate window `[-1 / phi^2, 1 / phi]`. -/
noncomputable def goldenWindow : Set ℝ :=
  Set.Icc (-(Real.goldenRatio⁻¹ ^ 2)) Real.goldenRatio⁻¹

/-- The golden expansion-face value set, represented in the exact carrier `GoldenInt`. -/
noncomputable def goldenModelSet : Set GoldenInt := Set.range betaGolden

/-- The branch obtained by shifting every canonical digit one place upward. -/
noncomputable def phiBranch : Set GoldenInt :=
  (fun x ↦ phi * x) '' goldenModelSet

/-- The branch with least digit one and its remaining digits shifted two places upward. -/
noncomputable def phiSquaredBranch : Set GoldenInt :=
  (fun x ↦ phi ^ 2 + phi ^ 2 * x) '' goldenModelSet

@[simp] private theorem shift_digits_apply (offset i : Nat) (r : RawDigits) :
    shiftDigits offset r (offset + i) = r i := by
  apply Finsupp.mapDomain_apply
  exact fun _ _ equality ↦ Nat.add_left_cancel equality

private theorem shift_digits_eq_zero_of_lt {offset i : Nat} (r : RawDigits)
    (less : i < offset) : shiftDigits offset r i = 0 := by
  rw [shiftDigits, Finsupp.mapDomain_notin_range]
  rintro ⟨j, equality⟩
  subst i
  exact (Nat.not_lt_of_ge (Nat.le_add_right offset j)) less

private theorem shift_digits_canonical (offset : Nat) {r : RawDigits}
    (canonical : CanonicalRaw r) : CanonicalRaw (shiftDigits offset r) := by
  constructor
  · intro i
    by_cases inRange : offset ≤ i
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le inRange
      simpa [add_comm] using canonical.1 j
    · rw [shift_digits_eq_zero_of_lt r (Nat.lt_of_not_ge inRange)]
      omega
  · intro i occupied
    have inRange : offset ≤ i := by
      by_contra outside
      rw [shift_digits_eq_zero_of_lt r (Nat.lt_of_not_ge outside)] at occupied
      contradiction
    let j := i - offset
    have indexEq : i = offset + j := (Nat.add_sub_of_le inRange).symm
    have tailOccupied : r j = 1 := by simpa [indexEq] using occupied
    rw [show i + 1 = offset + (j + 1) by omega, shift_digits_apply]
    exact canonical.2 j tailOccupied

private theorem beta_digits_add (r s : RawDigits) :
    betaDigits (r + s) = betaDigits r + betaDigits s := by
  classical
  refine Finsupp.sum_add_index' (fun i ↦ ?_) (fun i m₁ m₂ ↦ ?_)
  · simp
  · push_cast
    ring

@[simp] private theorem beta_digits_single (i coefficient : Nat) :
    betaDigits (Finsupp.single i coefficient) =
      (coefficient : GoldenInt) * phi ^ (i + 2) := by
  classical
  rw [betaDigits, Finsupp.sum_single_index (by simp)]

private theorem beta_digits_shift (offset : Nat) (r : RawDigits) :
    betaDigits (shiftDigits offset r) = phi ^ offset * betaDigits r := by
  classical
  rw [betaDigits, shiftDigits]
  rw [Finsupp.sum_mapDomain_index]
  · rw [betaDigits, Finsupp.mul_sum]
    apply Finsupp.sum_congr
    intro i _
    rw [pow_add]
    ring
  · intro i
    simp
  · intro i m₁ m₂
    push_cast
    ring

private theorem beta_digits_mem_model_set {r : RawDigits} (canonical : CanonicalRaw r) :
    betaDigits r ∈ goldenModelSet := by
  refine ⟨rawValue r, ?_⟩
  rw [betaGolden]
  congr 1
  apply canonicalRaw_unique (canonicalRaw_toRaw _) canonical
  rw [rawValue_toRaw_Z]

private theorem drop_digits_canonical (offset : Nat) {r : RawDigits}
    (canonical : CanonicalRaw r) : CanonicalRaw (dropDigits offset r) := by
  constructor
  · intro i
    rw [drop_digits_apply]
    exact canonical.1 (offset + i)
  · intro i occupied
    rw [drop_digits_apply] at occupied ⊢
    simpa [Nat.add_assoc] using canonical.2 (offset + i) occupied

private theorem shift_drop_one_eq {r : RawDigits} (leastZero : r 0 = 0) :
    shiftDigits 1 (dropDigits 1 r) = r := by
  ext i
  cases i with
  | zero =>
      rw [shift_digits_eq_zero_of_lt (dropDigits 1 r) (by omega)]
      exact leastZero.symm
  | succ i =>
      rw [show i + 1 = 1 + i by omega, shift_digits_apply, drop_digits_apply]

private theorem least_one_shift_two_canonical {r : RawDigits} (canonical : CanonicalRaw r) :
    CanonicalRaw (Finsupp.single 0 1 + shiftDigits 2 r) := by
  constructor
  · intro i
    rcases i with _ | _ | i
    · simp [shift_digits_eq_zero_of_lt (offset := 2) r]
    · simp [shift_digits_eq_zero_of_lt (offset := 2) r]
    · change ((Finsupp.single 0 1 : RawDigits) + shiftDigits 2 r) (i + 2) ≤ 1
      rw [Finsupp.add_apply,
        Finsupp.single_eq_of_ne (Nat.add_pos_right i (by decide : 0 < 2)).ne', zero_add]
      rw [show i + 2 = 2 + i by omega, shift_digits_apply]
      exact canonical.1 i
  · intro i occupied
    rcases i with _ | _ | i
    · simp [shift_digits_eq_zero_of_lt (offset := 2) r]
    · simp [shift_digits_eq_zero_of_lt (offset := 2) r] at occupied
    · have tailOccupied : r i = 1 := by
        change ((Finsupp.single 0 1 : RawDigits) + shiftDigits 2 r) (i + 2) = 1
          at occupied
        rw [Finsupp.add_apply,
          Finsupp.single_eq_of_ne (Nat.add_pos_right i (by decide : 0 < 2)).ne',
          zero_add] at occupied
        rw [show i + 2 = 2 + i by omega, shift_digits_apply] at occupied
        exact occupied
      change ((Finsupp.single 0 1 : RawDigits) + shiftDigits 2 r) (i + 2 + 1) = 0
      rw [Finsupp.add_apply,
        Finsupp.single_eq_of_ne (Nat.add_pos_right (i + 2) (by decide : 0 < 1)).ne',
        zero_add]
      rw [show i + 2 + 1 = 2 + (i + 1) by omega, shift_digits_apply]
      exact canonical.2 i tailOccupied

/-- The Lebesgue length of the closed golden conjugate window is exactly one. -/
theorem golden_window_volume : volume goldenWindow = 1 := by
  rw [goldenWindow, Real.volume_Icc, sub_neg_eq_add, add_comm]
  rw [inv_goldenRatio_sq_add_inv_goldenRatio]
  norm_num

/-- The golden beta range is the disjoint union `phi * B ⊎ (phi^2 + phi^2 * B)`. -/
theorem golden_model_set_self_similar :
    goldenModelSet = phiBranch ∪ phiSquaredBranch ∧
      Disjoint phiBranch phiSquaredBranch := by
  constructor
  · apply Set.Subset.antisymm
    · rintro y ⟨n, rfl⟩
      let r := toRaw (Z n)
      have canonical : CanonicalRaw r := canonicalRaw_toRaw _
      change betaDigits r ∈ phiBranch ∪ phiSquaredBranch
      rw [Set.mem_union]
      by_cases leastZero : r 0 = 0
      · left
        change betaDigits r ∈ (fun x : GoldenInt ↦ phi * x) '' goldenModelSet
        refine ⟨betaDigits (dropDigits 1 r),
          beta_digits_mem_model_set (drop_digits_canonical 1 canonical), ?_⟩
        calc
          phi * betaDigits (dropDigits 1 r) =
              betaDigits (shiftDigits 1 (dropDigits 1 r)) := by
                simpa using (beta_digits_shift 1 (dropDigits 1 r)).symm
          _ = betaDigits r := by rw [shift_drop_one_eq leastZero]
      · right
        have leastOne : r 0 = 1 := by
          have bound := canonical.1 0
          omega
        have nonzero : r ≠ 0 := by
          intro zero
          rw [zero] at leastOne
          simp at leastOne
        rcases canonical_raw_least_digit_decomposition r canonical nonzero with
          first | second | third
        · exact (leastZero first.1.1).elim
        · rcases second.2 with ⟨tail, ⟨tailCanonical, recompose⟩, _⟩
          change betaDigits r ∈
            (fun x : GoldenInt ↦ phi ^ 2 + phi ^ 2 * x) '' goldenModelSet
          refine ⟨betaDigits tail, beta_digits_mem_model_set tailCanonical, ?_⟩
          rw [recompose, beta_digits_add, beta_digits_single, beta_digits_shift]
          norm_num
        · exact (leastZero third.1.1).elim
    · intro y membership
      rw [Set.mem_union] at membership
      rcases membership with leftBranch | rightBranch
      · change y ∈ (fun x : GoldenInt ↦ phi * x) '' goldenModelSet at leftBranch
        rcases leftBranch with ⟨_, ⟨n, rfl⟩, rfl⟩
        have canonical : CanonicalRaw (toRaw (Z n)) := canonicalRaw_toRaw _
        have shifted := beta_digits_mem_model_set (shift_digits_canonical 1 canonical)
        rw [beta_digits_shift, pow_one] at shifted
        exact shifted
      · change y ∈
          (fun x : GoldenInt ↦ phi ^ 2 + phi ^ 2 * x) '' goldenModelSet at rightBranch
        rcases rightBranch with ⟨_, ⟨n, rfl⟩, rfl⟩
        have canonical : CanonicalRaw (toRaw (Z n)) := canonicalRaw_toRaw _
        have prefixed := beta_digits_mem_model_set
          (least_one_shift_two_canonical canonical)
        rw [beta_digits_add, beta_digits_single, beta_digits_shift] at prefixed
        norm_num at prefixed ⊢
        exact prefixed
  · rw [Set.disjoint_left]
    intro y leftMembership rightMembership
    change y ∈ (fun x : GoldenInt ↦ phi * x) '' goldenModelSet at leftMembership
    change y ∈
      (fun x : GoldenInt ↦ phi ^ 2 + phi ^ 2 * x) '' goldenModelSet at rightMembership
    rcases leftMembership with ⟨_, ⟨m, rfl⟩, leftValue⟩
    rcases rightMembership with ⟨_, ⟨n, rfl⟩, rightValue⟩
    let r := toRaw (Z m)
    let s := toRaw (Z n)
    have rCanonical : CanonicalRaw r := canonicalRaw_toRaw _
    have sCanonical : CanonicalRaw s := canonicalRaw_toRaw _
    have valueEq :
        betaDigits (shiftDigits 1 r) =
          betaDigits (Finsupp.single 0 1 + shiftDigits 2 s) := by
      rw [beta_digits_shift, pow_one, beta_digits_add, beta_digits_single,
        beta_digits_shift]
      norm_num
      simpa [betaGolden, r, s] using leftValue.trans rightValue.symm
    have coordinateEq := congrArg GoldenInt.b valueEq
    have integerValueEq :
        (rawValue (shiftDigits 1 r) : ℤ) =
          (rawValue (Finsupp.single 0 1 + shiftDigits 2 s) : ℤ) := by
      simpa only [D5.S1.Deficit.DoubleFaceLength.betaDigits_b] using coordinateEq
    have rawValueEq :
        rawValue (shiftDigits 1 r) =
          rawValue (Finsupp.single 0 1 + shiftDigits 2 s) := by
      exact_mod_cast integerValueEq
    have rawEq := canonicalRaw_unique (shift_digits_canonical 1 rCanonical)
      (least_one_shift_two_canonical sCanonical) rawValueEq
    have leastEq := congrArg (fun digits : RawDigits ↦ digits 0) rawEq
    simp [shift_digits_eq_zero_of_lt (offset := 1) r,
      shift_digits_eq_zero_of_lt (offset := 2) s] at leastEq

example : betaGolden 0 ∈ goldenModelSet := ⟨0, rfl⟩

#print axioms golden_model_set_self_similar

end D5.S1.Deficit.GoldenModelSetSelfSimilar
