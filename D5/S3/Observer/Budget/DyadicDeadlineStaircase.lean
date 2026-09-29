/- GID: D5/S3/Observer/Budget/DyadicDeadlineStaircase
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/DyadicDeadlineStaircase
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact binary staircase for the operational deadline-family clock minimum. -/

import D5.S3.Observer.Budget.DyadicPrefixDelayRange

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.DyadicDeadlineStaircase

open DyadicForwardWaitingOptimality DyadicPrefixDelayRange TerminalClockCompression

/-- A binary prefix with at most one missing one-bit is the all-ones prefix
or is obtained by deleting exactly one of its binary places. -/
private theorem binary_prefix_top_or_one_missing (d : Nat) :
    ∀ t : Nat, t < 2 ^ d →
      t.bitIndices.length ≤ d ∧
      (t.bitIndices.length = d → t = 2 ^ d - 1) ∧
      (t.bitIndices.length + 1 = d →
        ∃ k : Nat, k < d ∧ t + 2 ^ k = 2 ^ d - 1) := by
  induction d with
  | zero =>
      intro t ht
      have h : t = 0 := by simpa using ht
      subst t
      simp [Nat.bitIndices]
  | succ d ih =>
      intro t ht
      have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; omega
      let q := t / 2
      have hq : q < 2 ^ d := by dsimp [q]; rw [hp] at ht; omega
      obtain ⟨bound, top, missing⟩ := ih q hq
      rcases (show t % 2 = 0 ∨ t % 2 = 1 by omega) with he | ho
      · have hform : t = 2 * q := by dsimp [q]; omega
        have hweight : t.bitIndices.length = q.bitIndices.length := by
          rw [hform, Nat.bitIndices_two_mul, List.length_map]
        refine ⟨by omega, ?_, ?_⟩
        · intro hw
          omega
        · intro hw
          have hfull := top (by omega)
          refine ⟨0, by omega, ?_⟩
          rw [hform, hfull, hp]
          norm_num
          omega
      · have hform : t = 2 * q + 1 := by dsimp [q]; omega
        have hweight : t.bitIndices.length = q.bitIndices.length + 1 := by
          rw [hform, Nat.bitIndices_two_mul_add_one]
          simp
        refine ⟨by omega, ?_, ?_⟩
        · intro hw
          have hfull := top (by omega)
          rw [hform, hfull, hp]
          omega
        · intro hw
          obtain ⟨k, hk, hmiss⟩ := missing (by omega)
          refine ⟨k + 1, by omega, ?_⟩
          rw [hform, hp, pow_succ]
          omega

private theorem binary_prefix_exception_weights (d : Nat) :
    (2 ^ d - 1).bitIndices.length = d ∧
    ∀ k : Nat, k < d → (2 ^ d - 1 - 2 ^ k).bitIndices.length + 1 = d := by
  induction d with
  | zero =>
      constructor
      · simp [Nat.bitIndices]
      · intro k hk
        omega
  | succ d ih =>
      obtain ⟨fullWeight, missingWeight⟩ := ih
      have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; omega
      have hfull : 0 < 2 ^ d := Nat.two_pow_pos d
      constructor
      · have hform : 2 ^ (d + 1) - 1 = 2 * (2 ^ d - 1) + 1 := by
          rw [hp]; omega
        rw [hform, Nat.bitIndices_two_mul_add_one]
        simp [fullWeight]
      · intro k hk
        by_cases hz : k = 0
        · subst k
          have hform : 2 ^ (d + 1) - 1 - 2 ^ 0 = 2 * (2 ^ d - 1) := by
            rw [hp]; omega
          rw [hform, Nat.bitIndices_two_mul, List.length_map, fullWeight]
        · have hk' : k - 1 < d := by omega
          have hpow : 2 ^ (k - 1) < 2 ^ d :=
            Nat.pow_lt_pow_right (by decide) hk'
          have hpowk : 2 ^ k = 2 * 2 ^ (k - 1) := by
            conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
            omega
          have hform : 2 ^ (d + 1) - 1 - 2 ^ k =
              2 * (2 ^ d - 1 - 2 ^ (k - 1)) + 1 := by
            rw [hp, hpowk]
            omega
          rw [hform, Nat.bitIndices_two_mul_add_one]
          simp only [List.length_cons, List.length_map]
          have := missingWeight (k - 1) hk'
          omega

/-- Exactly the all-ones prefix and the one-bit deletions can acquire a
second terminal parity after the sharp common deadline. -/
theorem exceptional_prefix_timing (d : Nat) :
    let P := 2 ^ (d + 1)
    let W := sharpWait (d + 1)
    earliestTime d (2 ^ d - 1) + P = W + P ∧
    (∀ k : Nat, k < d →
      earliestTime d (2 ^ d - 1 - 2 ^ k) + P = W + 2 ^ (k + 1)) ∧
    (∀ t : Nat, t < 2 ^ d → t.bitIndices.length + 2 ≤ d →
      earliestTime d t + P ≤ W) ∧
    (∀ t : Nat, t < 2 ^ d →
      t.bitIndices.length ≤ d ∧
      (t.bitIndices.length = d → t = 2 ^ d - 1) ∧
      (t.bitIndices.length + 1 = d →
        ∃ k : Nat, k < d ∧ t + 2 ^ k = 2 ^ d - 1)) := by
  dsimp only
  let P := 2 ^ (d + 1)
  let W := sharpWait (d + 1)
  have hp : P = 2 * 2 ^ d := by dsimp [P]; rw [pow_succ]; omega
  have hW : sharpWait (d + 1) = d * 2 ^ (d + 1) + 1 := by
    simp [sharpWait]
  obtain ⟨fullWeight, missingWeight⟩ := binary_prefix_exception_weights d
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
  refine ⟨?_, ?_, ?_, binary_prefix_top_or_one_missing d⟩
  · have hval : 2 * (2 ^ d - 1) < P := by rw [hp]; omega
    dsimp [P] at hval
    dsimp [earliestTime]
    rw [fullWeight, hW]
    rw [Nat.mul_comm (2 ^ (d + 1)) d]
    omega
  · intro k hk
    have hpow : 2 ^ k < 2 ^ d := Nat.pow_lt_pow_right (by decide) hk
    have hstep : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
    have hval : (2 ^ d - 1 - 2 ^ k) + 2 ^ k = 2 ^ d - 1 := by omega
    have hsmall : 2 * (2 ^ d - 1 - 2 ^ k) < P := by rw [hp]; omega
    have hwt := missingWeight k hk
    have hmul : P * (2 ^ d - 1 - 2 ^ k).bitIndices.length + P = P * d := by
      calc
        _ = P * ((2 ^ d - 1 - 2 ^ k).bitIndices.length + 1) := by ring
        _ = P * d := by rw [hwt]
    dsimp [P] at hmul hsmall
    dsimp [earliestTime]
    rw [hW, hstep]
    rw [Nat.mul_comm (2 ^ (d + 1)) d] at hmul
    omega
  · intro t ht hwt
    have hval : 2 * t < P := by rw [hp]; omega
    have hmul : P * t.bitIndices.length + 2 * P ≤ P * d := by
      have hm := Nat.mul_le_mul_left P hwt
      nlinarith [hm]
    dsimp [P] at hmul hval
    dsimp [earliestTime]
    rw [hW]
    rw [Nat.mul_comm (2 ^ (d + 1)) d] at hmul
    omega

#print axioms exceptional_prefix_timing

/-- The sharp deadline staircase counts labels of actual terminal times from
the entire deadline family, with one decoder shared by every controller. -/
theorem deadline_family_closed_staircase (d h : Nat) (b : Fin 2) :
    let D := sharpWait (d + 1) + h
    let q := (Finset.Icc 1 (d + 1)).filter (fun i => 2 ^ i ≤ h)
    (∀ (Z : Type*) (phi : Nat → Z) (recover : Z → Fin 2 → Nat),
      (∀ p : Protocol (d + 1), deadlineFamily d b D p →
        ∀ r, r < 2 ^ (d + 1) →
          recover (phi (terminalTime (2 ^ (d + 1)) b p r))
            (terminalRecord (2 ^ (d + 1)) b p r).2 = r) →
      2 ^ (d + 1) - (d + 1) + q.card ≤
        (familyClockLabels d b D phi).card) ∧
    (∀ p : Protocol (d + 1), deadlineFamily d b D p →
      ∀ r, r < 2 ^ (d + 1) →
        tagDecode d b (clockTag d (terminalTime (2 ^ (d + 1)) b p r))
          (terminalRecord (2 ^ (d + 1)) b p r).2 = r) ∧
    (familyClockLabels d b D (clockTag d)).card =
      2 ^ (d + 1) - (d + 1) + q.card := by
  classical
  dsimp only
  let D := sharpWait (d + 1) + h
  let q := (Finset.Icc 1 (d + 1)).filter (fun i => 2 ^ i ≤ h)
  let q0 := (Finset.range (d + 1)).filter (fun i => 2 ^ (i + 1) ≤ h)
  let bad := (Finset.univ : Finset (Fin (2 ^ d))).filter
    (fun t => ¬ earliestTime d t.val + 2 ^ (d + 1) ≤ D)
  let badIndex := (Finset.range (d + 1)).filter (fun i => h < 2 ^ (i + 1))
  let ex : Nat → Fin (2 ^ d) := fun i =>
    ⟨if i = d then 2 ^ d - 1 else 2 ^ d - 1 - 2 ^ i,
      by
        have hp := Nat.two_pow_pos d
        split_ifs
        · omega
        · exact lt_of_le_of_lt (Nat.sub_le _ _) (by omega)⟩
  have hD : sharpWait (d + 1) ≤ D := by dsimp [D]; omega
  obtain ⟨topTime, missingTime, lowTime, classify⟩ := exceptional_prefix_timing d
  have hbad : bad = badIndex.image ex := by
    ext t
    constructor
    · intro ht
      have htbad : ¬ earliestTime d t.val + 2 ^ (d + 1) ≤ D :=
        (Finset.mem_filter.mp ht).2
      obtain ⟨wtBound, top, missing⟩ := classify t.val t.isLt
      have hwt : t.val.bitIndices.length + 2 ≤ d → False := by
        intro hw
        exact htbad ((lowTime t.val t.isLt hw).trans hD)
      by_cases hfull : t.val.bitIndices.length = d
      · have heq := top hfull
        have hslack : h < 2 ^ (d + 1) := by
          rw [heq, topTime] at htbad
          dsimp [D] at htbad
          omega
        apply Finset.mem_image.mpr
        refine ⟨d, Finset.mem_filter.mpr ⟨by simp, ?_⟩, ?_⟩
        · exact hslack
        · apply Fin.ext
          simp [ex, heq]
      · have hnotlow : ¬ t.val.bitIndices.length + 2 ≤ d := hwt
        have hnear : t.val.bitIndices.length + 1 = d := by omega
        obtain ⟨k, hk, hsum⟩ := missing hnear
        have heq : t.val = 2 ^ d - 1 - 2 ^ k := by omega
        have hslack : h < 2 ^ (k + 1) := by
          rw [heq, missingTime k hk] at htbad
          dsimp [D] at htbad
          omega
        apply Finset.mem_image.mpr
        refine ⟨k, Finset.mem_filter.mpr ⟨by simp; omega, hslack⟩, ?_⟩
        apply Fin.ext
        simp [ex, hk.ne, heq]
    · intro ht
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨hiRange, hiSlack⟩ := Finset.mem_filter.mp hi
      have hiLe : i ≤ d := by simpa using hiRange
      apply Finset.mem_filter.mpr
      constructor
      · simp
      · by_cases hid : i = d
        · have heq : (ex i).val = 2 ^ d - 1 := by simp [ex, hid]
          rw [heq, topTime]
          dsimp [D]
          simpa [hid] using hiSlack
        · have hil : i < d := by omega
          have heq : (ex i).val = 2 ^ d - 1 - 2 ^ i := by simp [ex, hid]
          rw [heq, missingTime i hil]
          dsimp [D]
          omega
  have hexInj : Set.InjOn ex badIndex := by
    intro i hi j hj heq
    have hiLe : i ≤ d := by
      have := (Finset.mem_filter.mp hi).1
      simpa using this
    have hjLe : j ≤ d := by
      have := (Finset.mem_filter.mp hj).1
      simpa using this
    by_cases hid : i = d
    · by_cases hjd : j = d
      · omega
      · have hjl : j < d := by omega
        have hp := Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) hjl
        have hv : (ex i).val = (ex j).val := congrArg Fin.val heq
        have hiVal : (ex i).val = 2 ^ d - 1 := by simp [ex, hid]
        have hjVal : (ex j).val = 2 ^ d - 1 - 2 ^ j := by simp [ex, hjd]
        rw [hiVal, hjVal] at hv
        have hpos := Nat.two_pow_pos j
        omega
    · by_cases hjd : j = d
      · have hil : i < d := by omega
        have hp := Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) hil
        have hv : (ex i).val = (ex j).val := congrArg Fin.val heq
        have hiVal : (ex i).val = 2 ^ d - 1 - 2 ^ i := by simp [ex, hid]
        have hjVal : (ex j).val = 2 ^ d - 1 := by simp [ex, hjd]
        rw [hiVal, hjVal] at hv
        have hpos := Nat.two_pow_pos i
        omega
      · have hil : i < d := by omega
        have hjl : j < d := by omega
        have hpi := Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) hil
        have hpj := Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) hjl
        have hv : (ex i).val = (ex j).val := congrArg Fin.val heq
        simp [ex, hid, hjd] at hv
        have hpow : 2 ^ i = 2 ^ j := by omega
        exact (pow_right_injective₀ (by decide : 0 < (2 : Nat))
          (by decide : (2 : Nat) ≠ 1)) hpow
  have hcount : (eligiblePrefixes d D).card + badIndex.card = 2 ^ d := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (2 ^ d))))
      (fun t => earliestTime d t.val + 2 ^ (d + 1) ≤ D)
    have hsplit' : (eligiblePrefixes d D).card + bad.card = 2 ^ d := by
      simpa [eligiblePrefixes, bad] using hsplit
    rw [hbad, Finset.card_image_of_injOn hexInj] at hsplit'
    exact hsplit'
  have hparts := Finset.card_filter_add_card_filter_not
    (s := Finset.range (d + 1)) (fun i => 2 ^ (i + 1) ≤ h)
  have hqbad : q0.card + badIndex.card = d + 1 := by
    simpa [q0, badIndex, not_le] using hparts
  have hshift : q0.card = q.card := by
    have himage : q = q0.image (fun i => i + 1) := by
      ext k
      simp only [q, q0, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_image, Finset.mem_range]
      constructor
      · intro hk
        refine ⟨k - 1, ?_, by omega⟩
        constructor
        · omega
        · have heq : k - 1 + 1 = k := by omega
          rw [heq]
          exact hk.2
      · rintro ⟨i, ⟨hi, hp⟩, heq⟩
        constructor
        · omega
        · rwa [← heq]
    rw [himage, Finset.card_image_of_injOn]
    intro i hi j hj heq
    change i + 1 = j + 1 at heq
    omega
  have hvalue : 2 ^ d + (eligiblePrefixes d D).card =
      2 ^ (d + 1) - (d + 1) + q.card := by
    have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; omega
    have hle : d + 1 ≤ 2 ^ (d + 1) :=
      (show d + 1 < 2 ^ (d + 1) from Nat.lt_two_pow_self).le
    omega
  obtain ⟨hlower, hdecode, hattain⟩ :=
    (deadline_family_operational_capacity d b D).2 hD
  refine ⟨?_, hdecode, ?_⟩
  · intro Z phi recover hrecover
    rw [← hvalue]
    exact hlower Z phi recover hrecover
  · rw [← hvalue]
    exact hattain

#print axioms deadline_family_closed_staircase

end D5.S3.Observer.Budget.DyadicDeadlineStaircase
