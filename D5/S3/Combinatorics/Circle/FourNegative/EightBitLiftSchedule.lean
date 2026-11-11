/- GID: D5/S3/Combinatorics/Circle/FourNegative/EightBitLiftSchedule
   generality: I
   mirror-B: none(waiver:consumed-by-eight-bit-physical-lift)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Literal physical eight-bit insertion and its charge-prefix proof. -/
import D5.S3.Combinatorics.Circle.FourNegative.EightBitLiftWord

/-! # A shared adaptive orientation for both physical coordinates -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.EightBitPhysicalLift

open SourceWidth PeriodicShorteningArithmetic

theorem target_double (k : ℕ) (hk : 8 ≤ k) :
    targetN k = 2 * targetH k + 1 ∧ targetH k = modulus (k + 8) / 2 := by
  have hp : (2 : ℤ) ^ k = 2 * 2 ^ (k - 1) := by
    calc
      (2 : ℤ) ^ k = 2 ^ ((k - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (k - 1) := by rw [pow_succ]; ring
  have hm : modulus k = 2 * (2 : ℤ) ^ (k - 1) - 1 := by rw [modulus, hp]
  have hh : modulus k / 2 = (2 : ℤ) ^ (k - 1) - 1 := by rw [hm]; omega
  have hn := (target_bounds k (by omega)).1
  rw [hm] at hn
  rw [targetH, hh]
  constructor
  · omega
  · change _ = targetN k / 2
    omega

theorem state_relation (k : ℕ) (hk : 8 ≤ k) (l : List (Fin (k + 1))) :
    secondState l = 2 * firstState l - (l.map (fullCharge k)).sum +
      85 * (l.map earIndicator).sum := by
  have h := (full_prefix_rows k hk l).2
  unfold firstState secondState
  rw [h]
  ring

def prefixEar {k : ℕ} (l : List (Fin (k + 1))) : Bool :=
  decide ((l.map earIndicator).sum = 1)

def adaptiveOrientation (k : ℕ) (hk : 8 ≤ k) (w : List (Fin (k + 1))) : Fin 8 → Bool :=
  fun i => decide (¬ (firstState (w.take (w.idxOf ⟨i.val, by omega⟩)) +
    85 * (2 : ℤ) ^ i.val ≤ corridorUpper (targetH k)
      (((w.take (w.idxOf ⟨i.val, by omega⟩)).map (fullCharge k)).sum)
      (prefixEar (w.take (w.idxOf ⟨i.val, by omega⟩)))))

private theorem pair_midpoint (H C c e x y a p : ℤ)
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hCc : C + c ≤ 85)
    (he : e = 0 ∨ e = 1) (hp : 0 ≤ p)
    (hrel : y = 2 * x - C + 85 * e)
    (hx : 0 ≤ x ∧ x ≤ H ∧ 0 ≤ y ∧ y ≤ 2 * H + 1)
    (hz : 0 ≤ x + a + p ∧ x + a + p ≤ H ∧
      0 ≤ y + 2 * a - c + 2 * p ∧ y + 2 * a - c + 2 * p ≤ 2 * H + 1)
    (hrow : (0 ≤ a ∧ 0 ≤ 2 * a - c) ∨
      (a ≤ 0 ∧ p - a ≤ H - 85) ∨ x + p ≤ H - 42) :
    if x + p ≤ corridorUpper H C (decide (e = 1)) then
      0 ≤ x + p ∧ x + p ≤ H ∧ 0 ≤ y + 2 * p ∧ y + 2 * p ≤ 2 * H + 1
    else
      0 ≤ x + a ∧ x + a ≤ H ∧ 0 ≤ y + 2 * a - c ∧
        y + 2 * a - c ≤ 2 * H + 1 := by
  have hC85 : C ≤ 85 := by omega
  have heb : e = if decide (e = 1) then 1 else 0 := by
    rcases he with rfl | rfl <;> norm_num
  have hxcor := (corridor_iff H C x (decide (e = 1)) ⟨hC, hC85⟩).mp (by
    rw [← heb, ← hrel]; exact hx)
  have hzcor := (corridor_iff H (C + c) (x + a + p) (decide (e = 1))
    ⟨by omega, hCc⟩).mp (by
      rw [← heb]
      exact ⟨hz.1, hz.2.1, by omega, by omega⟩)
  split_ifs with hfit
  · have hm := (corridor_iff H C (x + p) (decide (e = 1)) ⟨hC, hC85⟩).mpr
      ⟨by omega, hfit⟩
    rw [← heb] at hm
    have heq : 2 * (x + p) - C + 85 * e = y + 2 * p := by rw [hrel]; ring
    simpa only [heq] using hm
  · rcases hrow with hpos | hneg | hsmall
    · omega
    · have hm := negative_pair_corridor H C c x a p (decide (e = 1))
        hC hc hCc hxcor hzcor hneg.1 hp hneg.2
      rw [if_neg hfit] at hm
      have hm' := (corridor_iff H (C + c) (x + a) (decide (e = 1))
        ⟨by omega, hCc⟩).mpr hm
      rw [← heb] at hm'
      have heq : 2 * (x + a) - (C + c) + 85 * e = y + 2 * a - c := by
        rw [hrel]; ring
      simpa only [heq] using hm'
    · rcases he with rfl | rfl <;>
        simp only [corridorUpper, decide_false, decide_true, Bool.false_eq_true,
          Bool.true_eq, if_false, if_true] at hfit <;> omega

theorem state_append (k : ℕ) (l : List (Fin (k + 1))) (j : Fin (k + 1)) :
    firstState (l ++ [j]) = firstState l +
      (256 * fullFirst k j - 255 * fullCharge k j + 85 * lowWeight j) ∧
    secondState (l ++ [j]) = secondState l +
      (256 * actualSource (k + 1) 170 j - 255 * fullCharge k j -
        21675 * earIndicator j + 170 * lowWeight j) := by
  simp only [firstState, secondState, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  constructor <;> ring

theorem adaptive_block_strip (k : ℕ) (hk : 8 ≤ k)
    (w : List (Fin (k + 1))) (hw : JointWord k w) (n : ℕ) (hn : n < w.length) :
    InStrip (fullFirst (k + 8)) (targetH k) (firstState (w.take n))
      (physicalBlock (adaptiveOrientation k hk w) w[n]) ∧
    InStrip (actualSource (k + 9) 170) (targetN k) (secondState (w.take n))
      (physicalBlock (adaptiveOrientation k hk w) w[n]) := by
  let l := w.take n
  let j := w[n]
  have ht : w.take (n + 1) = l ++ [j] := List.take_succ_eq_append_getElem hn
  have hs := canonical_complete_prefix k hk w hw n
  have hz := canonical_complete_prefix k hk w hw (n + 1)
  rw [ht] at hz
  have hstep := state_append k l j
  have hold := target_full_old_rows k hk j
  change InStrip _ _ _ (physicalBlock _ j) ∧ InStrip _ _ _ (physicalBlock _ j)
  by_cases hj : j.val < 8
  · let i : Fin k := ⟨j.val, by omega⟩
    have hji : j = i.castSucc := rfl
    have hnew := target_full_new_rows k hk ⟨j.val, hj⟩
    let x := firstState l
    let y := secondState l
    let C := (l.map (fullCharge k)).sum
    let e := (l.map earIndicator).sum
    let c := fullCharge k j
    let a := 256 * fullFirst k j - 255 * c
    let p := 85 * (2 : ℤ) ^ j.val
    have hinv := full_prefix_inventory k hk w hw.1 n
    have hc := (full_source_rows k hk j).1
    have hinv' := (full_prefix_inventory k hk w hw.1 (n + 1)).1
    rw [ht] at hinv'
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero] at hinv'
    have he : e = 0 ∨ e = 1 := by dsimp [e, l]; omega
    have hear : earIndicator j = 0 := by simp [earIndicator, show j.val ≠ k by omega]
    have hlow : lowWeight j = (2 : ℤ) ^ j.val := by simp [lowWeight, hj]
    have hrel : y = 2 * x - C + 85 * e := state_relation k hk l
    have hrow := (full_source_rows k hk j).2.2
    have hsecond : 256 * actualSource (k + 1) 170 j - 255 * fullCharge k j -
        21675 * earIndicator j = 2 * a - c := by
      rw [hrow, hear]
      dsimp [a, c]
      ring
    have hstepx : firstState (l ++ [j]) = x + a + p := by
      rw [hstep.1, hlow]; dsimp [x, a, p, c]; ring
    have hstepy : secondState (l ++ [j]) = y + 2 * a - c + 2 * p := by
      rw [hstep.2, hlow]
      dsimp [y, a, c, p]
      rw [hrow, hear]
      ring
    have hpairrow : (0 ≤ a ∧ 0 ≤ 2 * a - c) ∨
        (a ≤ 0 ∧ p - a ≤ targetH k - 85) ∨ x + p ≤ targetH k - 42 := by
      by_cases hk8 : k = 8
      · right; right
        have hp : p ≤ 10880 := by
          have h := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
            (show j.val ≤ 7 by omega)
          norm_num at h
          dsimp [p]
          omega
        have hx : x ≤ 21845 := hs.2.2.2.2 hk8
        have hH8 : targetH k = 32767 := by subst k; norm_num [targetH, modulus]
        omega
      · have h := low_row_parity k (by omega) i (by exact hj)
        have h' : (0 ≤ a ∧ 0 ≤ 2 * a - c) ∨ (a ≤ 0 ∧ p - a ≤ targetH k - 171) := by
          simpa only [a, c, p, hji, fullFirst, fullCharge, Fin.lastCases_castSucc,
            Fin.val_castSucc] using h
        rcases h' with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨h.1, by omega⟩)
    have hmid := pair_midpoint (targetH k) C c e x y a p
      hinv.1.1 hc (by exact hinv'.2) he (by dsimp [p]; positivity) hrel
      (by rw [← (target_double k hk).1]; exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩)
      (by rw [← hstepx, ← hstepy, ← (target_double k hk).1]
          exact ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1⟩) hpairrow
    have hnd := hw.1.nodup_iff.mpr (List.nodup_finRange _)
    have ho : adaptiveOrientation k hk w ⟨j.val, hj⟩ =
        decide (¬ (x + p ≤ corridorUpper (targetH k) C (decide (e = 1)))) := by
      unfold adaptiveOrientation
      have heq : (⟨j.val, by omega⟩ : Fin (k + 1)) = w[n] := rfl
      rw [heq, hnd.idxOf_getElem n hn]
      rfl
    change InStrip _ _ _ (physicalBlock _ j) ∧ InStrip _ _ _ (physicalBlock _ j)
    unfold physicalBlock
    rw [dif_pos hj, ho]
    have hfirst : fullFirst (k + 8) (liftOldLabel j) = a := hold.1
    have hsecond' : actualSource (k + 9) 170 (liftOldLabel j) = 2 * a - c := by
      rw [hold.2.2.2, hsecond]
    have hnewx : fullFirst (k + 8) (liftNewLabel ⟨j.val, hj⟩) = p := hnew.1
    have hnewy : actualSource (k + 9) 170 (liftNewLabel ⟨j.val, hj⟩) = 2 * p := by
      rw [hnew.2]; dsimp [p]; ring
    by_cases hfit : x + p ≤ corridorUpper (targetH k) C (decide (e = 1))
    · rw [if_pos hfit] at hmid
      simp only [hfit, not_true_eq_false, decide_false, Bool.false_eq_true,
        if_false, InStrip, hfirst, hsecond', hnewx, hnewy]
      simp only [(target_double k hk).1]
      rw [hstepx, hstepy] at hz
      rw [(target_double k hk).1] at hs hz
      dsimp [x, y, l] at *
      constructor <;> (repeat' constructor) <;> omega
    · rw [if_neg hfit] at hmid
      simp only [hfit, not_false_eq_true, decide_true, if_true, InStrip,
        hfirst, hsecond', hnewx, hnewy]
      simp only [(target_double k hk).1]
      rw [hstepx, hstepy] at hz
      rw [(target_double k hk).1] at hs hz
      dsimp [x, y, l] at *
      constructor <;> (repeat' constructor) <;> omega
  · have hlow : lowWeight j = 0 := by simp [lowWeight, hj]
    simp only [physicalBlock, dif_neg hj, InStrip]
    rw [hold.1, hold.2.2.2]
    rw [hlow] at hstep
    simp only [mul_zero, add_zero] at hstep
    constructor <;> (repeat' constructor) <;> dsimp [l] at * <;> omega

theorem physical_joint_lift (k : ℕ) (hk : 8 ≤ k)
    (w : List (Fin (k + 1))) (hw : JointWord k w) :
    JointWord (k + 8) (physicalLiftWord w (adaptiveOrientation k hk w)) ∧
      insertionDeletion (physicalLiftWord w (adaptiveOrientation k hk w)) = w := by
  let o := adaptiveOrientation k hk w
  have hsums := physical_word_sums k hk w o
  have hcharge : (w.map (fullCharge k)).sum = 85 := by
    rw [(hw.1.map _).sum_eq, full_charge_total k hk]
  have hear : (w.map earIndicator).sum = 1 := by
    rw [(hw.1.map _).sum_eq, indicator_total k]
  have hlow : (w.map lowWeight).sum = 255 := by
    rw [(hw.1.map _).sum_eq, low_weight_total k hk]
  have htotal : firstState w = 0 ∧ secondState w = 0 := by
    simp [firstState, secondState, hw.2.1, hw.2.2.1, hcharge, hear, hlow]
  have hprefix : ∀ n, n ≤ w.length →
      InStrip (fullFirst (k + 8)) (targetH k) 0 (physicalLiftWord (w.take n) o) ∧
      InStrip (actualSource (k + 9) 170) (targetN k) 0 (physicalLiftWord (w.take n) o) := by
    intro n
    induction n with
    | zero =>
        intro _
        have h := canonical_complete_prefix k hk w hw 0
        simpa [physicalLiftWord, InStrip, firstState, secondState] using
          (show (0 ≤ firstState (w.take 0) ∧ firstState (w.take 0) ≤ targetH k) ∧
            (0 ≤ secondState (w.take 0) ∧ secondState (w.take 0) ≤ targetN k) from
            ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2.1⟩)
    | succ n ih =>
        intro hn
        have hn' : n < w.length := by omega
        have hh := ih (by omega)
        have hb := adaptive_block_strip k hk w hw n hn'
        have ht := List.take_succ_eq_append_getElem hn'
        rw [ht]
        simp only [physicalLiftWord, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
        change InStrip _ _ 0 (physicalLiftWord (w.take n) o ++ physicalBlock o w[n]) ∧
          InStrip _ _ 0 (physicalLiftWord (w.take n) o ++ physicalBlock o w[n])
        have hsum := physical_word_sums k hk (w.take n) o
        constructor
        · apply inStrip_append hh.1
          simpa only [zero_add, hsum.1] using hb.1
        · apply inStrip_append hh.2
          simpa only [zero_add, hsum.2] using hb.2
  have hstrip := hprefix w.length (by omega)
  rw [List.take_length] at hstrip
  refine ⟨⟨physical_inventory k hk w hw.1 o, ?_, ?_, ?_⟩,
    insertionDeletion_physicalLiftWord w o⟩
  · rw [hsums.1, htotal.1]
  · rw [hsums.2, htotal.2]
  · intro n
    have hx := inStrip_prefix hstrip.1 n
    have hy := inStrip_prefix hstrip.2 n
    rw [(target_double k hk).2] at hx
    exact ⟨by simpa using hx.1, by simpa using hx.2,
      by simpa using hy.1, by simpa [targetN] using hy.2⟩

end D5.S3.Combinatorics.Circle.FourNegative.EightBitPhysicalLift
