/- GID: D5/S3/Combinatorics/Circle/FourNegative/ResonantUniversalInsertionSchedule
   generality: I
   mirror-B: none(waiver:universal-resonant-source)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Generic target endpoints and canonical prefix states for resonant insertion. -/
import D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertionPrefix

/-! # Canonical endpoints of resonant insertion blocks -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion

open SourceWidth PeriodicShortening PeriodicShorteningArithmetic
open RunFirstEarTransport
open scoped BigOperators

def resonantHighWeight {k ell : ℕ} (j : Fin (k + 1)) : ℤ :=
  Fin.lastCases 0 (fun i => if i.val < ell then 0 else (2 : ℤ) ^ (i.val - ell)) j

theorem resonant_weight_decomposition {k ell m : ℕ}
    (hm : m = 2 ^ ell) (hkl : ell ≤ k) (j : Fin (k + 1)) :
    resonantWeight k j = resonantLowWeight (ell := ell) j +
      (m : ℤ) * resonantHighWeight (ell := ell) j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [resonantWeight, resonantLowWeight, resonantHighWeight, hkl]
  · by_cases h : i.val < ell
    · simp [resonantWeight, resonantLowWeight, resonantHighWeight, h]
    · have hpow : (2 : ℤ) ^ i.val = (m : ℤ) * (2 : ℤ) ^ (i.val - ell) := by
        rw [show i.val = (i.val - ell) + ell by omega, pow_add]
        norm_num [hm]
        ring
      simp only [resonantWeight, resonantLowWeight, resonantHighWeight,
        Fin.lastCases_castSucc, Fin.val_castSucc, h, if_false]
      rw [hpow]
      ring

theorem resonant_prefix_weight_decomposition {k ell m : ℕ}
    (hm : m = 2 ^ ell) (hkl : ell ≤ k) (l : List (Fin (k + 1))) :
    (l.map (resonantWeight k)).sum =
      (l.map (resonantLowWeight (ell := ell))).sum +
        (m : ℤ) * (l.map (resonantHighWeight (ell := ell))).sum := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [resonant_weight_decomposition hm hkl j, ih]
    ring

theorem resonant_old_modulus_half {k : ℕ} (hk : 2 ≤ k) :
    modulus k / 2 = (2 : ℤ) ^ (k - 1) - 1 := by
  have hp : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
    calc
      (2 : ℤ) ^ k = 2 ^ ((k - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (k - 1) := by ring
  unfold modulus
  rw [hp]
  omega

theorem resonant_target_values {ell k m : ℕ}
    (hell : 1 ≤ ell) (hm : m = 2 ^ ell) (hkl : ell ≤ k) :
    ∃ B : ℤ, (m : ℤ) = 2 * B ∧
      resonantTargetH k ell = (m : ℤ) * (2 : ℤ) ^ (k - 1) - 1 ∧
      resonantTargetN k ell = 2 * (m : ℤ) * (2 : ℤ) ^ (k - 1) - 1 := by
  let B : ℤ := (2 : ℤ) ^ (ell - 1)
  have hmB : (m : ℤ) = 2 * B := by
    dsimp [B]
    rw [hm, show ell = (ell - 1) + 1 by omega, pow_succ]
    norm_num
    ring
  have hp : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
    calc
      (2 : ℤ) ^ k = 2 ^ ((k - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (k - 1) := by ring
  have hmk : modulus k = 2 * (2 : ℤ) ^ (k - 1) - 1 := by
    unfold modulus
    rw [hp]
  have htarget := resonance_target_modulus (k := k) (ell := ell) (m := m) hm
  refine ⟨B, hmB, ?_, ?_⟩
  · unfold resonantTargetH
    rw [htarget, hmk, hmB]
    have hid : 2 * B * (2 * (2 : ℤ) ^ (k - 1) - 1 + 1) - 1 =
        2 * (2 * B * (2 : ℤ) ^ (k - 1) - 1) + 1 := by ring
    rw [hid]
    omega
  · unfold resonantTargetN
    rw [htarget, hmk]
    ring

/-- Every legal source prefix reaches a legal canonical target endpoint. -/
theorem resonant_canonical_complete_prefix {w ell k m : ℕ}
    (hw : 1 ≤ w) (hell : 1 ≤ ell) (hm : m = 2 ^ ell)
    (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m) (hkl : ell ≤ k)
    (word : List (Fin (k + 1))) (hsource : resonantSourceWord k w word) (n : ℕ) :
    0 ≤ resonantFirstState k ell w m (word.take n) ∧
      resonantFirstState k ell w m (word.take n) ≤ resonantTargetH k ell ∧
      0 ≤ resonantSecondState k ell w m (word.take n) ∧
      resonantSecondState k ell w m (word.take n) ≤ resonantTargetN k ell := by
  obtain ⟨hell2, hk2, hwpos, hwodd, hroom⟩ :=
    resonant_hypotheses_facts hw hell hm hdiv hlarge hkl
  let l := word.take n
  let F : ℤ := (l.map (resonantFirst k w)).sum
  let Y : ℤ := (l.map (actualSource (k + 1) (2 * w))).sum
  let C : ℤ := (l.map (resonantCharge k w)).sum
  let T : ℤ := (l.map (resonantWeight k)).sum
  let u : ℤ := (l.map (resonantLowWeight (ell := ell))).sum
  let b : ℤ := (l.map (resonantEar k)).sum
  have hn := resonant_prefix_normal_form hell hm hw hdiv hlarge hroom hk2 word
    hsource.1 n hkl
  change F = (w : ℤ) * T - modulus k * C ∧
    Y = 2 * F - C + (w : ℤ) * b ∧
    0 ≤ C ∧ C ≤ (w : ℤ) ∧ 0 ≤ b ∧ b ≤ 1 ∧
    0 ≤ u ∧ u ≤ (m : ℤ) - 1 at hn
  rcases hn with ⟨hFrel, hYrel, hC0, hCw, hb0, hb1, hu0, huMax⟩
  have hbaseRange := hsource.2.2.2 n
  have hF : 0 ≤ F ∧ F ≤ (modulus k) / 2 := ⟨hbaseRange.1, hbaseRange.2.1⟩
  have hY : 0 ≤ Y ∧ Y ≤ modulus k := ⟨hbaseRange.2.2.1, hbaseRange.2.2.2⟩
  have hC : 0 ≤ C ∧ C ≤ (w : ℤ) := ⟨hC0, hCw⟩
  have hb : b = 0 ∨ b = 1 := by
    by_cases hb0 : b = 0
    · exact Or.inl hb0
    · right
      omega
  have hrel : Y = 2 * F - C + (w : ℤ) * b := hYrel
  have hstateX : resonantFirstState k ell w m l =
      (m : ℤ) * F - (m - 1 : ℕ) * C + (w : ℤ) * u := by
    simp [resonantFirstState, F, C, u]
  have hstateZ : resonantSecondState k ell w m l =
      (m : ℤ) * Y - (m - 1 : ℕ) * C - (w : ℤ) * (m - 1 : ℕ) * b +
        (2 * w : ℤ) * u := by
    simp [resonantSecondState, Y, C, b, u]
  obtain ⟨B, hmB, htargetH, htargetN⟩ := resonant_target_values hell hm hkl
  have hmodhalf : modulus k / 2 = (2 : ℤ) ^ (k - 1) - 1 := resonant_old_modulus_half hk2
  rw [hmodhalf] at hF
  by_cases hkeq : k = ell
  · subst k
    have hBpow : B = (2 : ℤ) ^ (ell - 1) := by
      have hmPow : (m : ℤ) = 2 * (2 : ℤ) ^ (ell - 1) := by
        rw [hm, show ell = (ell - 1) + 1 by omega, pow_succ]
        norm_num
        ring
      nlinarith [hmB, hmPow]
    have hweightlow : T = u := by
      have h := resonant_prefix_weight_decomposition hm (by omega : ell ≤ ell) l
      have hz : (l.map (resonantHighWeight (ell := ell))).sum = 0 := by
        induction l with
        | nil => simp
        | cons j l ih =>
          have hj : resonantHighWeight (ell := ell) j = 0 := by
            refine Fin.lastCases ?_ (fun i => ?_) j
            · simp [resonantHighWeight]
            · have hi : i.val < ell := i.isLt
              simp [resonantHighWeight, hi]
          simp only [List.map_cons, List.sum_cons, hj, ih, zero_add]
      simpa [T, u] using h.trans (by simp [hz])

    have hbase : F = (w : ℤ) * T - ((m : ℤ) - 1) * C := by
      simpa [l, F, T, C, modulus, hm, List.map_take] using hFrel
    have hF' : 0 ≤ F ∧ F ≤ ((m : ℤ) - 2) / 2 := by
      have heq : ((m : ℤ) - 2) / 2 = B - 1 := by omega
      rw [heq, hBpow]
      exact hF
    have hBhalf : (m : ℤ) = 2 * B := hmB
    have hqNat := resonance_quotient_ge_three hw hdiv hlarge
    have hqOddNat : Odd ((m - 1) / w) := by
      have hprod := resonance_quotient_mul hwpos hdiv
      have hoddm : Odd (m - 1) := by
        rw [hm]
        have he : ell = (ell - 1) + 1 := by omega
        rw [he, pow_succ]
        exact ⟨2 ^ (ell - 1) - 1, by omega⟩
      have hoddprod : Odd (w * ((m - 1) / w)) := by
        have hprod' : w * ((m - 1) / w) = m - 1 := by
          simpa [resonanceQuotient] using hprod
        rw [hprod']
        exact hoddm
      exact Nat.Odd.of_mul_right hoddprod
    have hend := resonant_boundary_endpoint (w := (w : ℤ)) (ell := (ell : ℤ))
      (m := (m : ℤ)) (q := (((m - 1) / w : ℕ) : ℤ)) B F Y C u T b
      (by
        have hqNat : w * ((m - 1) / w) = m - 1 := by
          simpa [resonanceQuotient] using resonance_quotient_mul hwpos hdiv
        have hq' : (w : ℤ) * (((m - 1) / w : ℕ) : ℤ) = (m : ℤ) - 1 := by
          rw [show (m : ℤ) - 1 = ((m - 1 : ℕ) : ℤ) by omega]
          exact_mod_cast hqNat
        omega)
      hBhalf (Odd.natCast hqOddNat) (by exact_mod_cast hqNat)
      (by exact_mod_cast hwpos) hF'
      (by simpa [modulus, hm] using hY) hC hb hweightlow.symm hbase hrel
    have hstateX' := hstateX
    have hstateZ' := hstateZ
    norm_num [Nat.cast_sub (by omega : 1 ≤ m)] at hstateX' hstateZ'
    have hbase_u : F = (w : ℤ) * u - ((m : ℤ) - 1) * C := by
      simpa [hweightlow] using hbase
    have hx : resonantFirstState ell ell w m l = ((m : ℤ) + 1) * F := by
      calc
        resonantFirstState ell ell w m l =
            (m : ℤ) * F - ((m : ℤ) - 1) * C + (w : ℤ) * u := hstateX'
        _ = ((m : ℤ) + 1) * F := by rw [hbase_u]; ring
    have hz : resonantSecondState ell ell w m l = Y + 2 * (m : ℤ) * F := by
      calc
        resonantSecondState ell ell w m l =
            (m : ℤ) * Y - ((m : ℤ) - 1) * C - (w : ℤ) * ((m : ℤ) - 1) * b +
              (2 * w : ℤ) * u := hstateZ'
        _ = Y + 2 * (m : ℤ) * F := by rw [hrel, hbase_u]; ring
    rw [hx, hz, htargetH, htargetN]
    exact ⟨hend.1, by simpa [hBpow] using hend.2.1,
      hend.2.2.1, by simpa [hBpow] using hend.2.2.2⟩
  · have hkle : ell + 1 ≤ k := by omega
    let S : ℤ := (2 : ℤ) ^ (k - ell - 1)
    have hBS : (2 : ℤ) ^ (k - 1) = (m : ℤ) * S := by
      dsimp [S]
      rw [show k - 1 = ell + (k - ell - 1) by omega, pow_add]
      norm_num [hm]
    have hdecomp := resonant_prefix_weight_decomposition hm hkl l
    let Q : ℤ := (l.map (resonantHighWeight (ell := ell))).sum
    have hT : T = u + (m : ℤ) * Q := by simpa [Q] using hdecomp
    have hmk : modulus k = 2 * (2 : ℤ) ^ (k - 1) - 1 := by
      have hpowk : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
        calc
          (2 : ℤ) ^ k = 2 ^ ((k - 1) + 1) := by congr 1 <;> omega
          _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (k - 1) := by ring
      unfold modulus
      rw [hpowk]
    have hbase : F = (w : ℤ) * T - (2 * (2 : ℤ) ^ (k - 1) - 1) * C := by
      rw [← hmk]
      simpa [l, F, T, C, List.map_take] using hFrel
    let q : ℤ := ((m - 1) / w : ℕ)
    have hmq : (m : ℤ) = 1 + (w : ℤ) * q := by
      have hqNat : w * ((m - 1) / w) = m - 1 := by
        simpa [resonanceQuotient] using resonance_quotient_mul hwpos hdiv
      have hq' : (w : ℤ) * q = (m : ℤ) - 1 := by
        dsimp [q]
        rw [show (m : ℤ) - 1 = ((m - 1 : ℕ) : ℤ) by omega]
        exact_mod_cast hqNat
      omega

    let r : ℤ := u + ((m : ℤ) - 1) * Q - 2 * q * S * C
    have hquot : (m : ℤ) * r = u + q * (F - C) := by
      dsimp [r]
      rw [hbase, hT, hBS]
      rw [hmq]
      ring
    have hqpos : 0 < q := by
      dsimp [q]
      have hq3 : 3 ≤ (m - 1) / w := by
        simpa [resonanceQuotient] using resonance_quotient_ge_three hw hdiv hlarge
      exact_mod_cast (by omega : 0 < (m - 1) / w)
    have hS : 0 ≤ S := by positivity
    have hend := resonant_quotient_bound (m := (m : ℤ)) (w := (w : ℤ)) q
      ((2 : ℤ) ^ (k - 1)) S F C u T Q r hmq hBS hqpos
      (by rw [hm]; positivity) hF hC
      (by
        constructor
        · exact hu0
        · have hu_le := huMax
          omega)
      hT hbase hquot
    have hY' : 0 ≤ Y ∧ Y ≤ 2 * (2 : ℤ) ^ (k - 1) - 1 := by
      have hmk : modulus k = 2 * (2 : ℤ) ^ (k - 1) - 1 := by
        have hpowk : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by
          calc
            (2 : ℤ) ^ k = 2 ^ ((k - 1) + 1) := by congr 1 <;> omega
            _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
            _ = 2 * 2 ^ (k - 1) := by ring
        unfold modulus
        rw [hpowk]
      rw [hmk] at hY
      exact hY
    have hstateX' := hstateX
    have hstateZ' := hstateZ
    norm_num [Nat.cast_sub (by omega : 1 ≤ m)] at hstateX' hstateZ'
    have hcan := resonant_canonical_endpoint (w := (w : ℤ)) (ell := (ell : ℤ))
      (k := (k : ℤ)) (m := (m : ℤ)) q ((2 : ℤ) ^ (k - 1)) S F Y C u b r
      (resonantFirstState k ell w m l) (resonantSecondState k ell w m l)
      hmq hBS (by rw [hm]; positivity) (by exact_mod_cast hwpos) hqpos hF hY' hC
      (by
        constructor
        · exact hu0
        · have hu_le := huMax
          omega) hb hrel hend hquot hstateX' hstateZ'
    rw [htargetH, htargetN]
    simpa [l] using hcan

/-- Either orientation of a physical block has the same two endpoint increments. -/
theorem resonant_block_sums {w ell k m : ℕ}
    (hw : 1 ≤ w) (hell : 1 ≤ ell) (hm : m = 2 ^ ell)
    (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m) (hkl : ell ≤ k)
    (orientation : Fin ell → Bool) (j : Fin (k + 1)) :
    ((resonantBlock orientation j).map (resonantTargetFirst k ell w)).sum =
      (m : ℤ) * resonantFirst k w j - (m - 1 : ℕ) * resonantCharge k w j +
        (w : ℤ) * resonantLowWeight (ell := ell) j ∧
    ((resonantBlock orientation j).map (resonantTargetSecond k ell w)).sum =
      (m : ℤ) * actualSource (k + 1) (2 * w) j -
        (m - 1 : ℕ) * resonantCharge k w j -
        (w : ℤ) * (m - 1 : ℕ) * resonantEar k j +
        (2 * w : ℤ) * resonantLowWeight (ell := ell) j := by
  obtain ⟨_, hk, _, _, hroom⟩ := resonant_hypotheses_facts hw hell hm hdiv hlarge hkl
  have hold := resonant_target_old_rows hell hm hw hdiv hlarge hroom hk hkl j
  by_cases hj : j.val < ell
  · have hnew := resonant_target_new_rows hell hm hroom hk ⟨j.val, hj⟩
    simp only [resonantBlock, dif_pos hj]
    split_ifs with ho
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, hold.1, hold.2, hnew.1, hnew.2, resonantLowWeight,
        if_pos hj, Fin.val_mk]
      constructor <;> trivial
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, hold.1, hold.2, hnew.1, hnew.2, resonantLowWeight,
        if_pos hj, Fin.val_mk]
      constructor <;> rw [add_comm]
  · have hlow : resonantLowWeight (ell := ell) j = 0 := by
      simp [resonantLowWeight, hj]
    simp [resonantBlock, hj, hlow, hold.1, hold.2]

/-- The actual lifted-word sums equal the canonical states, independently of orientation. -/
theorem resonant_liftWord_states {w ell k m : ℕ}
    (hw : 1 ≤ w) (hell : 1 ≤ ell) (hm : m = 2 ^ ell)
    (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m) (hkl : ell ≤ k)
    (word : List (Fin (k + 1))) (orientation : Fin ell → Bool) :
    ((resonantLiftWord word orientation).map (resonantTargetFirst k ell w)).sum =
      resonantFirstState k ell w m word ∧
    ((resonantLiftWord word orientation).map (resonantTargetSecond k ell w)).sum =
      resonantSecondState k ell w m word := by
  induction word with
  | nil => simp [resonantLiftWord, resonantFirstState, resonantSecondState]
  | cons j word ih =>
    change (((resonantBlock orientation j) ++ resonantLiftWord word orientation).map _).sum = _ ∧
      (((resonantBlock orientation j) ++ resonantLiftWord word orientation).map _).sum = _
    simp only [List.map_append, List.sum_append, ih.1, ih.2]
    rw [(resonant_block_sums hw hell hm hdiv hlarge hkl orientation j).1,
      (resonant_block_sums hw hell hm hdiv hlarge hkl orientation j).2]
    simp only [resonantFirstState, resonantSecondState, List.map_cons, List.sum_cons]
    constructor <;> ring

/-- A complete physical block prefix ends in both target strips for every orientation. -/
theorem resonant_complete_block_prefix {w ell k m : ℕ}
    (hw : 1 ≤ w) (hell : 1 ≤ ell) (hm : m = 2 ^ ell)
    (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m) (hkl : ell ≤ k)
    (word : List (Fin (k + 1))) (hsource : resonantSourceWord k w word)
    (n : ℕ) (orientation : Fin ell → Bool) :
    let targetPrefix := resonantLiftWord (word.take n) orientation
    0 ≤ (targetPrefix.map (resonantTargetFirst k ell w)).sum ∧
      (targetPrefix.map (resonantTargetFirst k ell w)).sum ≤ resonantTargetH k ell ∧
      0 ≤ (targetPrefix.map (resonantTargetSecond k ell w)).sum ∧
      (targetPrefix.map (resonantTargetSecond k ell w)).sum ≤ resonantTargetN k ell := by
  dsimp only
  have hstates := resonant_liftWord_states hw hell hm hdiv hlarge hkl (word.take n) orientation
  rw [hstates.1, hstates.2]
  exact resonant_canonical_complete_prefix hw hell hm hdiv hlarge hkl word hsource n

end D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion
