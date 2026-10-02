/- GID: D5/S3/QuantumBounds/SliwaSevenArbitraryOutcomeLocalBound
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/SliwaSevenArbitraryOutcomeLocalBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The local bound of the arbitrary-output Sliwa seventh inequality is 6(K-1). -/
/-
proof_shape: result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#12317; Proved)
Direct frozen dependencies: none (pinned Mathlib only)
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuantumBounds.SliwaSevenArbitraryOutcomeLocalBound

/-- The twelve-term deterministic expression of Appendix B, inequality (B1). -/
def J (K : ℕ) (a b c A B C : ZMod K) : ℕ :=
  let S := a + b + c
  let T := A + B + C
  2 * S.val + 2 * (-S - 1).val + (-S).val +
    3 * (-T - 1).val + (T - 1).val + T.val +
    (-A + b + c).val + (-B + a + c).val + (-C + a + b).val +
    (-a + B + C).val + (-b + A + C).val + (-c + A + B).val

/-- Only the local-bound clause of the source conjecture. -/
def claim : Prop := ∀ K : ℕ, 2 ≤ K →
  IsLeast {J K a b c A B C | (a : ZMod K) (b : ZMod K) (c : ZMod K)
    (A : ZMod K) (B : ZMod K) (C : ZMod K)} (6 * (K - 1))

theorem result : claim := by
  intro K hK
  have hK0 : K ≠ 0 := by omega
  have : NeZero K := ⟨hK0⟩
  have hmone : (-1 : ZMod K).val = K - 1 := by
    cases K with
    | zero => omega
    | succ k => exact ZMod.val_neg_one k
  constructor
  · refine ⟨0, 0, 0, 0, 0, 0, ?_⟩
    simp only [J, add_zero, neg_zero, zero_sub, ZMod.val_zero, hmone]
    omega
  · rintro z ⟨a, b, c, A, B, C, rfl⟩
    let k : ℤ := K
    let S := a + b + c
    let T := A + B + C
    let U := -A + b + c
    let V := -B + a + c
    let W := -C + a + b
    let s : ℤ := S.val
    let t : ℤ := T.val
    let u : ℤ := U.val
    let v : ℤ := V.val
    let w : ℤ := W.val
    have hk : 0 < k := by dsimp [k]; omega
    have bounds (x : ZMod K) : 0 ≤ (x.val : ℤ) ∧ (x.val : ℤ) < k :=
      ⟨by omega, by dsimp only [k]; exact_mod_cast ZMod.val_lt x⟩
    have hs := bounds S
    have ht := bounds T
    have hu := bounds U
    have hv := bounds V
    have hw := bounds W
    have residue (x : ZMod K) (r : ℤ) (hr : (r : ZMod K) = x) :
        (x.val : ℤ) = r % k := by
      dsimp only [k]
      rw [← hr, ZMod.val_intCast]
    have hcast : ((u + v + w - 2 * s + t : ℤ) : ZMod K) = 0 := by
      dsimp only [u, v, w, s, t]
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id]
      dsimp only [U, V, W, S, T]
      ring
    obtain ⟨q, hq⟩ := (ZMod.intCast_eq_iff K (u + v + w - 2 * s + t) 0).mp hcast
    simp only [ZMod.val_zero, Int.natCast_zero, zero_add] at hq
    have hU : u + v + w = 2 * s - t + k * q := by
      dsimp only [k]
      linarith only [hq]
    have mixedA : ((-a + B + C).val : ℤ) = (u + t - s) % k := by
      apply residue
      dsimp only [u, t, s]
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id]
      dsimp only [U, T, S]
      ring
    have mixedB : ((-b + A + C).val : ℤ) = (v + t - s) % k := by
      apply residue
      dsimp only [v, t, s]
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id]
      dsimp only [V, T, S]
      ring
    have mixedC : ((-c + A + B).val : ℤ) = (w + t - s) % k := by
      apply residue
      dsimp only [w, t, s]
      push_cast
      simp only [ZMod.natCast_val, ZMod.cast_id]
      dsimp only [W, T, S]
      ring
    have neg_pred (x : ZMod K) : ((-x - 1).val : ℤ) = k - 1 - x.val := by
      have h := bounds x
      have hc : ((-(x.val : ℤ) - 1 : ℤ) : ZMod K) = -x - 1 := by
        push_cast
        rw [ZMod.natCast_val, ZMod.cast_id]
      rw [residue _ _ hc]
      calc (-(x.val : ℤ) - 1) % k = (k - 1 - x.val) % k := by
             have he : -(x.val : ℤ) - 1 = (k - 1 - x.val) + k * (-1) := by ring
             conv_lhs => rw [he, Int.add_mul_emod_self_left]
           _ = k - 1 - x.val := Int.emod_eq_of_lt (by omega) (by omega)
    have neg_val : ((-S).val : ℤ) = if s = 0 then 0 else k - s := by
      have hc : ((-s : ℤ) : ZMod K) = -S := by
        dsimp [s]; push_cast; rw [ZMod.natCast_val, ZMod.cast_id]
      rw [residue _ _ hc]
      split_ifs with hs0
      · simp only [hs0, neg_zero, Int.zero_emod]
      · calc (-s) % k = (k - s) % k := by
               have he : -s = (k - s) + k * (-1) := by ring
               conv_lhs => rw [he, Int.add_mul_emod_self_left]
             _ = k - s := Int.emod_eq_of_lt (by omega) (by omega)
    have pred_val : ((T - 1).val : ℤ) = if t = 0 then k - 1 else t - 1 := by
      have hc : ((t - 1 : ℤ) : ZMod K) = T - 1 := by
        dsimp [t]; push_cast; rw [ZMod.natCast_val, ZMod.cast_id]
      rw [residue _ _ hc]
      split_ifs with ht0
      · rw [ht0]
        calc (0 - 1 : ℤ) % k = (k - 1) % k := by
               have he : (0 - 1 : ℤ) = (k - 1) + k * (-1) := by ring
               conv_lhs => rw [he, Int.add_mul_emod_self_left]
             _ = k - 1 := Int.emod_eq_of_lt (by omega) (by omega)
      · exact Int.emod_eq_of_lt (by omega) (by omega)
    let L := u + v + w + (u + t - s) % k + (v + t - s) % k + (w + t - s) % k
    have mixed_residue_bound (k s t u v w q : ℤ)
        (hk : 0 < k) (hs : 0 ≤ s ∧ s < k) (ht : 0 ≤ t ∧ t < k)
        (hu : 0 ≤ u ∧ u < k) (hv : 0 ≤ v ∧ v < k) (hw : 0 ≤ w ∧ w < k)
        (hU : u + v + w = 2 * s - t + k * q) :
        s + t ≤ u + v + w + (u + t - s) % k + (v + t - s) % k + (w + t - s) % k ∧
        (s = 0 → 0 < t → s + t + k ≤
          u + v + w + (u + t - s) % k + (v + t - s) % k + (w + t - s) % k) := by
      by_cases hst : s ≤ t
      · have wrap (x : ℤ) (hx : 0 ≤ x ∧ x < k) :
            (x + t - s) % k = if k ≤ x + t - s then x + t - s - k else x + t - s := by
          split_ifs with h
          · have he : x + t - s = (x + t - s - k) + k * 1 := by ring
            calc (x + t - s) % k = (x + t - s - k) % k := by
                   conv_lhs => rw [he, Int.add_mul_emod_self_left]
                 _ = x + t - s - k := Int.emod_eq_of_lt (by omega) (by omega)
          · exact Int.emod_eq_of_lt (by omega) (by omega)
        rw [wrap u hu, wrap v hv, wrap w hw]
        by_cases h1 : k ≤ u + t - s <;>
          by_cases h2 : k ≤ v + t - s <;>
          by_cases h3 : k ≤ w + t - s
        all_goals simp only [h1, h2, h3, if_true, if_false]
        · have hq : 2 ≤ q := by
            by_contra hn
            have hn' : q ≤ 1 := by omega
            have hm := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
            nlinarith only [hU, hu.1, hv.1, hw.1, hs.1, hs.2, ht.1, ht.2, hk, hst, h1, h2, h3, hm]
          have hm := mul_le_mul_of_nonneg_left hq (le_of_lt hk)
          constructor
          · nlinarith only [hU, hm, hk]
          · intro hs0 ht0
            nlinarith only [hU, hm, hk]
        · have hq : 2 ≤ q := by
            by_contra hn
            have hn' : q ≤ 1 := by omega
            have hm := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
            nlinarith only [hU, hu.1, hv.1, hw.1, hs.1, hs.2, ht.1, ht.2, hk, hst, h1, h2, h3, hm]
          have hm := mul_le_mul_of_nonneg_left hq (le_of_lt hk)
          constructor
          · nlinarith only [hU, hm, hk]
          · intro hs0 ht0
            nlinarith only [hU, hm, hk]
        · have hq : 2 ≤ q := by
            by_contra hn
            have hn' : q ≤ 1 := by omega
            have hm := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
            nlinarith only [hU, hu.1, hv.1, hw.1, hs.1, hs.2, ht.1, ht.2, hk, hst, h1, h2, h3, hm]
          have hm := mul_le_mul_of_nonneg_left hq (le_of_lt hk)
          constructor
          · nlinarith only [hU, hm, hk]
          · intro hs0 ht0
            nlinarith only [hU, hm, hk]
        · have hq : 1 ≤ q := by
            by_contra hn
            have hn' : q ≤ 0 := by omega
            have hm := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
            nlinarith only [hU, hu.1, hv.1, hw.1, hs.1, hs.2, ht.1, ht.2, hk, hst, h1, h2, h3, hm]
          have hm := mul_le_mul_of_nonneg_left hq (le_of_lt hk)
          constructor
          · nlinarith only [hU, hm, hk]
          · intro hs0 ht0
            nlinarith only [hU, hm, hk]
        · have hq : 2 ≤ q := by
            by_contra hn
            have hn' : q ≤ 1 := by omega
            have hm := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
            nlinarith only [hU, hu.1, hv.1, hw.1, hs.1, hs.2, ht.1, ht.2, hk, hst, h1, h2, h3, hm]
          have hm := mul_le_mul_of_nonneg_left hq (le_of_lt hk)
          constructor
          · nlinarith only [hU, hm, hk]
          · intro hs0 ht0
            nlinarith only [hU, hm, hk]
        · have hq : 1 ≤ q := by
            by_contra hn
            have hn' : q ≤ 0 := by omega
            have hm := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
            nlinarith only [hU, hu.1, hv.1, hw.1, hs.1, hs.2, ht.1, ht.2, hk, hst, h1, h2, h3, hm]
          have hm := mul_le_mul_of_nonneg_left hq (le_of_lt hk)
          constructor
          · nlinarith only [hU, hm, hk]
          · intro hs0 ht0
            nlinarith only [hU, hm, hk]
        · have hq : 1 ≤ q := by
            by_contra hn
            have hn' : q ≤ 0 := by omega
            have hm := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
            nlinarith only [hU, hu.1, hv.1, hw.1, hs.1, hs.2, ht.1, ht.2, hk, hst, h1, h2, h3, hm]
          have hm := mul_le_mul_of_nonneg_left hq (le_of_lt hk)
          constructor
          · nlinarith only [hU, hm, hk]
          · intro hs0 ht0
            nlinarith only [hU, hm, hk]
        · have hq : 0 ≤ q := by
            by_contra hn
            have hn' : q ≤ -1 := by omega
            have hm := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
            nlinarith only [hU, hu.1, hv.1, hw.1, hs.1, hs.2, ht.1, ht.2, hk, hst, h1, h2, h3, hm]
          have hm := mul_le_mul_of_nonneg_left hq (le_of_lt hk)
          constructor
          · nlinarith only [hU, hm, hk]
          · intro hs0 ht0
            have hq1 : 1 ≤ q := by
              by_contra hn
              have hn' : q ≤ 0 := by omega
              have hm' := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
              nlinarith only [hU, hu.1, hv.1, hw.1, hs0, ht0, hm']
            have hm' := mul_le_mul_of_nonneg_left hq1 (le_of_lt hk)
            nlinarith only [hU, hm', hk]
      · have hts : t < s := by omega
        have wrap (x : ℤ) (hx : 0 ≤ x ∧ x < k) :
            (x + t - s) % k = if x < s - t then x + t - s + k else x + t - s := by
          split_ifs with h
          · have he : x + t - s = (x + t - s + k) + k * (-1) := by ring
            calc (x + t - s) % k = (x + t - s + k) % k := by
                   conv_lhs => rw [he, Int.add_mul_emod_self_left]
                 _ = x + t - s + k := Int.emod_eq_of_lt (by omega) (by omega)
          · exact Int.emod_eq_of_lt (by omega) (by omega)
        rw [wrap u hu, wrap v hv, wrap w hw]
        by_cases h1 : u < s - t <;>
          by_cases h2 : v < s - t <;>
          by_cases h3 : w < s - t
        all_goals simp only [h1, h2, h3, if_true, if_false]
        · have hq : -1 ≤ q := by
            by_contra hn
            have hn' : q ≤ -2 := by omega
            have hm := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
            nlinarith only [hU, hu.1, hv.1, hw.1, hs.1, hs.2, ht.1, ht.2, hk, h1, h2, h3, hm]
          have hm := mul_le_mul_of_nonneg_left hq (le_of_lt hk)
          constructor
          · nlinarith only [hU, hm, hk]
          · intro hs0 ht0
            omega
        · have hq : 0 ≤ q := by
            by_contra hn
            have hn' : q ≤ -1 := by omega
            have hm := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
            nlinarith only [hU, hu.1, hv.1, hw.1, hs.1, hs.2, ht.1, ht.2, hk, h1, h2, h3, hm]
          have hm := mul_le_mul_of_nonneg_left hq (le_of_lt hk)
          constructor
          · nlinarith only [hU, hm, hk]
          · intro hs0 ht0
            omega
        · have hq : 0 ≤ q := by
            by_contra hn
            have hn' : q ≤ -1 := by omega
            have hm := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
            nlinarith only [hU, hu.1, hv.1, hw.1, hs.1, hs.2, ht.1, ht.2, hk, h1, h2, h3, hm]
          have hm := mul_le_mul_of_nonneg_left hq (le_of_lt hk)
          constructor
          · nlinarith only [hU, hm, hk]
          · intro hs0 ht0
            omega
        · have hq : 0 ≤ q := by
            by_contra hn
            have hn' : q ≤ -1 := by omega
            have hm := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
            nlinarith only [hU, hu.1, hv.1, hw.1, hs.1, hs.2, ht.1, ht.2, hk, h1, h2, h3, hm]
          have hm := mul_le_mul_of_nonneg_left hq (le_of_lt hk)
          constructor
          · nlinarith only [hU, hm, hk]
          · intro hs0 ht0
            omega
        · have hq : 0 ≤ q := by
            by_contra hn
            have hn' : q ≤ -1 := by omega
            have hm := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
            nlinarith only [hU, hu.1, hv.1, hw.1, hs.1, hs.2, ht.1, ht.2, hk, h1, h2, h3, hm]
          have hm := mul_le_mul_of_nonneg_left hq (le_of_lt hk)
          constructor
          · nlinarith only [hU, hm, hk]
          · intro hs0 ht0
            omega
        · have hq : 0 ≤ q := by
            by_contra hn
            have hn' : q ≤ -1 := by omega
            have hm := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
            nlinarith only [hU, hu.1, hv.1, hw.1, hs.1, hs.2, ht.1, ht.2, hk, h1, h2, h3, hm]
          have hm := mul_le_mul_of_nonneg_left hq (le_of_lt hk)
          constructor
          · nlinarith only [hU, hm, hk]
          · intro hs0 ht0
            omega
        · have hq : 0 ≤ q := by
            by_contra hn
            have hn' : q ≤ -1 := by omega
            have hm := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
            nlinarith only [hU, hu.1, hv.1, hw.1, hs.1, hs.2, ht.1, ht.2, hk, h1, h2, h3, hm]
          have hm := mul_le_mul_of_nonneg_left hq (le_of_lt hk)
          constructor
          · nlinarith only [hU, hm, hk]
          · intro hs0 ht0
            omega
        · have hq : 0 ≤ q := by
            by_contra hn
            have hn' : q ≤ -1 := by omega
            have hm := mul_le_mul_of_nonneg_left hn' (le_of_lt hk)
            nlinarith only [hU, hu.1, hv.1, hw.1, hs.1, hs.2, ht.1, ht.2, hk, h1, h2, h3, hm]
          have hm := mul_le_mul_of_nonneg_left hq (le_of_lt hk)
          constructor
          · nlinarith only [hU, hm, hk]
          · intro hs0 ht0
            omega

    have hL := mixed_residue_bound k s t u v w q hk hs ht hu hv hw hU
    change s + t ≤ L ∧ (s = 0 → 0 < t → s + t + k ≤ L) at hL
    have identity : (J K a b c A B C : ℤ) - 6 * (k - 1) =
        L - s - t + k * ((if t = 0 then 1 else 0) - (if s = 0 then 1 else 0)) := by
      dsimp only [J]
      push_cast
      change 2 * s + 2 * ((-S - 1).val : ℤ) + ((-S).val : ℤ) +
        3 * ((-T - 1).val : ℤ) + ((T - 1).val : ℤ) + t + u + v + w +
        ((-a + B + C).val : ℤ) + ((-b + A + C).val : ℤ) +
        ((-c + A + B).val : ℤ) - 6 * (k - 1) = _
      rw [neg_pred S, neg_pred T, neg_val, pred_val, mixedA, mixedB, mixedC]
      change 2 * s + 2 * (k - 1 - s) + (if s = 0 then 0 else k - s) +
        3 * (k - 1 - t) + (if t = 0 then k - 1 else t - 1) + t + u + v + w +
        (u + t - s) % k + (v + t - s) % k + (w + t - s) % k - 6 * (k - 1) = _
      dsimp only [L]
      by_cases hs0 : s = 0 <;> by_cases ht0 : t = 0 <;>
        simp only [hs0, ht0, if_true, if_false] <;> ring
    have lower : 6 * (k - 1) ≤ (J K a b c A B C : ℤ) := by
      by_cases hs0 : s = 0 <;> by_cases ht0 : t = 0
      · simp [hs0, ht0] at identity
        linarith only [identity, hL.1, hs0, ht0]
      · have htpos : 0 < t := by omega
        have hstrong := hL.2 hs0 htpos
        simp [hs0, ht0] at identity
        linarith only [identity, hstrong, hs0]
      · simp [hs0, ht0] at identity
        linarith only [identity, hL.1, hk, ht0]
      · simp [hs0, ht0] at identity
        linarith only [identity, hL.1]
    have cast_bound : ((6 * (K - 1) : ℕ) : ℤ) = (6 * (k - 1) : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ K)]
      rfl
    exact_mod_cast (show ((6 * (K - 1) : ℕ) : ℤ) ≤ (J K a b c A B C : ℤ) by
      rw [cast_bound]; exact lower)

#print axioms result

end D5.S3.QuantumBounds.SliwaSevenArbitraryOutcomeLocalBound
