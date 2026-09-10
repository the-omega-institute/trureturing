/- GID: D5/S3/Arith/GoldenResource/GoldenCell5040Congruence
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/GoldenCell5040Congruence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.ModEq]
   utility: none
   digest: Small multiplicative orders and coprime CRT give residue 2241 on the 5040 cell. -/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.GoldenResource.GoldenCell5040Congruence

private theorem three_order_16 : orderOf (3 : ZMod 16) = 4 := by
  apply (orderOf_eq_iff (by decide : 0 < 4)).2
  constructor
  · decide
  · intro k hk hkpos
    interval_cases k <;> decide

private theorem three_order_32 : orderOf (3 : ZMod 32) = 8 := by
  apply (orderOf_eq_iff (by decide : 0 < 8)).2
  constructor
  · decide
  · intro k hk hkpos
    interval_cases k <;> decide

private theorem three_order_64 : orderOf (3 : ZMod 64) = 16 := by
  apply (orderOf_eq_iff (by decide : 0 < 16)).2
  constructor
  · decide
  · intro k hk hkpos
    interval_cases k <;> decide

private theorem three_order_5 : orderOf (3 : ZMod 5) = 4 := by
  apply (orderOf_eq_iff (by decide : 0 < 4)).2
  constructor
  · decide
  · intro k hk hkpos
    interval_cases k <;> decide

private theorem three_order_7 : orderOf (3 : ZMod 7) = 6 := by
  apply (orderOf_eq_iff (by decide : 0 < 6)).2
  constructor
  · decide
  · intro k hk hkpos
    interval_cases k <;> decide

private theorem three_pow_modEq_one (m n k : Nat)
    (horder : orderOf (3 : ZMod m) = k) (hn : k ∣ n) : Nat.ModEq m (3 ^ n) 1 := by
  have h : orderOf (3 : ZMod m) ∣ n := by rwa [horder]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      (orderOf_dvd_iff_pow_eq_one.mp h))

-- The exponent stays symbolic while the three prime-power congruences are combined.
private theorem three_pow_modEq_one_crt (n b k : Nat)
    (horder : orderOf (3 : ZMod b) = k) (hk : k ∣ n) (h4 : 4 ∣ n) (h6 : 6 ∣ n)
    (hcop : b.Coprime 35) : Nat.ModEq (b * 35) (3 ^ n) 1 := by
  have h35 : Nat.ModEq (5 * 7) (3 ^ n) 1 :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 5 7)).mp
      ⟨three_pow_modEq_one 5 n 4 three_order_5 h4,
        three_pow_modEq_one 7 n 6 three_order_7 h6⟩
  exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
    ⟨three_pow_modEq_one b n k horder hk, h35⟩

private theorem three_pow_modEq_2241_crt (n a b k : Nat)
    (hshape : n = 3 ^ a * (b * 35)) (han : a ≤ n) (ha3 : a ≤ 3)
    (horder : orderOf (3 : ZMod b) = k) (hk : k ∣ n) (h4 : 4 ∣ n) (h6 : 6 ∣ n)
    (hb : b.Coprime 35) (hcop : (3 ^ a).Coprime (b * 35)) (hm : b * 35 ∣ 2240) :
    Nat.ModEq n (3 ^ n) 2241 := by
  have hzero : Nat.ModEq (3 ^ a) (3 ^ n) 2241 :=
    (Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 3 han)).trans
      (Nat.modEq_zero_iff_dvd.mpr
        ((pow_dvd_pow (3 : Nat) ha3).trans (by decide : 3 ^ 3 ∣ 2241))).symm
  have hone : Nat.ModEq (b * 35) (3 ^ n) 2241 :=
    (three_pow_modEq_one_crt n b k horder hk h4 h6 hb).trans
      (Nat.modEq_of_dvd' (by decide : 1 ≤ 2241) hm)
  have hcrt := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hzero, hone⟩
  simpa only [← hshape] using hcrt

-- Only the factorizations, bounds, divisibilities and small orders are normalized here.
private theorem goldenCell5040_crt_data (n : Nat)
    (hn : n ∈ ({5040, 10080, 15120, 20160, 30240, 60480} : Finset Nat)) :
    ∃ a b k : Nat, n = 3 ^ a * (b * 35) ∧ a ≤ n ∧ a ≤ 3 ∧
      k ∣ n ∧ 4 ∣ n ∧ 6 ∣ n ∧ b.Coprime 35 ∧ (3 ^ a).Coprime (b * 35) ∧
      b * 35 ∣ 2240 ∧ orderOf (3 : ZMod b) = k := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨2, 16, 4, ?_⟩
    norm_num [three_order_16, Nat.Coprime]
    decide
  · refine ⟨2, 32, 8, ?_⟩
    norm_num [three_order_32, Nat.Coprime]
    decide
  · refine ⟨3, 16, 4, ?_⟩
    norm_num [three_order_16, Nat.Coprime]
    decide
  · refine ⟨2, 64, 16, ?_⟩
    norm_num [three_order_64, Nat.Coprime]
    decide
  · refine ⟨3, 32, 8, ?_⟩
    norm_num [three_order_32, Nat.Coprime]
    decide
  · refine ⟨3, 64, 16, ?_⟩
    norm_num [three_order_64, Nat.Coprime]
    decide

/-- Every member of the six-element 5040 cell has power residue 2241 modulo itself. -/
theorem goldenCell5040_modEq_2241 (n : Nat)
    (hn : n ∈ ({5040, 10080, 15120, 20160, 30240, 60480} : Finset Nat)) :
    Nat.ModEq n (3 ^ n) 2241 := by
  obtain ⟨a, b, k, hshape, han, ha3, hk, h4, h6, hb, hcop, hm, horder⟩ :=
    goldenCell5040_crt_data n hn
  exact three_pow_modEq_2241_crt n a b k hshape han ha3 horder hk h4 h6 hb hcop hm

#print axioms goldenCell5040_modEq_2241

end D5.S3.Arith.GoldenResource.GoldenCell5040Congruence
