/- GID: D5/S3/Arith/GoldenResource/GoldenCell902160Uniqueness
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenResource/GoldenCell902160Uniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.GroupTheory.OrderOfElement]
   utility: none
   digest: The order modulo 179 isolates one exponent class and one member of the scaled cell. -/

import D5.S3.Arith.GoldenResource.GoldenCell5040Congruence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.GoldenResource.GoldenCell902160Uniqueness

-- This argument uses the specific order modulo 179; an arbitrary multiplier need not have it.
private theorem three_order_179 : orderOf (3 : ZMod 179) = 89 := by
  let : Fact (Nat.Prime 89) := ⟨by decide⟩
  exact orderOf_eq_prime (by norm_num; decide) (by decide)

/-- The residue modulo 179 is characterized for every natural exponent, without a search bound. -/
theorem three_pow_modEq_179_iff (n : Nat) :
    Nat.ModEq 179 (3 ^ n) 2241 ↔ Nat.ModEq 89 n 23 := by
  have hfin : IsOfFinOrder (3 : ZMod 179) :=
    orderOf_pos_iff.mp (by rw [three_order_179]; decide)
  have hres : (3 : ZMod 179) ^ 23 = 2241 := by decide
  rw [← ZMod.natCast_eq_natCast_iff]
  simpa only [Nat.cast_pow, Nat.cast_ofNat, ← hres, three_order_179] using
    (hfin.pow_eq_pow_iff_modEq (n := n) (m := 23))

private theorem modEq_2241_at_multiple (t : Nat) (ht : t ≠ 0) :
    Nat.ModEq 10080 (3 ^ (10080 * t)) 2241 := by
  have hbase := GoldenCell5040Congruence.goldenCell5040_modEq_2241 10080 (by simp)
  -- Lift the frozen small-modulus residues, keeping the large power symbolic.
  have hone (m : Nat) (hm : m ∣ 10080) (hr : Nat.ModEq m 2241 1) :
      Nat.ModEq m (3 ^ (10080 * t)) 2241 := by
    have hp : Nat.ModEq m (3 ^ (10080 * t)) 1 := by
      simpa only [pow_mul, one_pow] using ((hbase.of_dvd hm).trans hr).pow t
    exact hp.trans hr.symm
  have h9 : Nat.ModEq 9 (3 ^ (10080 * t)) 2241 := by
    have hz : Nat.ModEq 9 (3 ^ 10080) 0 :=
      (hbase.of_dvd (by decide : 9 ∣ 10080)).trans (by decide)
    have hp : Nat.ModEq 9 (3 ^ (10080 * t)) 0 := by
      simpa only [pow_mul, zero_pow ht] using hz.pow t
    exact hp.trans (by decide)
  have h35 : Nat.ModEq (5 * 7) (3 ^ (10080 * t)) 2241 :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 5 7)).mp
      ⟨hone 5 (by decide) (by decide), hone 7 (by decide) (by decide)⟩
  have h1120 : Nat.ModEq (32 * 35) (3 ^ (10080 * t)) 2241 :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 32 35)).mp
      ⟨hone 32 (by decide) (by decide), h35⟩
  exact (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 9 1120)).mp
    ⟨h9, h1120⟩

/-- Exactly one member of the scaled six-element cell has power residue 2241 modulo itself. -/
theorem goldenCell902160_modEq_2241_iff (n : Nat)
    (hn : n ∈ ({902160, 1804320, 2706480, 3608640, 5412960, 10825920} : Finset Nat)) :
    Nat.ModEq n (3 ^ n) 2241 ↔ n = 1804320 := by
  constructor
  · intro hmod
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    have hd : 179 ∣ n := by
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hexp := (three_pow_modEq_179_iff n).mp (hmod.of_dvd hd)
    -- Each failure is witnessed modulo 179; only exponents modulo 89 are normalized.
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | norm_num [Nat.ModEq] at hexp
  · rintro rfl
    have hcrt : Nat.ModEq (10080 * 179) (3 ^ (10080 * 179)) 2241 :=
      (Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 10080 179)).mp
        ⟨modEq_2241_at_multiple 179 (by decide),
          (three_pow_modEq_179_iff (10080 * 179)).mpr (by decide)⟩
    simpa only [show 10080 * 179 = 1804320 by decide] using hcrt

#print axioms three_pow_modEq_179_iff
#print axioms goldenCell902160_modEq_2241_iff

end D5.S3.Arith.GoldenResource.GoldenCell902160Uniqueness
