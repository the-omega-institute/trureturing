/- GID: D5/S3/Factorization/ThreeTorsionZMod
   generality: G
   mirror-B: D5/B/S3/Factorization/ThreeTorsionZMod
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Three-torsion in a cyclic modulus of order 3m has exactly three coordinates. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Tactic

namespace D5.S3.Factorization.ThreeTorsionZMod

/-- The three-torsion coordinates in ZMod (3m), with m positive. -/
theorem three_nsmul_eq_zero_iff (m : ℕ) (hm : 0 < m) (x : ZMod (3 * m)) :
    3 • x = 0 ↔ x = 0 ∨ x = (m : ZMod (3 * m)) ∨
      x = ((2 * m : ℕ) : ZMod (3 * m)) := by
  letI : NeZero (3 * m) := ⟨by omega⟩
  constructor
  · intro hx
    have hc : ((3 * x.val : ℕ) : ZMod (3 * m)) = 0 := by
      simpa only [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul] using hx
    have hd : 3 * m ∣ 3 * x.val := (ZMod.natCast_eq_zero_iff _ _).mp hc
    have hmdiv : m ∣ x.val := (Nat.mul_dvd_mul_iff_left (by omega : 0 < 3)).mp hd
    obtain ⟨k, hk⟩ := hmdiv
    have hlt : x.val < 3 * m := ZMod.val_lt x
    have hk3 : k < 3 := by
      nlinarith
    have hrepr : ((m * k : ℕ) : ZMod (3 * m)) = x := by
      rw [← hk, ZMod.natCast_zmod_val]
    interval_cases k <;> simp_all [Nat.mul_comm]
  · rintro (rfl | rfl | rfl)
    · simp
    · have hz : ((3 * m : ℕ) : ZMod (3 * m)) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr dvd_rfl
      simpa only [Nat.cast_mul, nsmul_eq_mul] using hz
    · have hd : 3 * m ∣ 3 * (2 * m) := by
        refine ⟨2, ?_⟩
        ring
      have hz : ((3 * (2 * m) : ℕ) : ZMod (3 * m)) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hd
      simpa only [Nat.cast_mul, nsmul_eq_mul] using hz

#print axioms three_nsmul_eq_zero_iff

end D5.S3.Factorization.ThreeTorsionZMod
