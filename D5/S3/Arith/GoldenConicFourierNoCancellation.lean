/- GID: D5/S3/Arith/GoldenConicFourierNoCancellation
   generality: G
   mirror-B: none(waiver:all-odd-moduli-actual-standard-character)
   mirror-E: none(waiver:complete-two-and-four-phase-obstruction)
   anchors: []
   digest: The two and four stationary golden phases cannot cancel for an odd modulus. -/

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.GoldenConicFourierNoCancellation

/-- The actual two-phase sum, with a sign supplied by the quadratic Gauss factor. -/
noncomputable def pairPeriod {N : ℕ} [NeZero N] (a : ZMod N) (s : ℂ) : ℂ :=
  ZMod.stdAddChar a + s * ZMod.stdAddChar (-a)

/-- The four actual stationary phases on a scalar fourth-root orbit. -/
noncomputable def quarterPeriod {N : ℕ} [NeZero N]
    (a i : ZMod N) (s : ℂ) : ℂ :=
  pairPeriod a 1 + s * pairPeriod (i * a) 1

/-- A canonical additive-character theorem used in the full golden-orbit transform.
It does not assume nonvanishing of any phase sum. The only scalar premises are
an actual inverse of a and, for the four-term clause, an actual square root of -1.
The modulus may be composite. These are exactly the one-, two- and four-element
scalar stabilizers of the original golden orbit; the one-term case is automatic.
Both possible Gauss signs are covered. -/
theorem result {N : ℕ} [NeZero N] (hN : 3 ≤ N) (hodd : Odd N)
    (a ainv : ZMod N) (ha : a * ainv = 1) :
    (∀ s : ℂ, s = 1 ∨ s = -1 → pairPeriod a s ≠ 0) ∧
    (∀ i : ZMod N, i ^ 2 = -1 →
      ∀ s : ℂ, s = 1 ∨ s = -1 → quarterPeriod a i s ≠ 0) := by
  let chi : AddChar (ZMod N) ℂ := ZMod.stdAddChar
  have hinj : Function.Injective chi := ZMod.injective_stdAddChar
  have hone (t : ZMod N) (ht : chi t = 1) : t = 0 := by
    apply hinj
    simpa only [chi.map_zero_eq_one] using ht
  have htwo : (2 : ZMod N) ≠ 0 := by
    intro h
    have hd : N ∣ 2 := (ZMod.natCast_eq_zero_iff 2 N).mp h
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hroot (t : ZMod N) : chi t ^ N = 1 := by
    rw [← chi.map_nsmul_eq_pow]
    have hz : N • t = 0 := by
      rw [nsmul_eq_mul]
      simp
    rw [hz, chi.map_zero_eq_one]
  have hminus (t : ZMod N) : chi t ≠ -1 := by
    intro ht
    have h := hroot t
    rw [ht, hodd.neg_one_pow] at h
    norm_num at h
  have hprod (t : ZMod N) : chi t * chi (-t) = 1 := by
    rw [← chi.map_add_eq_mul, add_neg_cancel, chi.map_zero_eq_one]
  constructor
  · intro s hs
    rcases hs with rfl | rfl
    · intro h
      change chi a + 1 * chi (-a) = 0 at h
      have hsq : chi (a + a) = -1 := by
        rw [chi.map_add_eq_mul]
        linear_combination (chi a) * h - hprod a
      exact hminus (a + a) hsq
    · intro h
      change chi a + (-1) * chi (-a) = 0 at h
      have hsq : chi (a + a) = 1 := by
        rw [chi.map_add_eq_mul]
        linear_combination (chi a) * h + hprod a
      have hz := hone (a + a) hsq
      apply htwo
      calc
        (2 : ZMod N) = (a + a) * ainv := by linear_combination -2 * ha
        _ = 0 := by rw [hz]; ring
  · intro i hi s hs
    have hi1 : i ≠ 1 := by
      intro h
      rw [h] at hi
      apply htwo
      linear_combination hi
    have hin1 : i ≠ -1 := by
      intro h
      rw [h] at hi
      apply htwo
      linear_combination hi
    have hsame : chi a ≠ chi (i * a) := by
      intro h
      have heq := hinj h
      apply hi1
      calc
        i = (i * a) * ainv := by rw [mul_assoc, ha, mul_one]
        _ = a * ainv := by rw [← heq]
        _ = 1 := ha
    have hopposite : chi (a + i * a) ≠ 1 := by
      intro h
      have hz := hone (a + i * a) h
      have hia : i * a = -a := by linear_combination hz
      apply hin1
      calc
        i = (i * a) * ainv := by rw [mul_assoc, ha, mul_one]
        _ = (-a) * ainv := by rw [hia]
        _ = -1 := by rw [neg_mul, ha]
    rcases hs with rfl | rfl
    · intro h
      change (chi a + 1 * chi (-a)) +
        1 * (chi (i * a) + 1 * chi (-(i * a))) = 0 at h
      have hfactor : (chi a + chi (i * a)) * (chi a * chi (i * a) + 1) = 0 := by
        linear_combination (chi a * chi (i * a)) * h -
          chi (i * a) * hprod a - chi a * hprod (i * a)
      rcases mul_eq_zero.mp hfactor with hleft | hright
      · have hbad : chi (a + -(i * a)) = -1 := by
          rw [chi.map_add_eq_mul]
          linear_combination chi (-(i * a)) * hleft - hprod (i * a)
        exact hminus (a + -(i * a)) hbad
      · apply hminus (a + i * a)
        rw [chi.map_add_eq_mul]
        linear_combination hright
    · intro h
      change (chi a + 1 * chi (-a)) +
        (-1) * (chi (i * a) + 1 * chi (-(i * a))) = 0 at h
      have hfactor : (chi a - chi (i * a)) * (chi a * chi (i * a) - 1) = 0 := by
        linear_combination (chi a * chi (i * a)) * h -
          chi (i * a) * hprod a + chi a * hprod (i * a)
      rcases mul_eq_zero.mp hfactor with hleft | hright
      · exact hsame (sub_eq_zero.mp hleft)
      · apply hopposite
        rw [chi.map_add_eq_mul]
        exact sub_eq_zero.mp hright

end D5.S3.Arith.GoldenConicFourierNoCancellation
