/- GID: D5/S1/Words/Palindromes/PeriodDoubling/DyadicSignedWeight
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/DyadicSignedWeight
   mirror-E: none(waiver:unbounded-dyadic-minimum-split)
   anchors: []
   utility: none
   digest: Signed binary weight splits exactly across every dyadic boundary. -/

/-
proof_shape: content (signed_weight_dyadic_split)
escape_witness: Binary induction couples the two alternative carries at every dyadic scale.
admission_basis: escape-witness
Direct frozen dependencies: none; SignedWeight is delivered with this module.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.SignedWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.PeriodDoubling

/-- The exact two-branch formula includes both endpoints and arbitrary integer high parts. -/
theorem signed_weight_dyadic_split (h : ℕ) (M : ℤ) (u : ℕ) (hu : u ≤ 2 ^ h) :
    signedWeight (M * 2 ^ h + u) =
      min (signedWeight M + signedWeight u)
        (signedWeight (M + 1) + signedWeight ((2 ^ h - u : ℕ) : ℤ)) := by
  obtain ⟨hzero, hone, hneg, htri, heven, hodd⟩ := signed_weight_arithmetic
  have adjacent (x : ℤ) :
      signedWeight x ≤ signedWeight (x + 1) + 1 ∧
        signedWeight (x + 1) ≤ signedWeight x + 1 := by
    have ha := htri x 1
    have hb := htri (x + 1) (-1)
    have hn := hneg 1
    simp only [hone] at ha hn
    have he : x + 1 + -1 = x := by omega
    rw [he, hn] at hb
    exact ⟨hb, ha⟩
  induction h generalizing M u with
  | zero =>
    have ha := adjacent M
    have hu' : u = 0 ∨ u = 1 := by norm_num at hu; omega
    rcases hu' with rfl | rfl
    · simp only [pow_zero, mul_one, Nat.cast_zero, add_zero,
        Nat.sub_zero, Nat.cast_one, hzero, hone]
      omega
    · simp only [pow_zero, mul_one, Nat.cast_one, Nat.sub_self,
        Nat.cast_zero, hzero, hone, add_zero]
      omega
  | succ h ih =>
    let v := u / 2
    by_cases hm : u % 2 = 0
    · have he : u = 2 * v := by dsimp [v]; omega
      have hv : v ≤ 2 ^ h := by rw [pow_succ] at hu; omega
      have ht : 2 ^ (h + 1) - u = 2 * (2 ^ h - v) := by
        rw [pow_succ] at hu ⊢
        omega
      have hleft : M * 2 ^ (h + 1) + u = 2 * (M * 2 ^ h + (v : ℤ)) := by
        rw [he, pow_succ]
        push_cast
        ring
      rw [hleft, heven, ih M v hv, ht, he]
      simp only [Nat.cast_mul, Nat.cast_ofNat, heven]
    · have he : u = 2 * v + 1 := by dsimp [v]; omega
      have hv : v ≤ 2 ^ h := by rw [pow_succ] at hu; omega
      have hv1 : v + 1 ≤ 2 ^ h := by rw [pow_succ] at hu; omega
      have ht : 2 ^ (h + 1) - u = 2 * (2 ^ h - (v + 1)) + 1 := by
        rw [pow_succ] at hu ⊢
        omega
      have hleft : M * 2 ^ (h + 1) + u = 2 * (M * 2 ^ h + (v : ℤ)) + 1 := by
        rw [he, pow_succ]
        push_cast
        ring
      have hnext : M * 2 ^ h + (v : ℤ) + 1 = M * 2 ^ h + ((v + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      have htail : 2 ^ h - (v + 1) + 1 = 2 ^ h - v := by omega
      rw [hleft, hodd, hnext, ih M v hv, ih M (v + 1) hv1, ht, he]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, hodd]
      have hcast : ((2 ^ h - (v + 1) : ℕ) : ℤ) + 1 =
          ((2 ^ h - v : ℕ) : ℤ) := by omega
      rw [hcast]
      omega

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.signed_weight_dyadic_split
