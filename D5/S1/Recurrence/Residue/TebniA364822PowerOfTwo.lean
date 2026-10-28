/- GID: D5/S1/Recurrence/Residue/TebniA364822PowerOfTwo
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/TebniA364822PowerOfTwo
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Hyperbolic EGF coefficients have residue one at every power of two. -/

/-
admission_basis: open-problem-resolution (#18644; Proved)
escape_witness: none (the settling result supplies admission).
proof_shape: claim: bind-only; consumers: result; escape_witness: none.
Direct frozen dependencies for claim: none.
proof_shape: pow_two_dvd_choose_odd: bind-only; consumers: result; escape_witness: none.
Direct frozen dependencies for pow_two_dvd_choose_odd: none.
proof_shape: result: bind-only; consumers: external open-problem settlement; escape_witness: none.
Direct frozen dependencies for result:
  D5/S1/Recurrence/Residue/IntegralEGFComposition.Integral
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.Integral
  declaration statement_id: sha256:58f904034d1cc94d838676ce38b8f8081488ba2d1ebdfd8ffb25c0be7ee2a0b6;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff
  declaration statement_id: sha256:4352a2872dd069de3ca054aab1c4950930a811b324435173c0e64781d46fc330;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_mul
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_mul
  declaration statement_id: sha256:d77958a970452d82e689ee9878ff79fda28b9bc1537bf45041f667d5e694a1f5;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.eCoeff_zero
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff_zero
  declaration statement_id: sha256:69e1d2e22802c66151c2c3239fdceab9ab8a796d9f10d82c7366e4d57e790054;
  D5/S1/Recurrence/Residue/IntegralEGFComposition.integral_subst
  Lean: D5.S1.Recurrence.Residue.IntegralEGFComposition.integral_subst
  declaration statement_id: sha256:fdc1fe71291a1abb3b01cd1c2aa567a8b264a1c888a1723ecd9394f64e5b1ce1;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.eCoeff_encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.eCoeff_encode
  declaration statement_id: sha256:352e6f7d24ca45dedb1bc8138765409965b1fb7a21903187a52a0d3fbd0a3bf7;
  D5/S1/Recurrence/Residue/QuarticEGFFixedPoint.encode
  Lean: D5.S1.Recurrence.Residue.QuarticEGFFixedPoint.encode
  declaration statement_id: sha256:bb200c57b57d3db01e9c5a71120a010d1a0509f29a9046ca82c6726744329840;
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22441.
The claim includes m = 0, whose modulus is one.
-/

import D5.S1.Recurrence.Residue.TebniA364822

set_option autoImplicit false

namespace D5.S1.Recurrence.Residue.TebniA364822PowerOfTwo
open D5.S1.Recurrence.Residue.TebniA364822 Finset

/-- A364822 ("For n = 2^m (m natural number), a(n) == 1 (mod n)."). -/
def claim : Prop := ∀ m : ℕ, ∃ z : ℤ, (z : ℚ) = a (2 ^ m) ∧ z ≡ 1 [ZMOD 2 ^ m]

private theorem pow_two_dvd_choose_odd (m k : ℕ) (hk : Odd k) : 2^m ∣ (2^m).choose k := by
  have hpos : 0 < 2^m := by exact Nat.two_pow_pos m
  cases k with
  | zero => simp at hk
  | succ k =>
    have heq := Nat.add_one_mul_choose_eq (2^m-1) k
    rw [Nat.sub_add_cancel hpos] at heq
    have hd : 2^m ∣ (2^m).choose (k+1) * (k+1) := by
      exact Dvd.intro ((2 ^ m - 1).choose k) heq
    exact (Nat.prime_two.coprime_pow_of_not_dvd hk.not_two_dvd_nat).symm.dvd_mul_right.mp hd

theorem result : claim := by
  intro m
  refine ⟨(a (2^m)).num, num_cast (2^m), ?_⟩
  cases m with
  | zero => simp [Int.ModEq]
  | succ m =>
    have hn : Even (2^(m+1)) := by
      rw [even_iff_two_dvd]
      exact dvd_pow_self 2 (by omega)
    apply (ZMod.intCast_eq_intCast_iff ((a (2^(m+1))).num) 1 (2^(m+1))).mp
    rw [num_recurrence]
    simp only [hn, ite_true, Int.cast_add, Int.cast_one, Int.cast_mul, Int.cast_ofNat,
      Int.cast_sum, Int.cast_natCast, Int.cast_ite, Int.cast_zero]
    have hs : (∑ k ∈ range (2^(m+1)), ((2^(m+1)).choose k : ZMod (2^(m+1))) *
        ((a k).num : ZMod (2^(m+1))) * (if Even (2^(m+1)-k) then 0 else 1)) = 0 := by
      apply sum_eq_zero
      intro k hk
      by_cases he : Even (2^(m+1)-k)
      · simp [he]
      · have hko : Odd k := by
          have hkle := (mem_range.mp hk).le
          have hoddn : ¬ Odd (2^(m+1)) := Nat.not_odd_iff_even.mpr hn
          rw [Nat.even_sub' hkle] at he
          by_contra hnot
          exact he (iff_of_false hoddn hnot)
        have hd := pow_two_dvd_choose_odd (m+1) k hko
        rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd]
        simp
    rw [hs]
    simp

end D5.S1.Recurrence.Residue.TebniA364822PowerOfTwo
