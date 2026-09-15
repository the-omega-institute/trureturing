/- GID: D5/S1/Recurrence/Residue/IterateExponentialModThree
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/IterateExponentialModThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A396803 coefficients equal their indices modulo three. -/

import D5.S1.Recurrence.Residue.IterateExponentialParity
import Mathlib.Data.Nat.Choose.Lucas

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint
open D5.S1.Recurrence.Residue.IterateExponentialParity
open private stepK stepK_map approximationK from
  D5.S1.Recurrence.Residue.IterateExponentialParity
open D5.S1.Recurrence.Residue.QuarticEGFModFour (F)
open private coeff_F_pow eCoeff_F composition_assoc composition_identity_right from
  D5.S1.Recurrence.Residue.QuarticEGFModFour

namespace D5.S1.Recurrence.Residue.IterateExponentialModThree

theorem result (n : ℕ) (hn : 1 ≤ n) :
    Nat.ModEq 3 (D5.S1.Recurrence.Residue.IterateExponentialParity.aK 3 n) n := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have choose3 (n i : ℕ) :
      (n.choose i : ZMod 3) = (n % 3).choose (i % 3) * ((n / 3).choose (i / 3) : ZMod 3) := by
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := i) (p := 3)
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  let E (g : ℕ → ZMod 3) := composition (fun _ => 1) g
  have E_rec (g : ℕ → ZMod 3) (n : ℕ) :
      E g (n + 1) = ∑ i ∈ range (n + 1),
        (n.choose i : ZMod 3) * E g i * g (n - i + 1) := by
    unfold E
    rw [composition, Fin.sum_univ_eq_sum_range (fun i =>
      (n.choose i : ZMod 3) * composition (fun _ => 1) g i * g (n - i + 1))]
  have E_block_one (g : ℕ → ZMod 3)
      (h1 : ∀ q, g (3 * q + 1) = if q = 0 then 1 else 0) (q : ℕ) :
      E g (3 * q + 1) = E g (3 * q) := by
    rw [E_rec, sum_range_succ]
    have hg1 : g 1 = 1 := by simpa using h1 0
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, zero_add, hg1, mul_one]
    have hs : (∑ i ∈ range (3 * q), ((3 * q).choose i : ZMod 3) * E g i *
        g (3 * q - i + 1)) = 0 := by
      apply sum_eq_zero
      intro i hi
      have hi' := mem_range.mp hi
      by_cases hm : i % 3 = 0
      · have hh : 3 * q - i + 1 = 3 * (q - i / 3) + 1 := by omega
        rw [hh, h1, if_neg (by omega : q - i / 3 ≠ 0), mul_zero]
      · have hc : ((3 * q).choose i : ZMod 3) = 0 := by
          rw [choose3]
          simp only [Nat.mul_mod_right]
          rw [Nat.choose_eq_zero_of_lt (by omega : 0 < i % 3), Nat.cast_zero, zero_mul]
        rw [hc, zero_mul, zero_mul]
    rw [hs, zero_add]
  have E_support (g : ℕ → ZMod 3)
      (h0 : ∀ q, g (3 * q) = 0)
      (h1 : ∀ q, g (3 * q + 1) = if q = 0 then 1 else 0) (q : ℕ) :
      E g (3 * q) = 1 ∧ E g (3 * q + 1) = 1 := by
    have hg1 : g 1 = 1 := by simpa using h1 0
    have hstep (q : ℕ) : E g (3 * q + 3) = E g (3 * q) := by
      let S := ∑ i ∈ range (3 * q + 1), ((3 * q + 1).choose i : ZMod 3) *
        E g i * g (3 * q + 1 - i + 1)
      have htwo : E g (3 * q + 2) = S + E g (3 * q + 1) := by
        rw [show 3 * q + 2 = (3 * q + 1) + 1 by omega, E_rec, sum_range_succ]
        simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, zero_add, hg1, mul_one]
        rfl
      have hthree : E g (3 * q + 3) = 2 * S + E g (3 * q + 2) := by
        rw [show 3 * q + 3 = (3 * q + 2) + 1 by omega, E_rec, sum_range_succ]
        simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, zero_add, hg1, mul_one]
        congr 1
        rw [show 3 * q + 2 = (3 * q + 1) + 1 by omega, sum_range_succ']
        have hz : g (3 * q + 1 + 1 - 0 + 1) = 0 := by
          simpa [Nat.mul_add] using h0 (q + 1)
        simp only [hz, mul_zero, add_zero]
        dsimp [S]
        rw [mul_sum]
        apply sum_congr rfl
        intro i hi
        have hi' := mem_range.mp hi
        have hj : 3 * q + 1 + 1 - (i + 1) + 1 = 3 * q + 1 - i + 1 := by omega
        rw [hj]
        rcases Nat.mod_lt i (by decide : 0 < 3) with hm
        interval_cases hr : i % 3
        · have hi0 : i = 3 * (i / 3) := by omega
          have he : E g (i + 1) = E g i := by
            simpa only [← hi0] using E_block_one g h1 (i / 3)
          have hc : ((3 * q + 1 + 1).choose (i + 1) : ZMod 3) =
              2 * ((3 * q + 1).choose i : ZMod 3) := by
            rw [choose3 (3 * q + 1 + 1) (i + 1), choose3 (3 * q + 1) i]
            have hdiv : (i + 1) / 3 = i / 3 := by omega
            have hq1 : (3 * q + 1) / 3 = q := by omega
            have hq2 : (3 * q + 1 + 1) / 3 = q := by omega
            norm_num [Nat.add_mod, hr, hdiv, hq1, hq2]
          rw [hc, he]
          ring
        · have hh : 3 * q + 1 - i + 1 = 3 * (q - i / 3) + 1 := by omega
          rw [hh, h1, if_neg (by omega : q - i / 3 ≠ 0)]
          ring
        · have hh : 3 * q + 1 - i + 1 = 3 * (q - i / 3) := by omega
          rw [hh, h0]
          ring
      rw [hthree, htwo, E_block_one g h1]
      have h3 : (3 : ZMod 3) = 0 := by decide
      linear_combination S * h3
    have he0 : E g (3 * q) = 1 := by
      induction q with
      | zero => simp [E, composition]
      | succ q ih =>
        rw [show 3 * (q + 1) = 3 * q + 3 by omega, hstep, ih]
    exact ⟨he0, (E_block_one g h1 q).trans he0⟩
  have subst_F_formula (f : PowerSeries ℚ) (n : ℕ) :
      eCoeff (f.subst F) n =
        ∑ k ∈ range (n + 1), (n.choose k : ℚ) * eCoeff f k * (k : ℚ) ^ (n - k) := by
    rw [eCoeff, coeff_subst' (.of_constantCoeff_zero (show constantCoeff F = 0 by simp [F]))]
    have hs : (Function.support (fun k => coeff k f • coeff n (F ^ k))) ⊆
        (range (n + 1) : Set ℕ) := by
      intro k hk
      by_contra h
      have hkn : ¬k ≤ n := by simpa using h
      exact hk (by simp [coeff_F_pow, hkn])
    rw [finsum_eq_sum_of_support_subset _ hs, mul_sum]
    apply sum_congr rfl
    intro k hk
    have hkn := mem_range_succ_iff.mp hk
    rw [coeff_F_pow, if_pos hkn, smul_eq_mul]
    have hc : (n.choose k : ℚ) * k.factorial * (n - k).factorial = n.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
    dsimp only [eCoeff]
    rw [← hc]
    field_simp
  have comp_linear_formula (f : ℕ → ℤ) (n : ℕ) :
      composition f (fun j : ℕ => (j : ℤ)) n =
        ∑ k ∈ range (n + 1), (n.choose k : ℤ) * f k * (k : ℤ) ^ (n - k) := by
    have h := subst_F_formula (encode (fun j => (f j : ℚ))) n
    rw [eCoeff_composition _ _ (by simp [F]),
      show eCoeff F = (fun j : ℕ => (j : ℚ)) from funext eCoeff_F,
      show eCoeff (encode (fun j => (f j : ℚ))) = (fun j => (f j : ℚ))
        from funext (eCoeff_encode _)] at h
    have hm := composition_map (Int.castRingHom ℚ) f (fun j : ℕ => (j : ℤ)) n
    change ((composition f (fun j : ℕ => (j : ℤ)) n : ℤ) : ℚ) =
      composition (fun j => (f j : ℚ)) (fun j : ℕ => (j : ℚ)) n at hm
    rw [← hm] at h
    dsimp only at h
    exact_mod_cast h
  let T (f : ℕ → ZMod 3) (n : ℕ) : ZMod 3 :=
    ∑ k ∈ range (n + 1), (n.choose k : ZMod 3) * f k * (k : ZMod 3) ^ (n - k)
  have T_zero_residue (f : ℕ → ZMod 3) (q : ℕ) :
      T f (3 * q) = f (3 * q) := by
    dsimp only [T]
    rw [sum_range_succ]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero, mul_one]
    have hs : (∑ i ∈ range (3 * q), ((3 * q).choose i : ZMod 3) *
        f i * (i : ZMod 3) ^ (3 * q - i)) = 0 := by
      apply sum_eq_zero
      intro i hi
      have hi' := mem_range.mp hi
      by_cases hm : i % 3 = 0
      · have hz : (i : ZMod 3) = 0 := by rw [← ZMod.natCast_mod i 3, hm]; rfl
        rw [hz, zero_pow (by omega : 3 * q - i ≠ 0), mul_zero]
      · have hc : ((3 * q).choose i : ZMod 3) = 0 := by
          rw [choose3]
          simp only [Nat.mul_mod_right]
          rw [Nat.choose_eq_zero_of_lt (by omega : 0 < i % 3), Nat.cast_zero, zero_mul]
        rw [hc, zero_mul, zero_mul]
    rw [hs, zero_add]
  have sum_residue_one (h : ℕ → ZMod 3)
      (hz : ∀ i, i % 3 ≠ 1 → h i = 0) (q : ℕ) :
      ∑ i ∈ range (3 * q + 2), h i = ∑ r ∈ range (q + 1), h (3 * r + 1) := by
    induction q with
    | zero => norm_num [sum_range_succ, hz 0 (by decide)]
    | succ q ih =>
      rw [show 3 * (q + 1) + 2 = (3 * q + 2) + 1 + 1 + 1 by omega]
      rw [sum_range_succ, sum_range_succ, sum_range_succ, ih, sum_range_succ]
      rw [hz (3 * q + 2) (by omega), hz (3 * q + 2 + 1) (by omega)]
      simp only [add_zero]
      rw [show 3 * q + 2 + 1 + 1 = 3 * (q + 1) + 1 by omega]
      simp only [sum_range_succ]
  have T_one_residue (f : ℕ → ZMod 3) (q : ℕ) :
      T f (3 * q + 1) = ∑ r ∈ range (q + 1), (q.choose r : ZMod 3) * f (3 * r + 1) := by
    let h (i : ℕ) := ((3 * q + 1).choose i : ZMod 3) * f i *
      (i : ZMod 3) ^ (3 * q + 1 - i)
    have hz : ∀ i, i % 3 ≠ 1 → h i = 0 := by
      intro i hi
      dsimp [h]
      by_cases hin : i ≤ 3 * q + 1
      · have hr := Nat.mod_lt i (by decide : 0 < 3)
        interval_cases hm : i % 3
        · have hi' : i < 3 * q + 1 := by omega
          have hz : (i : ZMod 3) = 0 := by rw [← ZMod.natCast_mod i 3, hm]; rfl
          rw [hz, zero_pow (by omega : 3 * q + 1 - i ≠ 0), mul_zero]
        · exact (hi rfl).elim
        · have hc : ((3 * q + 1).choose i : ZMod 3) = 0 := by
            rw [choose3]
            norm_num [Nat.add_mod, hm]
          rw [hc, zero_mul, zero_mul]
      · rw [Nat.choose_eq_zero_of_lt (by omega : 3 * q + 1 < i), Nat.cast_zero, zero_mul, zero_mul]
    change (∑ i ∈ range (3 * q + 2), h i) = _
    rw [sum_residue_one h hz]
    apply sum_congr rfl
    intro r hr
    dsimp [h]
    rw [choose3]
    have hq : (3 * q + 1) / 3 = q := by omega
    have hr : (3 * r + 1) / 3 = r := by omega
    have hx : (3 * r + 1 : ZMod 3) = 1 := by
      rw [show (3 : ZMod 3) = 0 by decide, zero_mul, zero_add]
    norm_num [Nat.add_mod, hq, hr, hx]
  have triple_support (q : ℕ) :
      iterate (fun n : ℕ => (n : ZMod 3)) 3 (3 * q) = 0 ∧
        iterate (fun n : ℕ => (n : ZMod 3)) 3 (3 * q + 1) = if q = 0 then 1 else 0 := by
    let l (n : ℕ) : ℤ := n
    have hmap (f : ℕ → ℤ) (n : ℕ) :
        ((composition f l n : ℤ) : ZMod 3) = T (fun j => (f j : ZMod 3)) n := by
      rw [show l = (fun j : ℕ => (j : ℤ)) from rfl, comp_linear_formula]
      simp only [T, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_pow]
    have hint : iterate l 3 = composition (composition l l) l := by
      change composition l (composition l (composition l identity)) = _
      rw [composition_identity_right]
      exact (composition_assoc l l l rfl rfl).symm
    have htriple : iterate (fun n : ℕ => (n : ZMod 3)) 3 =
        T (T (fun n : ℕ => (n : ZMod 3))) := by
      funext n
      have hm := iterate_map (Int.castRingHom (ZMod 3)) l 3 n
      change ((iterate l 3 n : ℤ) : ZMod 3) =
        iterate (fun n : ℕ => (n : ZMod 3)) 3 n at hm
      rw [← hm, hint, hmap]
      congr 1
      funext j
      simpa only [l, Int.cast_natCast] using hmap l j
    have hone (q : ℕ) : T (fun n : ℕ => (n : ZMod 3)) (3 * q + 1) = 2 ^ q := by
      rw [T_one_residue]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
        show (3 : ZMod 3) = 0 by decide, zero_mul, zero_add, mul_one]
      simpa only [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat] using
        congrArg (fun j : ℕ => (j : ZMod 3)) (Nat.sum_range_choose q)
    rw [htriple]
    constructor
    · rw [T_zero_residue, T_zero_residue]
      simp only [Nat.cast_mul, Nat.cast_ofNat, show (3 : ZMod 3) = 0 by decide, zero_mul]
    · rw [T_one_residue]
      simp_rw [hone]
      have hs : (∑ r ∈ range (q + 1), (q.choose r : ZMod 3) * (2 : ZMod 3) ^ r) =
          (2 + 1 : ZMod 3) ^ q := by
        simpa only [one_pow, mul_one, one_mul, mul_comm] using (add_pow (2 : ZMod 3) 1 q).symm
      rw [hs, show (2 + 1 : ZMod 3) = 0 by decide]
      exact zero_pow_eq q
  have linear_fixed :
      stepK 3 (fun n : ℕ => (n : ZMod 3)) = fun n : ℕ => (n : ZMod 3) := by
    have he (q : ℕ) := E_support (iterate (fun n : ℕ => (n : ZMod 3)) 3)
      (fun q => (triple_support q).1) (fun q => (triple_support q).2) q
    funext n
    cases n with
    | zero => simp [stepK]
    | succ n =>
      change (n + 1 : ZMod 3) * E (iterate (fun n : ℕ => (n : ZMod 3)) 3) n = _
      have hr := Nat.mod_lt n (by decide : 0 < 3)
      interval_cases hm : n % 3
      · have hn : n = 3 * (n / 3) := by omega
        rw [hn, (he (n / 3)).1, mul_one]
        norm_cast
      · have hn : n = 3 * (n / 3) + 1 := by omega
        rw [hn, (he (n / 3)).2, mul_one]
        norm_cast
      · have hz : ((n + 1 : ℕ) : ZMod 3) = 0 := by
          rw [← ZMod.natCast_mod (n + 1) 3, show (n + 1) % 3 = 0 by omega]
          rfl
        have hz' : (n : ZMod 3) + 1 = 0 := by simpa only [Nat.cast_add, Nat.cast_one] using hz
        simp only [Nat.cast_add, Nat.cast_one, hz', zero_mul]
  have endpoint_of_linear_fixed
      (hf : stepK 3 (fun n : ℕ => (n : ZMod 3)) = fun n : ℕ => (n : ZMod 3))
      (n : ℕ) : Nat.ModEq 3 (aK 3 n) n := by
    have ha (d n : ℕ) : (approximationK 3 d n : ZMod 3) = n := by
      induction d generalizing n with
      | zero => rfl
      | succ d ih =>
        change (Nat.castRingHom (ZMod 3)) (stepK 3 (approximationK 3 d) n) = _
        rw [stepK_map]
        change stepK 3 (fun j => (approximationK 3 d j : ZMod 3)) n = _
        rw [show (fun j => (approximationK 3 d j : ZMod 3)) = (fun j : ℕ => (j : ZMod 3))
          from funext ih, hf]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (ha (n + 1) n)
  cases n with
  | zero => omega
  | succ n => exact endpoint_of_linear_fixed linear_fixed (n + 1)
set_option pp.fullNames true in

#print axioms result

end D5.S1.Recurrence.Residue.IterateExponentialModThree
