/- GID: D5/S1/Recurrence/Residue/IterateExponentialFiveModThree
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/IterateExponentialFiveModThree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A396805 has residues zero, one, zero modulo three from index three. -/

import D5.S1.Recurrence.Residue.IterateExponentialParity
import Mathlib.Data.Nat.Choose.Lucas

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition
open D5.S1.Recurrence.Residue.QuarticEGFFixedPoint
open D5.S1.Recurrence.Residue.IterateExponentialParity
open private stepK stepK_map aK_fixed aK_zero from
  D5.S1.Recurrence.Residue.IterateExponentialParity
open private intSeries intSeries_composition from
  D5.S1.Recurrence.Residue.QuarticEGFModFour

namespace D5.S1.Recurrence.Residue.IterateExponentialFiveModThree

theorem result (n : ℕ) (hn : 3 ≤ n) :
    Nat.ModEq 3 (D5.S1.Recurrence.Residue.IterateExponentialParity.aK 5 n)
      (if n % 3 = 1 then 1 else 0) := by
  classical
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let M (R : Type) [CommSemiring R] (f g : ℕ → R) (n : ℕ) : R :=
    ∑ i ∈ range (n + 1), (n.choose i : R) * f i * g (n - i)
  have M_map {R S : Type} [CommSemiring R] [CommSemiring S]
      (φ : R →+* S) (f g : ℕ → R) (n : ℕ) :
      φ (M R f g n) = M S (fun i => φ (f i)) (fun i => φ (g i)) n := by
    simp [M]
  have intSeries_mul (f g : ℕ → ℤ) :
      intSeries (M ℤ f g) = intSeries f * intSeries g := by
    apply eCoeff_ext
    intro j
    simp [intSeries, eCoeff_mul, M]
  have intSeries_shift (f : ℕ → ℤ) :
      intSeries (fun j => f (j + 1)) = derivative ℚ (intSeries f) := by
    apply eCoeff_ext
    intro j
    simp [intSeries]
  have coeff_cube (f : ℕ → ℤ) (j : ℕ) :
      M ℤ (M ℤ f f) f (j + 1) =
        3 * M ℤ (M ℤ f f) (fun i => f (i + 1)) j := by
    have hs : intSeries (M ℤ (M ℤ f f) f) = (intSeries f) ^ 3 := by
      rw [intSeries_mul, intSeries_mul]
      ring
    have hd := congrArg (fun s => eCoeff s j) (derivative_pow (intSeries f) 3)
    rw [← hs, eCoeff_derivative] at hd
    have hh : (3 : PowerSeries ℚ) * intSeries f ^ (3 - 1) *
        derivative ℚ (intSeries f) =
        3 * intSeries (M ℤ (M ℤ f f) (fun i => f (i + 1))) := by
      simp only [intSeries_mul, intSeries_shift]
      norm_num
      ring
    norm_num only [Nat.cast_ofNat] at hd
    rw [hh] at hd
    have he (s : PowerSeries ℚ) : eCoeff (3 * s) j = 3 * eCoeff s j := by
      rw [show (3 : PowerSeries ℚ) * s = s + s + s by ring]
      simp [eCoeff, mul_add]
      ring
    rw [he] at hd
    simp only [intSeries, eCoeff_encode] at hd
    exact_mod_cast hd
  have composition_third (f g : ℕ → ℤ) (hg : g 0 = 0) (j : ℕ) :
      composition f g (j + 3) =
        M ℤ (composition (fun i => f (i + 3)) g)
          (M ℤ (M ℤ (fun i => g (i + 1)) (fun i => g (i + 1)))
            (fun i => g (i + 1))) j +
        3 * M ℤ (M ℤ (composition (fun i => f (i + 2)) g)
          (fun i => g (i + 1))) (fun i => g (i + 2)) j +
        M ℤ (composition (fun i => f (i + 1)) g) (fun i => g (i + 3)) j := by
    let D := derivative ℚ
    have hgs : HasSubst (intSeries g) := .of_constantCoeff_zero (by
      change constantCoeff (intSeries g) = 0
      simp [intSeries, hg])
    have hc : D (D (D ((intSeries f).subst (intSeries g)))) =
        ((D (D (D (intSeries f)))).subst (intSeries g)) * (D (intSeries g)) ^ 3 +
        3 * ((D (D (intSeries f))).subst (intSeries g)) * D (intSeries g) *
          D (D (intSeries g)) +
        ((D (intSeries f)).subst (intSeries g)) * D (D (D (intSeries g))) := by
      simp only [D, derivative_subst hgs, map_add, Derivation.leibniz, smul_eq_mul]
      ring
    rw [← intSeries_composition f g hg] at hc
    have shift2 (a : ℕ → ℤ) : D (D (intSeries a)) = intSeries (fun i => a (i + 2)) := by
      rw [← intSeries_shift, ← intSeries_shift]
    have shift3 (a : ℕ → ℤ) : D (D (D (intSeries a))) =
        intSeries (fun i => a (i + 3)) := by
      rw [shift2, ← intSeries_shift]
    rw [shift3, shift3, shift3, shift2, shift2,
      ← intSeries_shift, ← intSeries_shift] at hc
    simp only [← intSeries_composition _ _ hg] at hc
    have headd (u v : PowerSeries ℚ) : eCoeff (u + v) j = eCoeff u j + eCoeff v j := by
      simp [eCoeff, mul_add]
    have hethree (u : PowerSeries ℚ) : eCoeff (3 * u) j = 3 * eCoeff u j := by
      rw [show (3 : PowerSeries ℚ) * u = u + u + u by ring]
      rw [headd, headd]
      ring
    have hcf := congrArg (fun s => eCoeff s j) hc
    rw [show intSeries (fun i => g (i + 1)) ^ 3 =
      intSeries (M ℤ (M ℤ (fun i => g (i + 1)) (fun i => g (i + 1)))
        (fun i => g (i + 1))) by simp only [intSeries_mul]; ring] at hcf
    simp only [headd] at hcf
    rw [show 3 * intSeries (composition (fun i => f (i + 2)) g) *
      intSeries (fun i => g (i + 1)) * intSeries (fun i => g (i + 2)) =
      3 * (intSeries (composition (fun i => f (i + 2)) g) *
        intSeries (fun i => g (i + 1)) * intSeries (fun i => g (i + 2))) by ring,
      hethree] at hcf
    simp only [← intSeries_mul] at hcf
    simp only [intSeries, eCoeff_encode] at hcf
    exact_mod_cast hcf
  have cube_mod (f : ℕ → ZMod 3) (j : ℕ) :
      M (ZMod 3) (M (ZMod 3) f f) f j = if j = 0 then f 0 ^ 3 else 0 := by
    cases j with
    | zero =>
      simp only [M, Nat.zero_add, sum_range_one, Nat.choose_self, Nat.cast_one, one_mul,
        Nat.sub_self, ite_true]
      ring
    | succ j =>
      let z (i : ℕ) : ℤ := (f i).val
      have he := congrArg (Int.castRingHom (ZMod 3)) (coeff_cube z j)
      simp only [map_mul, map_ofNat, M_map] at he
      have hz : (fun i => (Int.castRingHom (ZMod 3)) (z i)) = f := by
        funext i
        simp [z]
      rw [hz] at he
      simpa only [show (3 : ZMod 3) = 0 by decide, zero_mul, Nat.succ_ne_zero, if_false] using he
  have composition_third_mod (f g : ℕ → ZMod 3) (hg : g 0 = 0) (j : ℕ) :
      composition f g (j + 3) =
        M (ZMod 3) (composition (fun i => f (i + 3)) g)
          (fun i => if i = 0 then g 1 ^ 3 else 0) j +
        M (ZMod 3) (composition (fun i => f (i + 1)) g) (fun i => g (i + 3)) j := by
    let zf (i : ℕ) : ℤ := (f i).val
    let zg (i : ℕ) : ℤ := (g i).val
    have hzg : zg 0 = 0 := by simp [zg, hg]
    have he := congrArg (Int.castRingHom (ZMod 3)) (composition_third zf zg hzg j)
    simp only [map_add, map_mul, map_ofNat, M_map, composition_map] at he
    have hf : ∀ i, (Int.castRingHom (ZMod 3)) (zf i) = f i := by intro i; simp [zf]
    have hg' : ∀ i, (Int.castRingHom (ZMod 3)) (zg i) = g i := by intro i; simp [zg]
    simp only [hf, hg', show (3 : ZMod 3) = 0 by decide, zero_mul, add_zero] at he
    rw [show M (ZMod 3) (M (ZMod 3) (fun i => g (i + 1)) (fun i => g (i + 1)))
      (fun i => g (i + 1)) = (fun i => if i = 0 then g 1 ^ 3 else 0) by
        funext i; simpa using cube_mod (fun i => g (i + 1)) i] at he
    exact he
  have choose3 (n i : ℕ) :
      (n.choose i : ZMod 3) = (n % 3).choose (i % 3) * ((n / 3).choose (i / 3) : ZMod 3) := by
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := i) (p := 3)
    exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  have sum_residue_zero (h : ℕ → ZMod 3)
      (hz : ∀ i, i % 3 ≠ 0 → h i = 0) (q : ℕ) :
      ∑ i ∈ range (3 * q + 1), h i = ∑ r ∈ range (q + 1), h (3 * r) := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show 3 * (q + 1) + 1 = (3 * q + 1) + 1 + 1 + 1 by omega]
      rw [sum_range_succ, sum_range_succ, sum_range_succ, ih, sum_range_succ]
      rw [hz (3 * q + 1) (by omega), hz (3 * q + 1 + 1) (by omega)]
      simp only [add_zero]
      rw [show 3 * q + 1 + 1 + 1 = 3 * (q + 1) by omega]
      simp only [sum_range_succ]
  have M_zero_residue (f g : ℕ → ZMod 3) (q : ℕ) :
      M (ZMod 3) f g (3 * q) = ∑ r ∈ range (q + 1),
        (q.choose r : ZMod 3) * f (3 * r) * g (3 * (q - r)) := by
    dsimp only [M]
    rw [sum_residue_zero _ (by
      intro i hi
      have hc : ((3 * q).choose i : ZMod 3) = 0 := by
        rw [choose3]
        simp only [Nat.mul_mod_right]
        rw [Nat.choose_eq_zero_of_lt (by omega : 0 < i % 3), Nat.cast_zero, zero_mul]
      rw [hc, zero_mul, zero_mul])]
    apply sum_congr rfl
    intro r hr
    rw [choose3]
    have hq : (3 * q) / 3 = q := by omega
    have hr' : (3 * r) / 3 = r := by omega
    norm_num [Nat.mul_mod_right, hq, hr', Nat.mul_sub]
  have M_delta (f : ℕ → ZMod 3) (j : ℕ) :
      M (ZMod 3) f (fun i => if i = 0 then 1 else 0) j = f j := by
    dsimp only [M]
    rw [sum_eq_single j]
    · simp
    · intro i hi hij
      have hi' := mem_range.mp hi
      rw [if_neg (by omega : j - i ≠ 0), mul_zero]
    · simp
  have composition_zero_residue (f g : ℕ → ZMod 3)
      (hg0 : ∀ q, g (3 * q) = 0) (hg1 : g 1 = 1) (q : ℕ) :
      composition f g (3 * q) = f (3 * q) := by
    have hg : g 0 = 0 := by simpa using hg0 0
    induction q generalizing f with
    | zero => simp [composition]
    | succ q ih =>
      rw [show 3 * (q + 1) = 3 * q + 3 by omega,
        composition_third_mod f g hg (3 * q), hg1, one_pow, M_delta, ih]
      rw [M_zero_residue (composition (fun i => f (i + 1)) g) (fun i => g (i + 3)) q]
      have hz : (∑ r ∈ range (q + 1), (q.choose r : ZMod 3) *
          composition (fun i => f (i + 1)) g (3 * r) * g (3 * (q - r) + 3)) = 0 := by
        apply sum_eq_zero
        intro r _
        rw [show 3 * (q - r) + 3 = 3 * (q - r + 1) by omega, hg0, mul_zero]
      rw [hz, add_zero]
  have composition_one_residue (f g : ℕ → ZMod 3)
      (hg0 : ∀ q, g (3 * q) = 0) (hg1 : g 1 = 1) (q : ℕ) :
      composition f g (3 * q + 1) = ∑ r ∈ range (q + 1),
        (q.choose r : ZMod 3) * f (3 * r + 1) * g (3 * (q - r) + 1) := by
    have hc : composition f g (3 * q + 1) =
        M (ZMod 3) (composition (fun i => f (i + 1)) g) (fun i => g (i + 1)) (3 * q) := by
      rw [composition, Fin.sum_univ_eq_sum_range (fun i =>
        ((3 * q).choose i : ZMod 3) * composition (fun j => f (j + 1)) g i * g (3 * q - i + 1))]
    rw [hc, M_zero_residue (composition (fun i => f (i + 1)) g) (fun i => g (i + 1)) q]
    apply sum_congr rfl
    intro r _
    rw [composition_zero_residue _ _ hg0 hg1]
  let b (i : ℕ) : ZMod 3 := aK 5 i
  have b_fixed : b = stepK 5 b := by
    funext i
    have he := congrArg (Nat.castRingHom (ZMod 3)) (congrFun (aK_fixed 5) i)
    rw [stepK_map] at he
    exact he
  have b_rec (i : ℕ) : b (i + 1) =
      (i + 1 : ZMod 3) * composition (fun _ => 1) (iterate b 5) i := by
    have he := congrFun b_fixed (i + 1)
    simpa only [stepK] using he
  have b_zero : b 0 = 0 := by simp [b, aK_zero]
  have b_one : b 1 = 1 := by simpa [composition] using b_rec 0
  have b_zero_residue (q : ℕ) : b (3 * q) = 0 := by
    cases q with
    | zero => exact b_zero
    | succ q =>
      rw [show 3 * (q + 1) = (3 * q + 2) + 1 by omega, b_rec]
      have hz : ((3 * q + 2 : ℕ) : ZMod 3) + 1 = 0 := by
        push_cast
        rw [show (3 : ZMod 3) = 0 by decide, zero_mul, zero_add]
        decide
      rw [hz, zero_mul]
  have iterate_support (j : ℕ) :
      (∀ q, iterate b j (3 * q) = 0) ∧ iterate b j 1 = 1 := by
    induction j with
    | zero =>
      constructor
      · intro q
        simp [iterate, identity, show 3 * q ≠ 1 by omega]
      · simp [iterate, identity]
    | succ j ih =>
      constructor
      · intro q
        rw [iterate, composition_zero_residue _ _ ih.1 ih.2]
        exact b_zero_residue q
      · simp [iterate, composition, b_one, ih.2]
  have b_one_residue (q : ℕ) : b (3 * q + 1) = 1 := by
    rw [b_rec, composition_zero_residue _ _ (iterate_support 5).1 (iterate_support 5).2]
    simp only [Nat.cast_mul, Nat.cast_ofNat,
      show (3 : ZMod 3) = 0 by decide, zero_mul, zero_add, mul_one]
  have iterate_one_residue (j q : ℕ) : iterate b j (3 * q + 1) = (j : ZMod 3) ^ q := by
    induction j generalizing q with
    | zero =>
      by_cases hq : q = 0
      · subst q
        simp [iterate, identity]
      · simp [iterate, identity, hq]
    | succ j ih =>
      rw [iterate, composition_one_residue _ _ (iterate_support j).1 (iterate_support j).2]
      simp_rw [b_one_residue, mul_one, ih]
      have hs := (add_pow (1 : ZMod 3) (j : ZMod 3) q).symm
      simpa only [one_pow, one_mul, mul_one, mul_comm, add_comm, Nat.cast_add, Nat.cast_one,
        Nat.succ_eq_add_one] using hs
  have b_two_residue (q : ℕ) : b (3 * q + 2) = 2 * (6 : ZMod 3) ^ q := by
    rw [show 3 * q + 2 = (3 * q + 1) + 1 by omega, b_rec,
      composition_one_residue _ _ (iterate_support 5).1 (iterate_support 5).2]
    simp_rw [iterate_one_residue, mul_one]
    have hs : (∑ r ∈ range (q + 1), (q.choose r : ZMod 3) * (5 : ZMod 3) ^ (q - r)) =
        (6 : ZMod 3) ^ q := by
      have he := (add_pow (1 : ZMod 3) (5 : ZMod 3) q).symm
      simpa only [one_pow, one_mul, mul_comm, show (1 : ZMod 3) + 5 = 6 by decide] using he
    simp only [Nat.cast_ofNat]
    rw [hs]
    congr 1
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
      show (3 : ZMod 3) = 0 by decide, zero_mul, zero_add]
    decide
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  change b n = ((if n % 3 = 1 then 1 else 0 : ℕ) : ZMod 3)
  have hm := Nat.mod_lt n (by decide : 0 < 3)
  interval_cases hr : n % 3
  · have he : n = 3 * (n / 3) := by omega
    rw [if_neg (by decide : ¬0 = 1), Nat.cast_zero, he, b_zero_residue]
  · have he : n = 3 * (n / 3) + 1 := by omega
    rw [if_pos rfl, Nat.cast_one, he, b_one_residue]
  · have he : n = 3 * (n / 3) + 2 := by omega
    rw [if_neg (by decide : ¬2 = 1), Nat.cast_zero, he, b_two_residue,
      show (6 : ZMod 3) = 0 by decide, zero_pow (by omega : n / 3 ≠ 0), mul_zero]

end D5.S1.Recurrence.Residue.IterateExponentialFiveModThree
