/- GID: D5/S3/ArithSums/A025529PrimeCubeRefutation
   generality: I
   mirror-B: D5/B/S3/ArithSums/A025529PrimeCubeRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.NumberTheory.Harmonic.Bounds, mathlib/module/Mathlib.NumberTheory.Chebyshev, mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: kind=certified-instance; basis=refutes=atom:be6c6ca15dce93a97f68cdc6ba2cefd8031da6ab49f15b41c07902d2fb527ff5; result=D5/S3/ArithSums/A025529PrimeCubeRefutation.prime_square_only_refuted; claim=D5/S3/ArithSums/A025529PrimeCubeRefutation.PrimeSquareOnly
   digest: The prime cube 16843^3 refutes the A025529 composite-solution classification. -/

import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

open Finset
namespace D5.S3.ArithSums.A025529PrimeCubeRefutation

/-- The natural integer represented by the LCM times the rational harmonic sum. -/
def A (m : ℕ) : ℕ := ∑ k ∈ Icc 1 m, Nat.lcmUpto m / k

/-- The composite-solution classification for A025529. -/
def PrimeSquareOnly : Prop :=
  ∀ n : ℕ, (1 < n ∧ ¬ Nat.Prime n ∧ n ∣ A (n - 1)) →
    ∃ q : ℕ, Nat.Prime q ∧ 3 < q ∧ n = q ^ 2

/-- Reflection and denominator partition lift the short ring congruence to the
actual LCM-weighted sum at a prime cube. No large harmonic sum is evaluated. -/
theorem prime_cube_divides (p : ℕ) (hp : p.Prime) (hp3 : 3 < p)
    (hres : (∑ k ∈ Icc 1 (p - 1), (k : ZMod (p ^ 3))⁻¹) = 0) :
    p ^ 3 ∣ A (p ^ 3 - 1) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp0
  -- Exact natural quotients recover the rational definition for every index.
  have A_eq (m : ℕ) : (A m : ℚ) = (Nat.lcmUpto m : ℚ) * harmonic m := by
    rw [A, Nat.cast_sum, harmonic_eq_sum_Icc, mul_sum]
    apply sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
    rw [Nat.cast_div (show k ∣ Nat.lcmUpto m from dvd_lcm hk)
      (by exact_mod_cast hk0), div_eq_mul_inv]
  let R : Subring ℚ :=
    { carrier := {x | ¬ p ∣ x.den}
      zero_mem' := by simpa using hp.not_dvd_one
      one_mem' := by simpa using hp.not_dvd_one
      add_mem' := by
        intro a b ha hb h
        exact (hp.dvd_mul.mp (h.trans (Rat.add_den_dvd a b))).elim ha hb
      neg_mem' := by intro a ha; simpa using ha
      mul_mem' := by
        intro a b ha hb h
        exact (hp.dvd_mul.mp (h.trans (Rat.mul_den_dvd a b))).elim ha hb }
  have inv_mem (k : ℕ) (hk : ¬ p ∣ k) : (k : ℚ)⁻¹ ∈ R := by
    change ¬ p ∣ (k : ℚ)⁻¹.den
    rw [Rat.inv_natCast_den, if_neg (show k ≠ 0 by rintro rfl; exact hk (dvd_zero p))]
    exact hk
  let U (N : ℕ) : ℚ := ∑ k ∈ (Icc 1 (N - 1)).filter (fun k => ¬ p ∣ k), (k : ℚ)⁻¹
  -- Pair k with N-k; both denominators and 2 are units in the local ring.
  have reflection (N : ℕ) (hN : 0 < N) (hpN : p ∣ N) : U N / (N : ℚ) ∈ R := by
    let S := (Icc 1 (N - 1)).filter (fun k => ¬ p ∣ k)
    have hS (k : ℕ) (hk : k ∈ S) : N - k ∈ S := by
      obtain ⟨hkr, hkp⟩ := mem_filter.mp hk
      obtain ⟨hk1, hkN⟩ := mem_Icc.mp hkr
      apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      intro h
      exact hkp (by simpa only [Nat.sub_sub_self (by omega : k ≤ N)] using Nat.dvd_sub hpN h)
    have hpair : (∑ k ∈ S, ((N - k : ℕ) : ℚ)⁻¹) = U N := by
      apply sum_bij (fun k _ => N - k) hS
      · intro a ha b hb hab
        have := (mem_Icc.mp (mem_filter.mp ha).1).2
        have := (mem_Icc.mp (mem_filter.mp hb).1).2
        omega
      · intro b hb
        refine ⟨N - b, hS b hb, ?_⟩
        have := (mem_Icc.mp (mem_filter.mp hb).1).2
        omega
      · intro k hk; rfl
    have heq : U N / (N : ℚ) =
        (2 : ℚ)⁻¹ * ∑ k ∈ S, (k : ℚ)⁻¹ * ((N - k : ℕ) : ℚ)⁻¹ := by
      have hsum : U N + U N =
          (N : ℚ) * ∑ k ∈ S, (k : ℚ)⁻¹ * ((N - k : ℕ) : ℚ)⁻¹ := by
        conv_lhs => rhs; rw [← hpair]
        rw [← sum_add_distrib, mul_sum]
        apply sum_congr rfl
        intro k hk
        have hkb := mem_Icc.mp (mem_filter.mp hk).1
        have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
        have hNk0 : ((N - k : ℕ) : ℚ) ≠ 0 := by
          exact_mod_cast (show N - k ≠ 0 by omega)
        rw [Nat.cast_sub (by omega : k ≤ N)] at hNk0 ⊢
        field_simp
        ring
      have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      apply (div_eq_iff hNQ).mpr
      linear_combination (1 / 2 : ℚ) * hsum
    rw [heq]
    apply R.mul_mem (inv_mem 2 (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
    apply R.sum_mem
    intro k hk
    exact R.mul_mem (inv_mem k (mem_filter.mp hk).2)
      (inv_mem (N - k) (mem_filter.mp (hS k hk)).2)
  -- The terms divisible by p are indexed bijectively by k ↦ p*k.
  have partition (N : ℕ) (hN : 0 < N) :
      harmonic (p * N - 1) = U (p * N) + (p : ℚ)⁻¹ * harmonic (N - 1) := by
    rw [harmonic_eq_sum_Icc, ← sum_filter_add_sum_filter_not _ (fun k => ¬ p ∣ k)]
    congr 1
    rw [harmonic_eq_sum_Icc, mul_sum]
    symm
    apply sum_bij (fun k _ => p * k)
    · intro k hk
      obtain ⟨hk1, hkN⟩ := mem_Icc.mp hk
      apply mem_filter.mpr
      have hklt : k < N := by omega
      have hpklt := Nat.mul_lt_mul_of_pos_left hklt hp.pos
      refine ⟨mem_Icc.mpr ⟨by nlinarith [hp.pos], by omega⟩, ?_⟩
      simp
    · intro a ha b hb hab
      exact Nat.eq_of_mul_eq_mul_left hp.pos hab
    · intro b hb
      obtain ⟨hb, hd⟩ := mem_filter.mp hb
      have hd' : p ∣ b := by simpa using hd
      obtain ⟨k, rfl⟩ := hd'
      refine ⟨k, mem_Icc.mpr ?_, rfl⟩
      obtain ⟨hb1, hbN⟩ := mem_Icc.mp hb
      constructor
      · nlinarith [hp.pos]
      · have : p * k < p * N := by omega
        have := (Nat.mul_lt_mul_left hp.pos).mp this
        omega
    · intro k hk
      rw [Nat.cast_mul, mul_inv_rev, mul_comm]
  have hpartition : (p : ℚ)^2 * harmonic (p^3 - 1) =
      harmonic (p - 1) + p * U (p^2) + (p : ℚ)^2 * U (p^3) := by
    have h2 := partition p hp.pos
    have h3 := partition (p^2) (pow_pos hp.pos _)
    rw [show p * p = p^2 by ring] at h2
    rw [show p * p^2 = p^3 by ring] at h3
    rw [h3, h2]
    field_simp
    ring
  have hU2 : U (p^2) / (p : ℚ)^2 ∈ R := by
    simpa only [Nat.cast_pow] using
      reflection (p^2) (pow_pos hp.pos _) (dvd_pow_self p (by omega : 2 ≠ 0))
  have hU3 : U (p^3) / (p : ℚ)^3 ∈ R := by
    simpa only [Nat.cast_pow] using
      reflection (p^3) (pow_pos hp.pos _) (dvd_pow_self p (by omega : 3 ≠ 0))
  -- Clear only the short sum abstractly; the factorial is never evaluated.
  have hsmall : harmonic (p - 1) / (p : ℚ)^3 ∈ R := by
    let D := Nat.factorial (p - 1)
    let B (k : ℕ) := D / k
    let T := ∑ k ∈ Icc 1 (p - 1), B k
    have hD (k : ℕ) (hk : k ∈ Icc 1 (p - 1)) : k ∣ D :=
      Nat.dvd_factorial (by have := (mem_Icc.mp hk).1; omega) (mem_Icc.mp hk).2
    have hkunit (k : ℕ) (hk : k ∈ Icc 1 (p - 1)) : IsUnit (k : ZMod (p^3)) := by
      apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega : 0 < 3)).mpr
      have := mem_Icc.mp hk
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have hT : (T : ZMod (p^3)) = 0 := by
      have heq : (T : ZMod (p^3)) =
          (D : ZMod (p^3)) * ∑ k ∈ Icc 1 (p - 1), (k : ZMod (p^3))⁻¹ := by
        dsimp only [T]
        rw [Nat.cast_sum, mul_sum]
        apply sum_congr rfl
        intro k hk
        have hkD : B k * k = D := Nat.div_mul_cancel (hD k hk)
        have hc : (B k : ZMod (p^3)) * k = D := by
          simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : ZMod (p^3))) hkD
        rw [← hc, mul_assoc, ZMod.mul_inv_of_unit _ (hkunit k hk), mul_one]
      rw [heq, hres, mul_zero]
    have hH : (T : ℚ) = (D : ℚ) * harmonic (p - 1) := by
      dsimp only [T]
      rw [Nat.cast_sum, harmonic_eq_sum_Icc, mul_sum]
      apply sum_congr rfl
      intro k hk
      have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by have := (mem_Icc.mp hk).1; omega)
      exact (Nat.cast_div (hD k hk) hk0).trans (div_eq_mul_inv _ _)
    have hi : (harmonic (p - 1)).num * (D : ℤ) = (T : ℤ) * (harmonic (p - 1)).den := by
      have he : ((harmonic (p - 1)).num : ℚ) * D = (T : ℚ) * (harmonic (p - 1)).den := by
        rw [hH, ← Rat.mul_den_eq_num]
        ring
      exact_mod_cast he
    have hunitD : IsUnit (D : ZMod (p^3)) := by
      apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega : 0 < 3)).mpr
      rw [Nat.Prime.dvd_factorial hp]
      omega
    have hz : ((harmonic (p - 1)).num : ZMod (p^3)) = 0 := by
      apply hunitD.mul_right_cancel
      have hc := congrArg (fun z : ℤ => (z : ZMod (p^3))) hi
      push_cast at hc
      simpa only [hT, zero_mul] using hc
    obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    have hden : harmonic (p - 1) ∈ R := by
      rw [harmonic_eq_sum_Icc]
      apply R.sum_mem
      intro k hk
      have := mem_Icc.mp hk
      exact inv_mem k (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    have heq : harmonic (p - 1) / (p : ℚ)^3 =
        (a : ℚ) * ((harmonic (p - 1)).den : ℚ)⁻¹ := by
      have hn : ((harmonic (p - 1)).num : ℚ) = (p : ℚ)^3 * (a : ℚ) := by exact_mod_cast ha
      conv_lhs => lhs; rw [← Rat.num_div_den (harmonic (p - 1))]
      rw [hn]
      field_simp
    rw [heq]
    exact R.mul_mem (intCast_mem R a) (inv_mem _ hden)
  have hL : p^2 ∣ Nat.lcmUpto (p^3 - 1) := by
    apply dvd_lcm
    apply mem_Icc.mpr
    constructor
    · exact Nat.one_le_pow _ _ hp.pos
    · have : p^3 = p^2 * p := by ring
      have : p^2 < p^3 := by nlinarith [pow_pos hp.pos 2]
      omega
  have hA : (A (p^3 - 1) : ℚ) / (p : ℚ)^3 ∈ R := by
    have heq : (A (p^3 - 1) : ℚ) / (p : ℚ)^3 =
        (Nat.lcmUpto (p^3 - 1) / p^2 : ℕ) *
          (harmonic (p - 1) / (p : ℚ)^3 + U (p^2) / (p : ℚ)^2 +
            (p : ℚ)^2 * (U (p^3) / (p : ℚ)^3)) := by
      rw [Nat.cast_div hL (pow_ne_zero _ hpQ), A_eq]
      push_cast
      field_simp
      linear_combination (Nat.lcmUpto (p^3 - 1) : ℚ) * hpartition
    rw [heq]
    exact R.mul_mem (natCast_mem R _) (R.add_mem (R.add_mem hsmall hU2)
      (R.mul_mem (R.pow_mem (natCast_mem R p) 2) hU3))
  let q : ℚ := (A (p^3 - 1) : ℚ) / (p : ℚ)^3
  have hq : (A (p^3 - 1) : ℤ) * q.den = (p : ℤ)^3 * q.num := by
    have := Rat.mul_den_eq_num q
    dsimp [q] at this
    have he : (A (p^3 - 1) : ℚ) * q.den = (p : ℚ)^3 * q.num := by
      dsimp [q]
      field_simp at this ⊢
      exact this
    exact_mod_cast he
  have hunit : IsUnit (q.den : ZMod (p^3)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega : 0 < 3)).mpr hA
  have hz : (A (p^3 - 1) : ZMod (p^3)) = 0 := by
    apply hunit.mul_right_cancel
    have hh := congrArg (fun x : ℤ => (x : ZMod (p^3))) hq
    push_cast at hh
    simpa only [← Nat.cast_pow, ZMod.natCast_self, zero_mul] using hh
  exact (ZMod.natCast_eq_zero_iff _ _).mp hz

/-- The prime cube 16843^3 refutes the complete composite-solution classification. -/
theorem prime_square_only_refuted : ¬ PrimeSquareOnly := by
  intro hclaim
  -- Balanced interval certificates: 64 disjoint leaves and 63 exact additions.
  have residue : (∑ k ∈ Ico (1 : ℕ) 16843, (k : ZMod (16843^3))⁻¹) = 0 := by
    have r1_264 : (∑ k ∈ Ico (1 : ℕ) 264, (k : ZMod (16843^3))⁻¹) = 471428010868 := by
      decide +kernel
    have r264_527 : (∑ k ∈ Ico (264 : ℕ) 527, (k : ZMod (16843^3))⁻¹) = 1079740593648 := by
      decide +kernel
    have r1_527 : (∑ k ∈ Ico (1 : ℕ) 527, (k : ZMod (16843^3))⁻¹) = 1551168604516 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 1 ≤ 264) (by decide : 264 ≤ 527)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r1_264 r264_527).trans
          (by decide +kernel))
    have r527_790 : (∑ k ∈ Ico (527 : ℕ) 790, (k : ZMod (16843^3))⁻¹) = 4525174035128 := by
      decide +kernel
    have r790_1053 : (∑ k ∈ Ico (790 : ℕ) 1053, (k : ZMod (16843^3))⁻¹) = 342026242703 := by
      decide +kernel
    have r527_1053 : (∑ k ∈ Ico (527 : ℕ) 1053, (k : ZMod (16843^3))⁻¹) = 89066048724 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 527 ≤ 790) (by decide : 790 ≤ 1053)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r527_790 r790_1053).trans
          (by decide +kernel))
    have r1_1053 : (∑ k ∈ Ico (1 : ℕ) 1053, (k : ZMod (16843^3))⁻¹) = 1640234653240 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 1 ≤ 527) (by decide : 527 ≤ 1053)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r1_527 r527_1053).trans
          (by decide +kernel))
    have r1053_1316 : (∑ k ∈ Ico (1053 : ℕ) 1316, (k : ZMod (16843^3))⁻¹) = 2259937017727 := by
      decide +kernel
    have r1316_1579 : (∑ k ∈ Ico (1316 : ℕ) 1579, (k : ZMod (16843^3))⁻¹) = 2712265615000 := by
      decide +kernel
    have r1053_1579 : (∑ k ∈ Ico (1053 : ℕ) 1579, (k : ZMod (16843^3))⁻¹) = 194068403620 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 1053 ≤ 1316) (by decide : 1316 ≤ 1579)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r1053_1316 r1316_1579).trans
          (by decide +kernel))
    have r1579_1842 : (∑ k ∈ Ico (1579 : ℕ) 1842, (k : ZMod (16843^3))⁻¹) = 250464687490 := by
      decide +kernel
    have r1842_2106 : (∑ k ∈ Ico (1842 : ℕ) 2106, (k : ZMod (16843^3))⁻¹) = 3928151190908 := by
      decide +kernel
    have r1579_2106 : (∑ k ∈ Ico (1579 : ℕ) 2106, (k : ZMod (16843^3))⁻¹) = 4178615878398 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 1579 ≤ 1842) (by decide : 1842 ≤ 2106)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r1579_1842 r1842_2106).trans
          (by decide +kernel))
    have r1053_2106 : (∑ k ∈ Ico (1053 : ℕ) 2106, (k : ZMod (16843^3))⁻¹) = 4372684282018 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 1053 ≤ 1579) (by decide : 1579 ≤ 2106)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r1053_1579 r1579_2106).trans
          (by decide +kernel))
    have r1_2106 : (∑ k ∈ Ico (1 : ℕ) 2106, (k : ZMod (16843^3))⁻¹) = 1234784706151 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 1 ≤ 1053) (by decide : 1053 ≤ 2106)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r1_1053 r1053_2106).trans
          (by decide +kernel))
    have r2106_2369 : (∑ k ∈ Ico (2106 : ℕ) 2369, (k : ZMod (16843^3))⁻¹) = 3682614178791 := by
      decide +kernel
    have r2369_2632 : (∑ k ∈ Ico (2369 : ℕ) 2632, (k : ZMod (16843^3))⁻¹) = 957741191781 := by
      decide +kernel
    have r2106_2632 : (∑ k ∈ Ico (2106 : ℕ) 2632, (k : ZMod (16843^3))⁻¹) = 4640355370572 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 2106 ≤ 2369) (by decide : 2369 ≤ 2632)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r2106_2369 r2369_2632).trans
          (by decide +kernel))
    have r2632_2895 : (∑ k ∈ Ico (2632 : ℕ) 2895, (k : ZMod (16843^3))⁻¹) = 4308946959374 := by
      decide +kernel
    have r2895_3158 : (∑ k ∈ Ico (2895 : ℕ) 3158, (k : ZMod (16843^3))⁻¹) = 1936715224557 := by
      decide +kernel
    have r2632_3158 : (∑ k ∈ Ico (2632 : ℕ) 3158, (k : ZMod (16843^3))⁻¹) = 1467527954824 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 2632 ≤ 2895) (by decide : 2895 ≤ 3158)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r2632_2895 r2895_3158).trans
          (by decide +kernel))
    have r2106_3158 : (∑ k ∈ Ico (2106 : ℕ) 3158, (k : ZMod (16843^3))⁻¹) = 1329749096289 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 2106 ≤ 2632) (by decide : 2632 ≤ 3158)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r2106_2632 r2632_3158).trans
          (by decide +kernel))
    have r3158_3421 : (∑ k ∈ Ico (3158 : ℕ) 3421, (k : ZMod (16843^3))⁻¹) = 1694777027943 := by
      decide +kernel
    have r3421_3684 : (∑ k ∈ Ico (3421 : ℕ) 3684, (k : ZMod (16843^3))⁻¹) = 3239055884524 := by
      decide +kernel
    have r3158_3684 : (∑ k ∈ Ico (3158 : ℕ) 3684, (k : ZMod (16843^3))⁻¹) = 155698683360 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 3158 ≤ 3421) (by decide : 3421 ≤ 3684)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r3158_3421 r3421_3684).trans
          (by decide +kernel))
    have r3684_3947 : (∑ k ∈ Ico (3684 : ℕ) 3947, (k : ZMod (16843^3))⁻¹) = 878290529986 := by
      decide +kernel
    have r3947_4211 : (∑ k ∈ Ico (3947 : ℕ) 4211, (k : ZMod (16843^3))⁻¹) = 28863366876 := by
      decide +kernel
    have r3684_4211 : (∑ k ∈ Ico (3684 : ℕ) 4211, (k : ZMod (16843^3))⁻¹) = 907153896862 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 3684 ≤ 3947) (by decide : 3947 ≤ 4211)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r3684_3947 r3947_4211).trans
          (by decide +kernel))
    have r3158_4211 : (∑ k ∈ Ico (3158 : ℕ) 4211, (k : ZMod (16843^3))⁻¹) = 1062852580222 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 3158 ≤ 3684) (by decide : 3684 ≤ 4211)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r3158_3684 r3684_4211).trans
          (by decide +kernel))
    have r2106_4211 : (∑ k ∈ Ico (2106 : ℕ) 4211, (k : ZMod (16843^3))⁻¹) = 2392601676511 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 2106 ≤ 3158) (by decide : 3158 ≤ 4211)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r2106_3158 r3158_4211).trans
          (by decide +kernel))
    have r1_4211 : (∑ k ∈ Ico (1 : ℕ) 4211, (k : ZMod (16843^3))⁻¹) = 3627386382662 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 1 ≤ 2106) (by decide : 2106 ≤ 4211)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r1_2106 r2106_4211).trans
          (by decide +kernel))
    have r4211_4474 : (∑ k ∈ Ico (4211 : ℕ) 4474, (k : ZMod (16843^3))⁻¹) = 4355925571167 := by
      decide +kernel
    have r4474_4737 : (∑ k ∈ Ico (4474 : ℕ) 4737, (k : ZMod (16843^3))⁻¹) = 4622792245918 := by
      decide +kernel
    have r4211_4737 : (∑ k ∈ Ico (4211 : ℕ) 4737, (k : ZMod (16843^3))⁻¹) = 4200583587978 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 4211 ≤ 4474) (by decide : 4474 ≤ 4737)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r4211_4474 r4474_4737).trans
          (by decide +kernel))
    have r4737_5000 : (∑ k ∈ Ico (4737 : ℕ) 5000, (k : ZMod (16843^3))⁻¹) = 1068420271104 := by
      decide +kernel
    have r5000_5263 : (∑ k ∈ Ico (5000 : ℕ) 5263, (k : ZMod (16843^3))⁻¹) = 4574005484936 := by
      decide +kernel
    have r4737_5263 : (∑ k ∈ Ico (4737 : ℕ) 5263, (k : ZMod (16843^3))⁻¹) = 864291526933 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 4737 ≤ 5000) (by decide : 5000 ≤ 5263)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r4737_5000 r5000_5263).trans
          (by decide +kernel))
    have r4211_5263 : (∑ k ∈ Ico (4211 : ℕ) 5263, (k : ZMod (16843^3))⁻¹) = 286740885804 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 4211 ≤ 4737) (by decide : 4737 ≤ 5263)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r4211_4737 r4737_5263).trans
          (by decide +kernel))
    have r5263_5526 : (∑ k ∈ Ico (5263 : ℕ) 5526, (k : ZMod (16843^3))⁻¹) = 4632508613183 := by
      decide +kernel
    have r5526_5789 : (∑ k ∈ Ico (5526 : ℕ) 5789, (k : ZMod (16843^3))⁻¹) = 337294221225 := by
      decide +kernel
    have r5263_5789 : (∑ k ∈ Ico (5263 : ℕ) 5789, (k : ZMod (16843^3))⁻¹) = 191668605301 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 5263 ≤ 5526) (by decide : 5526 ≤ 5789)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r5263_5526 r5526_5789).trans
          (by decide +kernel))
    have r5789_6052 : (∑ k ∈ Ico (5789 : ℕ) 6052, (k : ZMod (16843^3))⁻¹) = 2564753083555 := by
      decide +kernel
    have r6052_6316 : (∑ k ∈ Ico (6052 : ℕ) 6316, (k : ZMod (16843^3))⁻¹) = 2059706723211 := by
      decide +kernel
    have r5789_6316 : (∑ k ∈ Ico (5789 : ℕ) 6316, (k : ZMod (16843^3))⁻¹) = 4624459806766 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 5789 ≤ 6052) (by decide : 6052 ≤ 6316)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r5789_6052 r6052_6316).trans
          (by decide +kernel))
    have r5263_6316 : (∑ k ∈ Ico (5263 : ℕ) 6316, (k : ZMod (16843^3))⁻¹) = 37994182960 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 5263 ≤ 5789) (by decide : 5789 ≤ 6316)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r5263_5789 r5789_6316).trans
          (by decide +kernel))
    have r4211_6316 : (∑ k ∈ Ico (4211 : ℕ) 6316, (k : ZMod (16843^3))⁻¹) = 324735068764 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 4211 ≤ 5263) (by decide : 5263 ≤ 6316)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r4211_5263 r5263_6316).trans
          (by decide +kernel))
    have r6316_6579 : (∑ k ∈ Ico (6316 : ℕ) 6579, (k : ZMod (16843^3))⁻¹) = 4092072657436 := by
      decide +kernel
    have r6579_6842 : (∑ k ∈ Ico (6579 : ℕ) 6842, (k : ZMod (16843^3))⁻¹) = 3608764213878 := by
      decide +kernel
    have r6316_6842 : (∑ k ∈ Ico (6316 : ℕ) 6842, (k : ZMod (16843^3))⁻¹) = 2922702642207 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 6316 ≤ 6579) (by decide : 6579 ≤ 6842)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r6316_6579 r6579_6842).trans
          (by decide +kernel))
    have r6842_7105 : (∑ k ∈ Ico (6842 : ℕ) 7105, (k : ZMod (16843^3))⁻¹) = 1827926241833 := by
      decide +kernel
    have r7105_7369 : (∑ k ∈ Ico (7105 : ℕ) 7369, (k : ZMod (16843^3))⁻¹) = 3101728667931 := by
      decide +kernel
    have r6842_7369 : (∑ k ∈ Ico (6842 : ℕ) 7369, (k : ZMod (16843^3))⁻¹) = 151520680657 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 6842 ≤ 7105) (by decide : 7105 ≤ 7369)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r6842_7105 r7105_7369).trans
          (by decide +kernel))
    have r6316_7369 : (∑ k ∈ Ico (6316 : ℕ) 7369, (k : ZMod (16843^3))⁻¹) = 3074223322864 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 6316 ≤ 6842) (by decide : 6842 ≤ 7369)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r6316_6842 r6842_7369).trans
          (by decide +kernel))
    have r7369_7632 : (∑ k ∈ Ico (7369 : ℕ) 7632, (k : ZMod (16843^3))⁻¹) = 450618777288 := by
      decide +kernel
    have r7632_7895 : (∑ k ∈ Ico (7632 : ℕ) 7895, (k : ZMod (16843^3))⁻¹) = 2141764787583 := by
      decide +kernel
    have r7369_7895 : (∑ k ∈ Ico (7369 : ℕ) 7895, (k : ZMod (16843^3))⁻¹) = 2592383564871 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 7369 ≤ 7632) (by decide : 7632 ≤ 7895)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r7369_7632 r7632_7895).trans
          (by decide +kernel))
    have r7895_8158 : (∑ k ∈ Ico (7895 : ℕ) 8158, (k : ZMod (16843^3))⁻¹) = 3270514678745 := by
      decide +kernel
    have r8158_8422 : (∑ k ∈ Ico (8158 : ℕ) 8422, (k : ZMod (16843^3))⁻¹) = 4639327186057 := by
      decide +kernel
    have r7895_8422 : (∑ k ∈ Ico (7895 : ℕ) 8422, (k : ZMod (16843^3))⁻¹) = 3131707635695 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 7895 ≤ 8158) (by decide : 8158 ≤ 8422)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r7895_8158 r8158_8422).trans
          (by decide +kernel))
    have r7369_8422 : (∑ k ∈ Ico (7369 : ℕ) 8422, (k : ZMod (16843^3))⁻¹) = 945956971459 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 7369 ≤ 7895) (by decide : 7895 ≤ 8422)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r7369_7895 r7895_8422).trans
          (by decide +kernel))
    have r6316_8422 : (∑ k ∈ Ico (6316 : ℕ) 8422, (k : ZMod (16843^3))⁻¹) = 4020180294323 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 6316 ≤ 7369) (by decide : 7369 ≤ 8422)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r6316_7369 r7369_8422).trans
          (by decide +kernel))
    have r4211_8422 : (∑ k ∈ Ico (4211 : ℕ) 8422, (k : ZMod (16843^3))⁻¹) = 4344915363087 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 4211 ≤ 6316) (by decide : 6316 ≤ 8422)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r4211_6316 r6316_8422).trans
          (by decide +kernel))
    have r1_8422 : (∑ k ∈ Ico (1 : ℕ) 8422, (k : ZMod (16843^3))⁻¹) = 3194167516642 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 1 ≤ 4211) (by decide : 4211 ≤ 8422)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r1_4211 r4211_8422).trans
          (by decide +kernel))
    have r8422_8685 : (∑ k ∈ Ico (8422 : ℕ) 8685, (k : ZMod (16843^3))⁻¹) = 3706381942250 := by
      decide +kernel
    have r8685_8948 : (∑ k ∈ Ico (8685 : ℕ) 8948, (k : ZMod (16843^3))⁻¹) = 2397121131081 := by
      decide +kernel
    have r8422_8948 : (∑ k ∈ Ico (8422 : ℕ) 8948, (k : ZMod (16843^3))⁻¹) = 1325368844224 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 8422 ≤ 8685) (by decide : 8685 ≤ 8948)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r8422_8685 r8685_8948).trans
          (by decide +kernel))
    have r8948_9211 : (∑ k ∈ Ico (8948 : ℕ) 9211, (k : ZMod (16843^3))⁻¹) = 327266266689 := by
      decide +kernel
    have r9211_9474 : (∑ k ∈ Ico (9211 : ℕ) 9474, (k : ZMod (16843^3))⁻¹) = 1190193871107 := by
      decide +kernel
    have r8948_9474 : (∑ k ∈ Ico (8948 : ℕ) 9474, (k : ZMod (16843^3))⁻¹) = 1517460137796 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 8948 ≤ 9211) (by decide : 9211 ≤ 9474)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r8948_9211 r9211_9474).trans
          (by decide +kernel))
    have r8422_9474 : (∑ k ∈ Ico (8422 : ℕ) 9474, (k : ZMod (16843^3))⁻¹) = 2842828982020 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 8422 ≤ 8948) (by decide : 8948 ≤ 9474)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r8422_8948 r8948_9474).trans
          (by decide +kernel))
    have r9474_9737 : (∑ k ∈ Ico (9474 : ℕ) 9737, (k : ZMod (16843^3))⁻¹) = 4504229588705 := by
      decide +kernel
    have r9737_10000 : (∑ k ∈ Ico (9737 : ℕ) 10000, (k : ZMod (16843^3))⁻¹) = 2013446770584 := by
      decide +kernel
    have r9474_10000 : (∑ k ∈ Ico (9474 : ℕ) 10000, (k : ZMod (16843^3))⁻¹) = 1739542130182 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 9474 ≤ 9737) (by decide : 9737 ≤ 10000)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r9474_9737 r9737_10000).trans
          (by decide +kernel))
    have r10000_10263 : (∑ k ∈ Ico (10000 : ℕ) 10263, (k : ZMod (16843^3))⁻¹) = 5868525872 := by
      decide +kernel
    have r10263_10527 : (∑ k ∈ Ico (10263 : ℕ) 10527, (k : ZMod (16843^3))⁻¹) = 1345154869482 := by
      decide +kernel
    have r10000_10527 : (∑ k ∈ Ico (10000 : ℕ) 10527, (k : ZMod (16843^3))⁻¹) = 1351023395354 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 10000 ≤ 10263) (by decide : 10263 ≤ 10527)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r10000_10263 r10263_10527).trans
          (by decide +kernel))
    have r9474_10527 : (∑ k ∈ Ico (9474 : ℕ) 10527, (k : ZMod (16843^3))⁻¹) = 3090565525536 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 9474 ≤ 10000) (by decide : 10000 ≤ 10527)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r9474_10000 r10000_10527).trans
          (by decide +kernel))
    have r8422_10527 : (∑ k ∈ Ico (8422 : ℕ) 10527, (k : ZMod (16843^3))⁻¹) = 1155260278449 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 8422 ≤ 9474) (by decide : 9474 ≤ 10527)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r8422_9474 r9474_10527).trans
          (by decide +kernel))
    have r10527_10790 : (∑ k ∈ Ico (10527 : ℕ) 10790, (k : ZMod (16843^3))⁻¹) = 1209967556623 := by
      decide +kernel
    have r10790_11053 : (∑ k ∈ Ico (10790 : ℕ) 11053, (k : ZMod (16843^3))⁻¹) = 1977484134182 := by
      decide +kernel
    have r10527_11053 : (∑ k ∈ Ico (10527 : ℕ) 11053, (k : ZMod (16843^3))⁻¹) = 3187451690805 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 10527 ≤ 10790) (by decide : 10790 ≤ 11053)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r10527_10790 r10790_11053).trans
          (by decide +kernel))
    have r11053_11316 : (∑ k ∈ Ico (11053 : ℕ) 11316, (k : ZMod (16843^3))⁻¹) = 3233645395927 := by
      decide +kernel
    have r11316_11579 : (∑ k ∈ Ico (11316 : ℕ) 11579, (k : ZMod (16843^3))⁻¹) = 1406183036564 := by
      decide +kernel
    have r11053_11579 : (∑ k ∈ Ico (11053 : ℕ) 11579, (k : ZMod (16843^3))⁻¹) = 4639828432491 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 11053 ≤ 11316) (by decide : 11316 ≤ 11579)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r11053_11316 r11316_11579).trans
          (by decide +kernel))
    have r10527_11579 : (∑ k ∈ Ico (10527 : ℕ) 11579, (k : ZMod (16843^3))⁻¹) = 3049145894189 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 10527 ≤ 11053) (by decide : 11053 ≤ 11579)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r10527_11053 r11053_11579).trans
          (by decide +kernel))
    have r11579_11842 : (∑ k ∈ Ico (11579 : ℕ) 11842, (k : ZMod (16843^3))⁻¹) = 3555344733472 := by
      decide +kernel
    have r11842_12105 : (∑ k ∈ Ico (11842 : ℕ) 12105, (k : ZMod (16843^3))⁻¹) = 1615686948554 := by
      decide +kernel
    have r11579_12105 : (∑ k ∈ Ico (11579 : ℕ) 12105, (k : ZMod (16843^3))⁻¹) = 392897452919 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 11579 ≤ 11842) (by decide : 11842 ≤ 12105)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r11579_11842 r11842_12105).trans
          (by decide +kernel))
    have r12105_12368 : (∑ k ∈ Ico (12105 : ℕ) 12368, (k : ZMod (16843^3))⁻¹) = 3521765024464 := by
      decide +kernel
    have r12368_12632 : (∑ k ∈ Ico (12368 : ℕ) 12632, (k : ZMod (16843^3))⁻¹) = 1757956935794 := by
      decide +kernel
    have r12105_12632 : (∑ k ∈ Ico (12105 : ℕ) 12632, (k : ZMod (16843^3))⁻¹) = 501587731151 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 12105 ≤ 12368) (by decide : 12368 ≤ 12632)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r12105_12368 r12368_12632).trans
          (by decide +kernel))
    have r11579_12632 : (∑ k ∈ Ico (11579 : ℕ) 12632, (k : ZMod (16843^3))⁻¹) = 894485184070 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 11579 ≤ 12105) (by decide : 12105 ≤ 12632)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r11579_12105 r12105_12632).trans
          (by decide +kernel))
    have r10527_12632 : (∑ k ∈ Ico (10527 : ℕ) 12632, (k : ZMod (16843^3))⁻¹) = 3943631078259 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 10527 ≤ 11579) (by decide : 11579 ≤ 12632)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r10527_11579 r11579_12632).trans
          (by decide +kernel))
    have r8422_12632 : (∑ k ∈ Ico (8422 : ℕ) 12632, (k : ZMod (16843^3))⁻¹) = 320757127601 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 8422 ≤ 10527) (by decide : 10527 ≤ 12632)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r8422_10527 r10527_12632).trans
          (by decide +kernel))
    have r12632_12895 : (∑ k ∈ Ico (12632 : ℕ) 12895, (k : ZMod (16843^3))⁻¹) = 497723146169 := by
      decide +kernel
    have r12895_13158 : (∑ k ∈ Ico (12895 : ℕ) 13158, (k : ZMod (16843^3))⁻¹) = 2253459151348 := by
      decide +kernel
    have r12632_13158 : (∑ k ∈ Ico (12632 : ℕ) 13158, (k : ZMod (16843^3))⁻¹) = 2751182297517 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 12632 ≤ 12895) (by decide : 12895 ≤ 13158)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r12632_12895 r12895_13158).trans
          (by decide +kernel))
    have r13158_13421 : (∑ k ∈ Ico (13158 : ℕ) 13421, (k : ZMod (16843^3))⁻¹) = 2673285654648 := by
      decide +kernel
    have r13421_13684 : (∑ k ∈ Ico (13421 : ℕ) 13684, (k : ZMod (16843^3))⁻¹) = 27988817683 := by
      decide +kernel
    have r13158_13684 : (∑ k ∈ Ico (13158 : ℕ) 13684, (k : ZMod (16843^3))⁻¹) = 2701274472331 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 13158 ≤ 13421) (by decide : 13421 ≤ 13684)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r13158_13421 r13421_13684).trans
          (by decide +kernel))
    have r12632_13684 : (∑ k ∈ Ico (12632 : ℕ) 13684, (k : ZMod (16843^3))⁻¹) = 674322540741 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 12632 ≤ 13158) (by decide : 13158 ≤ 13684)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r12632_13158 r13158_13684).trans
          (by decide +kernel))
    have r13684_13947 : (∑ k ∈ Ico (13684 : ℕ) 13947, (k : ZMod (16843^3))⁻¹) = 4752014365119 := by
      decide +kernel
    have r13947_14210 : (∑ k ∈ Ico (13947 : ℕ) 14210, (k : ZMod (16843^3))⁻¹) = 323656884653 := by
      decide +kernel
    have r13684_14210 : (∑ k ∈ Ico (13684 : ℕ) 14210, (k : ZMod (16843^3))⁻¹) = 297537020665 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 13684 ≤ 13947) (by decide : 13947 ≤ 14210)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r13684_13947 r13947_14210).trans
          (by decide +kernel))
    have r14210_14473 : (∑ k ∈ Ico (14210 : ℕ) 14473, (k : ZMod (16843^3))⁻¹) = 783437645442 := by
      decide +kernel
    have r14473_14737 : (∑ k ∈ Ico (14473 : ℕ) 14737, (k : ZMod (16843^3))⁻¹) = 3228561547966 := by
      decide +kernel
    have r14210_14737 : (∑ k ∈ Ico (14210 : ℕ) 14737, (k : ZMod (16843^3))⁻¹) = 4011999193408 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 14210 ≤ 14473) (by decide : 14473 ≤ 14737)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r14210_14473 r14473_14737).trans
          (by decide +kernel))
    have r13684_14737 : (∑ k ∈ Ico (13684 : ℕ) 14737, (k : ZMod (16843^3))⁻¹) = 4309536214073 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 13684 ≤ 14210) (by decide : 14210 ≤ 14737)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r13684_14210 r14210_14737).trans
          (by decide +kernel))
    have r12632_14737 : (∑ k ∈ Ico (12632 : ℕ) 14737, (k : ZMod (16843^3))⁻¹) = 205724525707 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 12632 ≤ 13684) (by decide : 13684 ≤ 14737)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r12632_13684 r13684_14737).trans
          (by decide +kernel))
    have r14737_15000 : (∑ k ∈ Ico (14737 : ℕ) 15000, (k : ZMod (16843^3))⁻¹) = 698465562658 := by
      decide +kernel
    have r15000_15263 : (∑ k ∈ Ico (15000 : ℕ) 15263, (k : ZMod (16843^3))⁻¹) = 1121594262417 := by
      decide +kernel
    have r14737_15263 : (∑ k ∈ Ico (14737 : ℕ) 15263, (k : ZMod (16843^3))⁻¹) = 1820059825075 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 14737 ≤ 15000) (by decide : 15000 ≤ 15263)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r14737_15000 r15000_15263).trans
          (by decide +kernel))
    have r15263_15526 : (∑ k ∈ Ico (15263 : ℕ) 15526, (k : ZMod (16843^3))⁻¹) = 4037764149014 := by
      decide +kernel
    have r15526_15790 : (∑ k ∈ Ico (15526 : ℕ) 15790, (k : ZMod (16843^3))⁻¹) = 99180922428 := by
      decide +kernel
    have r15263_15790 : (∑ k ∈ Ico (15263 : ℕ) 15790, (k : ZMod (16843^3))⁻¹) = 4136945071442 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 15263 ≤ 15526) (by decide : 15526 ≤ 15790)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r15263_15526 r15526_15790).trans
          (by decide +kernel))
    have r14737_15790 : (∑ k ∈ Ico (14737 : ℕ) 15790, (k : ZMod (16843^3))⁻¹) = 1178870667410 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 14737 ≤ 15263) (by decide : 15263 ≤ 15790)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r14737_15263 r15263_15790).trans
          (by decide +kernel))
    have r15790_16053 : (∑ k ∈ Ico (15790 : ℕ) 16053, (k : ZMod (16843^3))⁻¹) = 318876092706 := by
      decide +kernel
    have r16053_16316 : (∑ k ∈ Ico (16053 : ℕ) 16316, (k : ZMod (16843^3))⁻¹) = 4276729385911 := by
      decide +kernel
    have r15790_16316 : (∑ k ∈ Ico (15790 : ℕ) 16316, (k : ZMod (16843^3))⁻¹) = 4595605478617 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 15790 ≤ 16053) (by decide : 16053 ≤ 16316)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r15790_16053 r16053_16316).trans
          (by decide +kernel))
    have r16316_16579 : (∑ k ∈ Ico (16316 : ℕ) 16579, (k : ZMod (16843^3))⁻¹) = 4475432042571 := by
      decide +kernel
    have r16579_16843 : (∑ k ∈ Ico (16579 : ℕ) 16843, (k : ZMod (16843^3))⁻¹) = 363845328773 := by
      decide +kernel
    have r16316_16843 : (∑ k ∈ Ico (16316 : ℕ) 16843, (k : ZMod (16843^3))⁻¹) = 61143142237 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 16316 ≤ 16579) (by decide : 16579 ≤ 16843)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r16316_16579 r16579_16843).trans
          (by decide +kernel))
    have r15790_16843 : (∑ k ∈ Ico (15790 : ℕ) 16843, (k : ZMod (16843^3))⁻¹) = 4656748620854 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 15790 ≤ 16316) (by decide : 16316 ≤ 16843)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r15790_16316 r16316_16843).trans
          (by decide +kernel))
    have r14737_16843 : (∑ k ∈ Ico (14737 : ℕ) 16843, (k : ZMod (16843^3))⁻¹) = 1057485059157 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 14737 ≤ 15790) (by decide : 15790 ≤ 16843)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r14737_15790 r15790_16843).trans
          (by decide +kernel))
    have r12632_16843 : (∑ k ∈ Ico (12632 : ℕ) 16843, (k : ZMod (16843^3))⁻¹) = 1263209584864 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 12632 ≤ 14737) (by decide : 14737 ≤ 16843)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r12632_14737 r14737_16843).trans
          (by decide +kernel))
    have r8422_16843 : (∑ k ∈ Ico (8422 : ℕ) 16843, (k : ZMod (16843^3))⁻¹) = 1583966712465 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 8422 ≤ 12632) (by decide : 12632 ≤ 16843)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r8422_12632 r12632_16843).trans
          (by decide +kernel))
    have r1_16843 : (∑ k ∈ Ico (1 : ℕ) 16843, (k : ZMod (16843^3))⁻¹) = 0 :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (by decide : 1 ≤ 8422) (by decide : 8422 ≤ 16843)).symm.trans
        ((congrArg₂ (fun a b : ZMod (16843^3) => a + b) r1_8422 r8422_16843).trans
          (by decide +kernel))
    exact r1_16843
  have hp : Nat.Prime 16843 := by norm_num
  have hdiv : 16843^3 ∣ A (16843^3 - 1) := by
    apply prime_cube_divides 16843 hp (by norm_num)
    change (∑ k ∈ Icc (1 : ℕ) 16842, (k : ZMod (16843^3))⁻¹) = 0
    rw [← Ico_add_one_right_eq_Icc]
    exact residue
  have hcube : (16843 : ℕ)^3 = 4778134229107 := by norm_num
  have hcounter := hclaim 4778134229107
  rw [← hcube] at hcounter
  obtain ⟨q, hq, _, heq⟩ := hcounter
    ⟨by norm_num, Nat.Prime.not_prime_pow (by norm_num : 2 ≤ 3), hdiv⟩
  have hd : 16843 ∣ q^2 := heq ▸ dvd_pow_self 16843 (by decide : 3 ≠ 0)
  have he : 16843 = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hd)
  rw [← he] at heq
  norm_num at heq

end D5.S3.ArithSums.A025529PrimeCubeRefutation
