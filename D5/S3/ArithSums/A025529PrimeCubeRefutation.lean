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
    let S (a b : ℕ) : ZMod (16843^3) := ∑ k ∈ Ico a b, (k : ZMod (16843^3))⁻¹
    have j {a b c : ℕ} {x y : ZMod (16843^3)} (h : decide (a ≤ b ∧ b ≤ c) = true)
        (hx : S a b = x) (hy : S b c = y) : S a c = x + y :=
      (sum_Ico_consecutive (fun k : ℕ => (k : ZMod (16843^3))⁻¹)
        (of_decide_eq_true h).1 (of_decide_eq_true h).2).symm.trans
        (congrArg₂ (fun x y : ZMod (16843^3) => x + y) hx hy)
    have r0 : S 1 264 = 471428010868 := by decide +kernel
    have r1 : S 264 527 = 1079740593648 := by decide +kernel
    have r2 : S 1 527 = 1551168604516 := (j rfl r0 r1).trans (by decide +kernel)
    have r3 : S 527 790 = 4525174035128 := by decide +kernel
    have r4 : S 790 1053 = 342026242703 := by decide +kernel
    have r5 : S 527 1053 = 89066048724 := (j rfl r3 r4).trans (by decide +kernel)
    have r6 : S 1 1053 = 1640234653240 := (j rfl r2 r5).trans (by decide +kernel)
    have r7 : S 1053 1316 = 2259937017727 := by decide +kernel
    have r8 : S 1316 1579 = 2712265615000 := by decide +kernel
    have r9 : S 1053 1579 = 194068403620 := (j rfl r7 r8).trans (by decide +kernel)
    have r10 : S 1579 1842 = 250464687490 := by decide +kernel
    have r11 : S 1842 2106 = 3928151190908 := by decide +kernel
    have r12 : S 1579 2106 = 4178615878398 := (j rfl r10 r11).trans (by decide +kernel)
    have r13 : S 1053 2106 = 4372684282018 := (j rfl r9 r12).trans (by decide +kernel)
    have r14 : S 1 2106 = 1234784706151 := (j rfl r6 r13).trans (by decide +kernel)
    have r15 : S 2106 2369 = 3682614178791 := by decide +kernel
    have r16 : S 2369 2632 = 957741191781 := by decide +kernel
    have r17 : S 2106 2632 = 4640355370572 := (j rfl r15 r16).trans (by decide +kernel)
    have r18 : S 2632 2895 = 4308946959374 := by decide +kernel
    have r19 : S 2895 3158 = 1936715224557 := by decide +kernel
    have r20 : S 2632 3158 = 1467527954824 := (j rfl r18 r19).trans (by decide +kernel)
    have r21 : S 2106 3158 = 1329749096289 := (j rfl r17 r20).trans (by decide +kernel)
    have r22 : S 3158 3421 = 1694777027943 := by decide +kernel
    have r23 : S 3421 3684 = 3239055884524 := by decide +kernel
    have r24 : S 3158 3684 = 155698683360 := (j rfl r22 r23).trans (by decide +kernel)
    have r25 : S 3684 3947 = 878290529986 := by decide +kernel
    have r26 : S 3947 4211 = 28863366876 := by decide +kernel
    have r27 : S 3684 4211 = 907153896862 := (j rfl r25 r26).trans (by decide +kernel)
    have r28 : S 3158 4211 = 1062852580222 := (j rfl r24 r27).trans (by decide +kernel)
    have r29 : S 2106 4211 = 2392601676511 := (j rfl r21 r28).trans (by decide +kernel)
    have r30 : S 1 4211 = 3627386382662 := (j rfl r14 r29).trans (by decide +kernel)
    have r31 : S 4211 4474 = 4355925571167 := by decide +kernel
    have r32 : S 4474 4737 = 4622792245918 := by decide +kernel
    have r33 : S 4211 4737 = 4200583587978 := (j rfl r31 r32).trans (by decide +kernel)
    have r34 : S 4737 5000 = 1068420271104 := by decide +kernel
    have r35 : S 5000 5263 = 4574005484936 := by decide +kernel
    have r36 : S 4737 5263 = 864291526933 := (j rfl r34 r35).trans (by decide +kernel)
    have r37 : S 4211 5263 = 286740885804 := (j rfl r33 r36).trans (by decide +kernel)
    have r38 : S 5263 5526 = 4632508613183 := by decide +kernel
    have r39 : S 5526 5789 = 337294221225 := by decide +kernel
    have r40 : S 5263 5789 = 191668605301 := (j rfl r38 r39).trans (by decide +kernel)
    have r41 : S 5789 6052 = 2564753083555 := by decide +kernel
    have r42 : S 6052 6316 = 2059706723211 := by decide +kernel
    have r43 : S 5789 6316 = 4624459806766 := (j rfl r41 r42).trans (by decide +kernel)
    have r44 : S 5263 6316 = 37994182960 := (j rfl r40 r43).trans (by decide +kernel)
    have r45 : S 4211 6316 = 324735068764 := (j rfl r37 r44).trans (by decide +kernel)
    have r46 : S 6316 6579 = 4092072657436 := by decide +kernel
    have r47 : S 6579 6842 = 3608764213878 := by decide +kernel
    have r48 : S 6316 6842 = 2922702642207 := (j rfl r46 r47).trans (by decide +kernel)
    have r49 : S 6842 7105 = 1827926241833 := by decide +kernel
    have r50 : S 7105 7369 = 3101728667931 := by decide +kernel
    have r51 : S 6842 7369 = 151520680657 := (j rfl r49 r50).trans (by decide +kernel)
    have r52 : S 6316 7369 = 3074223322864 := (j rfl r48 r51).trans (by decide +kernel)
    have r53 : S 7369 7632 = 450618777288 := by decide +kernel
    have r54 : S 7632 7895 = 2141764787583 := by decide +kernel
    have r55 : S 7369 7895 = 2592383564871 := (j rfl r53 r54).trans (by decide +kernel)
    have r56 : S 7895 8158 = 3270514678745 := by decide +kernel
    have r57 : S 8158 8422 = 4639327186057 := by decide +kernel
    have r58 : S 7895 8422 = 3131707635695 := (j rfl r56 r57).trans (by decide +kernel)
    have r59 : S 7369 8422 = 945956971459 := (j rfl r55 r58).trans (by decide +kernel)
    have r60 : S 6316 8422 = 4020180294323 := (j rfl r52 r59).trans (by decide +kernel)
    have r61 : S 4211 8422 = 4344915363087 := (j rfl r45 r60).trans (by decide +kernel)
    have r62 : S 1 8422 = 3194167516642 := (j rfl r30 r61).trans (by decide +kernel)
    have r63 : S 8422 8685 = 3706381942250 := by decide +kernel
    have r64 : S 8685 8948 = 2397121131081 := by decide +kernel
    have r65 : S 8422 8948 = 1325368844224 := (j rfl r63 r64).trans (by decide +kernel)
    have r66 : S 8948 9211 = 327266266689 := by decide +kernel
    have r67 : S 9211 9474 = 1190193871107 := by decide +kernel
    have r68 : S 8948 9474 = 1517460137796 := (j rfl r66 r67).trans (by decide +kernel)
    have r69 : S 8422 9474 = 2842828982020 := (j rfl r65 r68).trans (by decide +kernel)
    have r70 : S 9474 9737 = 4504229588705 := by decide +kernel
    have r71 : S 9737 10000 = 2013446770584 := by decide +kernel
    have r72 : S 9474 10000 = 1739542130182 := (j rfl r70 r71).trans (by decide +kernel)
    have r73 : S 10000 10263 = 5868525872 := by decide +kernel
    have r74 : S 10263 10527 = 1345154869482 := by decide +kernel
    have r75 : S 10000 10527 = 1351023395354 := (j rfl r73 r74).trans (by decide +kernel)
    have r76 : S 9474 10527 = 3090565525536 := (j rfl r72 r75).trans (by decide +kernel)
    have r77 : S 8422 10527 = 1155260278449 := (j rfl r69 r76).trans (by decide +kernel)
    have r78 : S 10527 10790 = 1209967556623 := by decide +kernel
    have r79 : S 10790 11053 = 1977484134182 := by decide +kernel
    have r80 : S 10527 11053 = 3187451690805 := (j rfl r78 r79).trans (by decide +kernel)
    have r81 : S 11053 11316 = 3233645395927 := by decide +kernel
    have r82 : S 11316 11579 = 1406183036564 := by decide +kernel
    have r83 : S 11053 11579 = 4639828432491 := (j rfl r81 r82).trans (by decide +kernel)
    have r84 : S 10527 11579 = 3049145894189 := (j rfl r80 r83).trans (by decide +kernel)
    have r85 : S 11579 11842 = 3555344733472 := by decide +kernel
    have r86 : S 11842 12105 = 1615686948554 := by decide +kernel
    have r87 : S 11579 12105 = 392897452919 := (j rfl r85 r86).trans (by decide +kernel)
    have r88 : S 12105 12368 = 3521765024464 := by decide +kernel
    have r89 : S 12368 12632 = 1757956935794 := by decide +kernel
    have r90 : S 12105 12632 = 501587731151 := (j rfl r88 r89).trans (by decide +kernel)
    have r91 : S 11579 12632 = 894485184070 := (j rfl r87 r90).trans (by decide +kernel)
    have r92 : S 10527 12632 = 3943631078259 := (j rfl r84 r91).trans (by decide +kernel)
    have r93 : S 8422 12632 = 320757127601 := (j rfl r77 r92).trans (by decide +kernel)
    have r94 : S 12632 12895 = 497723146169 := by decide +kernel
    have r95 : S 12895 13158 = 2253459151348 := by decide +kernel
    have r96 : S 12632 13158 = 2751182297517 := (j rfl r94 r95).trans (by decide +kernel)
    have r97 : S 13158 13421 = 2673285654648 := by decide +kernel
    have r98 : S 13421 13684 = 27988817683 := by decide +kernel
    have r99 : S 13158 13684 = 2701274472331 := (j rfl r97 r98).trans (by decide +kernel)
    have r100 : S 12632 13684 = 674322540741 := (j rfl r96 r99).trans (by decide +kernel)
    have r101 : S 13684 13947 = 4752014365119 := by decide +kernel
    have r102 : S 13947 14210 = 323656884653 := by decide +kernel
    have r103 : S 13684 14210 = 297537020665 := (j rfl r101 r102).trans (by decide +kernel)
    have r104 : S 14210 14473 = 783437645442 := by decide +kernel
    have r105 : S 14473 14737 = 3228561547966 := by decide +kernel
    have r106 : S 14210 14737 = 4011999193408 := (j rfl r104 r105).trans (by decide +kernel)
    have r107 : S 13684 14737 = 4309536214073 := (j rfl r103 r106).trans (by decide +kernel)
    have r108 : S 12632 14737 = 205724525707 := (j rfl r100 r107).trans (by decide +kernel)
    have r109 : S 14737 15000 = 698465562658 := by decide +kernel
    have r110 : S 15000 15263 = 1121594262417 := by decide +kernel
    have r111 : S 14737 15263 = 1820059825075 := (j rfl r109 r110).trans (by decide +kernel)
    have r112 : S 15263 15526 = 4037764149014 := by decide +kernel
    have r113 : S 15526 15790 = 99180922428 := by decide +kernel
    have r114 : S 15263 15790 = 4136945071442 := (j rfl r112 r113).trans (by decide +kernel)
    have r115 : S 14737 15790 = 1178870667410 := (j rfl r111 r114).trans (by decide +kernel)
    have r116 : S 15790 16053 = 318876092706 := by decide +kernel
    have r117 : S 16053 16316 = 4276729385911 := by decide +kernel
    have r118 : S 15790 16316 = 4595605478617 := (j rfl r116 r117).trans (by decide +kernel)
    have r119 : S 16316 16579 = 4475432042571 := by decide +kernel
    have r120 : S 16579 16843 = 363845328773 := by decide +kernel
    have r121 : S 16316 16843 = 61143142237 := (j rfl r119 r120).trans (by decide +kernel)
    have r122 : S 15790 16843 = 4656748620854 := (j rfl r118 r121).trans (by decide +kernel)
    have r123 : S 14737 16843 = 1057485059157 := (j rfl r115 r122).trans (by decide +kernel)
    have r124 : S 12632 16843 = 1263209584864 := (j rfl r108 r123).trans (by decide +kernel)
    have r125 : S 8422 16843 = 1583966712465 := (j rfl r93 r124).trans (by decide +kernel)
    exact (j rfl r62 r125).trans (by decide +kernel)
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
