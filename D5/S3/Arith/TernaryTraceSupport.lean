/- GID: D5/S3/Arith/TernaryTraceSupport
   generality: I
   mirror-B: D5/B/S3/Arith/TernaryTraceSupport
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Ternary trace identities for the exact mod-three support of A396808. -/

import Mathlib.Tactic.ReduceModChar
import D5.S3.Arith.ArtinSchreierTracePowersOfTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped PowerSeries
open Finset Polynomial

namespace D5.S3.Arith.TernaryTraceSupport
noncomputable section
open D5.S3.Arith.ArtinSchreierTracePowersOfTwo
private abbrev F3 := ZMod 3

private theorem coeff_pow_add_monomial
    {R : Type*} [CommRing R] (p : R[X]) (n m : ℕ) (c : R)
    (hn : 0 < n) (hm : 0 < m) (hp0 : p.coeff 0 = 1) :
    ((p + Polynomial.monomial n c) ^ m).coeff n =
      (p ^ m).coeff n + (m : R) * c := by
  classical
  rw [add_comm, (Commute.all (Polynomial.monomial n c) p).add_pow,
    Polynomial.finsetSum_coeff]
  let f : ℕ → R := fun k =>
    ((Polynomial.monomial n c) ^ k * p ^ (m - k) *
      Polynomial.C (m.choose k : R)).coeff n
  have hf0 : f 0 = (p ^ m).coeff n := by
    simp [f]
  have hf1 : f 1 = (m : R) * c := by
    have hconst : ∀ k : ℕ, (p ^ k).coeff 0 = 1 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => simp [pow_succ, Polynomial.mul_coeff_zero, ih, hp0]
    have hcoef : ((Polynomial.monomial n c) * p ^ (m - 1)).coeff n = c := by
      simpa [hconst] using
        (Polynomial.coeff_monomial_mul (p ^ (m - 1)) n 0 c)
    have hcoef' : (p ^ (m - 1) * Polynomial.monomial n c).coeff n = c := by
      rw [mul_comm]
      exact hcoef
    simp [f, hcoef', mul_comm]
  have hfk : ∀ k ∈ Finset.range (m + 1), k ≠ 0 → k ≠ 1 → f k = 0 := by
    intro k hk hk0 hk1
    have hk2 : 2 ≤ k := by omega
    have hlarge : n < k * n := by nlinarith
    have hnle : ¬n * k ≤ n := by nlinarith
    simp only [f, Polynomial.monomial_pow]
    rw [Polynomial.coeff_mul_C, ← Polynomial.C_mul_X_pow_eq_monomial,
      mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    simp [hnle]
  change (∑ k ∈ Finset.range (m + 1), f k) = _
  let s := Finset.range (m + 1)
  have h0 : 0 ∈ s := by simp [s]
  have h1 : 1 ∈ s.erase 0 := by simp [s, hm]
  calc
    (∑ k ∈ s, f k) = f 0 + ∑ k ∈ s.erase 0, f k :=
      (Finset.add_sum_erase s f h0).symm
    _ = f 0 + f 1 := by
      rw [Finset.sum_eq_single 1]
      · intro k hk hk1'
        exact hfk k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk) hk1'
      · exact fun hnot => False.elim (hnot h1)
    _ = (p ^ m).coeff n + (m : R) * c := by rw [hf0, hf1]

private theorem coeff_pow_eq_coeff_trunc_pow
    {R : Type*} [CommRing R] (f : R⟦X⟧) (n m : ℕ) :
    PowerSeries.coeff n (f ^ m) = ((PowerSeries.trunc (n + 1) f) ^ m).coeff n := by
  have h := congrArg (fun p : R[X] => p.coeff n)
    (PowerSeries.trunc_trunc_pow f (n + 1) m)
  calc
    PowerSeries.coeff n (f ^ m) =
        PowerSeries.coeff n ((PowerSeries.trunc (n + 1) f : R⟦X⟧) ^ m) := by
      simpa only [PowerSeries.coeff_trunc, Nat.lt_succ_iff, le_rfl, if_true,
        Polynomial.coeff_coe] using h.symm
    _ = PowerSeries.coeff n ((↑((PowerSeries.trunc (n + 1) f) ^ m)) : R⟦X⟧) := by
      rw [Polynomial.coe_pow]
    _ = ((PowerSeries.trunc (n + 1) f) ^ m).coeff n :=
      Polynomial.coeff_coe _ _

private theorem coeff_pow_eq_strict_trunc_add
    {R : Type*} [CommRing R] (f : R⟦X⟧) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hf0 : PowerSeries.coeff 0 f = 1) :
    PowerSeries.coeff n (f ^ m) =
      ((PowerSeries.trunc n f) ^ m).coeff n + (m : R) * PowerSeries.coeff n f := by
  rw [coeff_pow_eq_coeff_trunc_pow, PowerSeries.trunc_succ]
  exact coeff_pow_add_monomial (PowerSeries.trunc n f) n m
    (PowerSeries.coeff n f) hn hm (by simpa [PowerSeries.coeff_trunc, hn] using hf0)


private theorem recursion_of_source {K : Type*} [CommRing K] (f : K⟦X⟧)
    (hf0 : PowerSeries.coeff 0 f = 1)
    (n : ℕ) (hn : 1 < n)
    (hs : (n + 1 : K) * PowerSeries.coeff n (f ^ (n + 1)) =
      (n : K) * PowerSeries.coeff n (f ^ (n + 2))) :
    PowerSeries.coeff n f =
      (n : K) * ((PowerSeries.trunc n f) ^ (n + 2)).coeff n -
      (n + 1 : K) * ((PowerSeries.trunc n f) ^ (n + 1)).coeff n := by
  have h1 := coeff_pow_eq_strict_trunc_add f n (n + 1) (by omega) (by omega) hf0
  have h2 := coeff_pow_eq_strict_trunc_add f n (n + 2) (by omega) (by omega) hf0
  rw [h1, h2] at hs
  push_cast at hs ⊢
  linear_combination hs

private theorem source_unique {K : Type*} [CommRing K] (f g : K⟦X⟧)
    (hf0 : PowerSeries.coeff 0 f = 1) (hg0 : PowerSeries.coeff 0 g = 1)
    (hf1 : PowerSeries.coeff 1 f = 1) (hg1 : PowerSeries.coeff 1 g = 1)
    (hsf : ∀ n : ℕ, 1 < n →
      (n + 1 : K) * PowerSeries.coeff n (f ^ (n + 1)) =
        (n : K) * PowerSeries.coeff n (f ^ (n + 2)))
    (hsg : ∀ n : ℕ, 1 < n →
      (n + 1 : K) * PowerSeries.coeff n (g ^ (n + 1)) =
        (n : K) * PowerSeries.coeff n (g ^ (n + 2))) : f = g := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        exact hf0.trans hg0.symm
      by_cases hn1 : n = 1
      · subst n
        exact hf1.trans hg1.symm
      have hn : 1 < n := by omega
      have ht : PowerSeries.trunc n f = PowerSeries.trunc n g := by
        ext j
        simp only [PowerSeries.coeff_trunc]
        split_ifs with hj
        · exact ih j hj
        · rfl
      rw [recursion_of_source f hf0 n hn (hsf n hn),
        recursion_of_source g hg0 n hn (hsg n hn), ht]

private def reducedSeries : F3⟦X⟧ :=
  PowerSeries.map (Int.castRingHom F3) (PowerSeries.mk a)

@[simp] private theorem coeff_reducedSeries (n : ℕ) :
    PowerSeries.coeff n reducedSeries = (a n : F3) := by
  simp [reducedSeries]

private theorem reduced_source_equation (n : ℕ) (hn : 1 < n) :
    (n + 1 : F3) * PowerSeries.coeff n (reducedSeries ^ (n + 1)) =
      (n : F3) * PowerSeries.coeff n (reducedSeries ^ (n + 2)) := by
  simp only [reducedSeries, ← map_pow, PowerSeries.coeff_map]
  simpa using congrArg (Int.castRingHom F3) (source_equation n hn)

private theorem reduced_zero : PowerSeries.coeff 0 reducedSeries = 1 := by
  rw [coeff_reducedSeries]
  have h : a 0 = 1 := rfl
  rw [h]
  rfl

private theorem reduced_one : PowerSeries.coeff 1 reducedSeries = 1 := by
  rw [coeff_reducedSeries]
  have h : a 1 = 1 := rfl
  rw [h]
  rfl


private abbrev PS := F3⟦X⟧

private instance : CharP PS 3 :=
  charP_of_injective_ringHom PowerSeries.C_injective 3

private def tracePoly : ℕ → F3[X]
  | 0 => 0
  | 1 => 1
  | 2 => 1 + 2 * Polynomial.X
  | m + 3 => tracePoly (m + 2) + Polynomial.X * tracePoly (m + 1) +
      Polynomial.X ^ 2 * tracePoly m

private theorem trace_degree (m : ℕ) : (tracePoly m).natDegree ≤ 2 * m / 3 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | _ | _ | m
    · simp [tracePoly]
    · simp [tracePoly]
    · norm_num [tracePoly]
      apply Polynomial.natDegree_add_le_of_degree_le
      · simp
      · exact (Polynomial.natDegree_mul_le).trans (by norm_num)
    · change (tracePoly (m+3)).natDegree ≤ _
      rw [tracePoly]
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · apply (Polynomial.natDegree_add_le _ _).trans
        apply max_le
        · have h := ih (m+2) (by omega)
          omega
        · apply Polynomial.natDegree_mul_le.trans
          have h := ih (m+1) (by omega)
          simp only [Polynomial.natDegree_X]
          omega
      · apply Polynomial.natDegree_mul_le.trans
        have h := ih m (by omega)
        simp only [Polynomial.natDegree_X_pow]
        omega

private theorem cube_identity (t : PS) :
    (1+t^2+t^4)^3 = (1+t^2+t^4)^2 + (t-t^3)^2*(1+t^2+t^4) + (t-t^3)^4 := by
  have : CharP PS 3 := inferInstance
  ring_nf
  reduce_mod_char!
  ring_nf
  reduce_mod_char!

private theorem cube_plus (t : PS) :
    ((t^2+t)^2)^3 = ((t^2+t)^2)^2 + (t-t^3)^2*((t^2+t)^2) + (t-t^3)^4 := by
  have : CharP PS 3 := inferInstance
  ring_nf
  reduce_mod_char!


private theorem cube_minus (t : PS) :
    ((t^2-t)^2)^3 = ((t^2-t)^2)^2 + (t-t^3)^2*((t^2-t)^2) + (t-t^3)^4 := by
  have : CharP PS 3 := inferInstance
  ring_nf
  reduce_mod_char!


private theorem roots_sum (t : PS) :
    (1+t^2+t^4) + (t^2+t)^2 + (t^2-t)^2 = 1 := by
  have : CharP PS 3 := inferInstance
  ring_nf
  reduce_mod_char!


private theorem roots_squares (t : PS) :
    (1+t^2+t^4)^2 + ((t^2+t)^2)^2 + ((t^2-t)^2)^2 = 1 + 2*(t-t^3)^2 := by
  have : CharP PS 3 := inferInstance
  ring_nf
  reduce_mod_char!
  ring_nf

private theorem root_pow (z : PS)
    (hz : z^3 = z^2 + PowerSeries.X^2*z + PowerSeries.X^4) (m : ℕ) :
    z^(m+3) = z^(m+2) + PowerSeries.X^2*z^(m+1) + PowerSeries.X^4*z^m := by
  calc
    z^(m+3) = z^m*z^3 := pow_add _ _ _
    _ = _ := by rw [hz]; ring

private theorem trace_identity (t : PS) (ht : t^3 = t - PowerSeries.X) (m : ℕ) :
    PowerSeries.expand 2 (by decide) (tracePoly m : PS) =
      (1+t^2+t^4)^m + ((t^2+t)^2)^m + ((t^2-t)^2)^m := by
  have hx : t-t^3 = PowerSeries.X := by linear_combination -ht
  have h0 := cube_identity t
  have h1 := cube_plus t
  have h2 := cube_minus t
  rw [hx] at h0 h1 h2
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases m with _ | _ | _ | m
    · simp only [tracePoly, Polynomial.coe_zero, map_zero, pow_zero]
      have : CharP PS 3 := inferInstance
      ring_nf
      reduce_mod_char!
    · simpa [tracePoly] using (roots_sum t).symm
    · have hs := roots_squares t
      rw [hx] at hs
      have hc : ((2 : F3[X]) : PS) = 2 := by
        change (Polynomial.coeToPowerSeries.ringHom (2 : F3[X])) = 2
        exact map_ofNat _ _
      simpa [tracePoly, hc, map_ofNat] using hs.symm
    · rw [tracePoly, Polynomial.coe_add, Polynomial.coe_add, Polynomial.coe_mul,
        Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, map_add, map_add,
        map_mul, map_mul, map_pow, PowerSeries.expand_X,
        ih (m+2) (by omega), ih (m+1) (by omega), ih m (by omega),
        root_pow _ h0, root_pow _ h1, root_pow _ h2]
      ring

private theorem coeff_root_pow_eq_zero (t : PS)
    (ht : t^3 = t - PowerSeries.X) (ht0 : PowerSeries.constantCoeff t = 0)
    (m n : ℕ) (hdegree : 2*m/3 < n) (hexponent : n < m) :
    PowerSeries.coeff (2*n) ((1+t^2+t^4)^m) = 0 := by
  have hp : (tracePoly m).coeff n = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (trace_degree m) hdegree)
  have hv : PowerSeries.coeff (2*n) (((t^2+t)^2)^m) = 0 := by
    rw [← pow_mul]
    apply PowerSeries.coeff_of_lt_order
    apply lt_of_lt_of_le _ (PowerSeries.le_order_pow_of_constantCoeff_eq_zero (2*m)
      (by simp [ht0] : PowerSeries.constantCoeff (t^2+t) = 0))
    exact_mod_cast (by omega : 2*n < 2*m)
  have hw : PowerSeries.coeff (2*n) (((t^2-t)^2)^m) = 0 := by
    rw [← pow_mul]
    apply PowerSeries.coeff_of_lt_order
    apply lt_of_lt_of_le _ (PowerSeries.le_order_pow_of_constantCoeff_eq_zero (2*m)
      (by simp [ht0] : PowerSeries.constantCoeff (t^2-t) = 0))
    exact_mod_cast (by omega : 2*n < 2*m)
  have h := congrArg (PowerSeries.coeff (2*n)) (trace_identity t ht m)
  simp only [PowerSeries.coeff_expand_mul, Polynomial.coeff_coe, map_add, hp, hv, hw,
    add_zero] at h
  exact h.symm

private def t : PS := by
  classical
  exact PowerSeries.mk fun n => if ∃ r : ℕ, n = 3 ^ r then 1 else 0

private theorem power_mul_iff (n : ℕ) :
    (∃ r : ℕ, 3*n = (3:ℕ)^r) ↔ ∃ r : ℕ, n = (3:ℕ)^r := by
  constructor
  · rintro ⟨r, hr⟩
    cases r with
    | zero => simp at hr
    | succ r => exact ⟨r, by simp only [pow_succ] at hr; omega⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r+1, by simp [pow_succ, Nat.mul_comm]⟩

private theorem power_not_dvd {n : ℕ} (hn : ¬3 ∣ n) :
    (∃ r : ℕ, n=(3:ℕ)^r) ↔ n=1 := by
  constructor
  · rintro ⟨r,rfl⟩
    cases r with
    | zero => rfl
    | succ r => simp [pow_succ] at hn
  · rintro rfl
    exact ⟨0,rfl⟩

private theorem t_expand : PowerSeries.expand 3 (by decide) t = t - PowerSeries.X := by
  classical
  ext n
  rw [PowerSeries.coeff_expand, map_sub, PowerSeries.coeff_X]
  simp only [t, PowerSeries.coeff_mk]
  by_cases h : 3 ∣ n
  · obtain ⟨k, rfl⟩ := h
    rw [if_pos (by simp), Nat.mul_div_cancel_left _ (by decide), power_mul_iff,
      if_neg (show ¬3*k=1 by omega)]
    simp
  · rw [if_neg h, power_not_dvd h]
    split_ifs <;> simp

private theorem cube_eq_expand (f : PS) : f^3 = PowerSeries.expand 3 (by decide) f := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) 3 (by decide) (f := f)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id] at h
  exact h.symm

private theorem t_cube : t^3 = t - PowerSeries.X := by
  rw [cube_eq_expand, t_expand]

private theorem t_zero : PowerSeries.constantCoeff t = 0 := by
  classical
  simp only [t, PowerSeries.constantCoeff_mk]
  apply if_neg
  rintro ⟨r, hr⟩
  have : 0 < (3:ℕ)^r := pow_pos (by decide) _
  omega

private theorem power_pair_unique (i j k l : ℕ) (hij : i ≤ j) (hkl : k ≤ l)
    (heq : (3:ℕ)^i + (3:ℕ)^j = (3:ℕ)^k + (3:ℕ)^l) : i=k ∧ j=l := by
  have high : ∀ a b c d : ℕ, a ≤ b → b < d → (3:ℕ)^a + (3:ℕ)^b < (3:ℕ)^c + (3:ℕ)^d := by
    intro a b c d hab hbd
    have ha : (3:ℕ)^a ≤ (3:ℕ)^b := Nat.pow_le_pow_right (by decide) hab
    have hd : (3:ℕ)^(b+1) ≤ (3:ℕ)^d := Nat.pow_le_pow_right (by decide) hbd
    have hp : 0 < (3:ℕ)^b := pow_pos (by decide) _
    rw [pow_succ] at hd
    calc
      (3:ℕ)^a + (3:ℕ)^b ≤ 2*(3:ℕ)^b := by omega
      _ < (3:ℕ)^b*3 := by omega
      _ ≤ (3:ℕ)^d := hd
      _ ≤ (3:ℕ)^c + (3:ℕ)^d := Nat.le_add_left _ _
  have hjl : j=l := by
    rcases lt_trichotomy j l with h | h | h
    · have := high i j k l hij h; omega
    · exact h
    · have := high k l i j hkl h; omega
  subst l
  constructor
  · apply Nat.pow_right_injective (by decide : 2 ≤ 3)
    exact Nat.add_right_cancel heq
  · rfl


private def pairSet (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.antidiagonal n).filter fun p =>
    (∃ i : ℕ, p.1 = 3^i) ∧ (∃ j : ℕ, p.2 = 3^j)

private theorem coeff_square (n : ℕ) :
    PowerSeries.coeff n (t^2) = ((pairSet n).card : F3) := by
  classical
  rw [pow_two, PowerSeries.coeff_mul]
  simp only [t, PowerSeries.coeff_mk]
  simp only [pairSet, Finset.card_eq_sum_ones, Nat.cast_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp_all

private theorem pairSet_sum (i j : ℕ) (hij : i ≤ j) :
    pairSet (3^i+3^j) = {(3^i,3^j), (3^j,3^i)} := by
  classical
  ext p
  simp only [pairSet, Finset.mem_filter, Finset.mem_antidiagonal,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hs, ⟨k,hk⟩, ⟨l,hl⟩⟩
    rcases le_total k l with hkl | hlk
    · have heq : (3:ℕ)^i+3^j = 3^k+3^l := by omega
      obtain ⟨rfl,rfl⟩ := power_pair_unique i j k l hij hkl heq
      left
      exact Prod.ext hk hl
    · have heq : (3:ℕ)^i+3^j = 3^l+3^k := by omega
      obtain ⟨rfl,rfl⟩ := power_pair_unique i j l k hij hlk heq
      right
      exact Prod.ext hk hl
  · rintro (rfl | rfl)
    · exact ⟨rfl, ⟨i,rfl⟩, ⟨j,rfl⟩⟩
    · exact ⟨Nat.add_comm _ _, ⟨j,rfl⟩, ⟨i,rfl⟩⟩

private theorem coeff_square_diagonal (i : ℕ) :
    PowerSeries.coeff (2*3^i) (t^2) = 1 := by
  classical
  rw [show 2*3^i = 3^i+3^i by omega, coeff_square, pairSet_sum i i (by omega)]
  simp

private theorem coeff_square_off_diagonal (i j : ℕ) (hij : i < j) :
    PowerSeries.coeff (3^i+3^j) (t^2) = 2 := by
  classical
  rw [coeff_square, pairSet_sum i j (by omega)]
  have hne : (3:ℕ)^i ≠ 3^j := (Nat.pow_right_injective (by decide)).ne (by omega)
  simp [hne, hne.symm]

private theorem coeff_square_else (n : ℕ)
    (h : ¬∃ i j : ℕ, n = 3^i+3^j) : PowerSeries.coeff n (t^2) = 0 := by
  classical
  rw [coeff_square]
  have hempty : pairSet n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    simp only [pairSet, Finset.mem_filter, Finset.mem_antidiagonal] at hp
    obtain ⟨hs, ⟨i,hi⟩, ⟨j,hj⟩⟩ := hp
    exact h ⟨i,j,by omega⟩
  simp [hempty]

private theorem coeff_square_odd (n : ℕ) (hn : Odd n) :
    PowerSeries.coeff n (t^2) = 0 := by
  apply coeff_square_else
  rintro ⟨i,j,rfl⟩
  have hi : Odd ((3:ℕ)^i) := (by decide : Odd (3:ℕ)).pow
  have hj : Odd ((3:ℕ)^j) := (by decide : Odd (3:ℕ)).pow
  obtain ⟨a,ha⟩ := hi
  obtain ⟨b,hb⟩ := hj
  obtain ⟨c,hc⟩ := hn
  omega


private def U : PS := 1 + PowerSeries.X^2 - t^6
private def R : PS := PowerSeries.mk fun n => PowerSeries.coeff (2*n) U

private theorem U_eq : U = 1+t^2+t^4 := by
  have hx : t-t^3 = PowerSeries.X := by linear_combination -t_cube
  unfold U
  rw [← hx]
  have : CharP PS 3 := inferInstance
  ring_nf
  reduce_mod_char!
  ring_nf
  reduce_mod_char!

private theorem sixth_eq : t^6 = PowerSeries.expand 3 (by decide) (t^2) := by
  rw [← cube_eq_expand, ← pow_mul]

private theorem U_odd (k : ℕ) : PowerSeries.coeff (2*k+1) U = 0 := by
  have h6 : PowerSeries.coeff (2*k+1) (t^6) = 0 := by
    rw [sixth_eq, PowerSeries.coeff_expand]
    split_ifs with h
    · apply coeff_square_odd
      obtain ⟨q,hq⟩ := h
      have hdiv : (2*k+1)/3 = q := by omega
      rw [hdiv]
      exact ⟨q/2, by omega⟩
    · rfl
  simp [U, map_sub, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X_pow,
    h6, show 2*k+1 ≠ 2 by omega]

private theorem expand_R : PowerSeries.expand 2 (by decide) R = U := by
  ext n
  rcases n.even_or_odd with ⟨k,hk⟩ | ⟨k,hk⟩
  · have hn : n=2*k := by omega
    rw [hn]
    simp only [PowerSeries.coeff_expand_mul, R, PowerSeries.coeff_mk]
  · have hn : n=2*k+1 := by omega
    rw [hn]
    rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ (by omega), U_odd]

private theorem coeff_R_pow_zero (m n : ℕ) (hd : 2*m/3<n) (he : n<m) :
    PowerSeries.coeff n (R^m) = 0 := by
  have h := coeff_root_pow_eq_zero t t_cube t_zero m n hd he
  rw [← U_eq, ← expand_R, ← map_pow, PowerSeries.coeff_expand_mul] at h
  exact h

private theorem coeff_R (n : ℕ) :
    PowerSeries.coeff n R =
      (if n=0 then 1 else 0) + (if n=1 then 1 else 0) -
        PowerSeries.coeff (2*n) (t^6) := by
  simp only [R, PowerSeries.coeff_mk, U, map_sub, map_add, PowerSeries.coeff_one,
    PowerSeries.coeff_X_pow]
  simp only [show (2*n=0) ↔ n=0 by omega, show (2*n=2) ↔ n=1 by omega]

private theorem R_zero : PowerSeries.coeff 0 R = 1 := by
  rw [coeff_R]
  simp [PowerSeries.coeff_zero_eq_constantCoeff, t_zero]

private theorem R_one : PowerSeries.coeff 1 R = 1 := by
  rw [coeff_R, sixth_eq, PowerSeries.coeff_expand_of_not_dvd _ _ _ (by norm_num)]
  norm_num

private theorem R_two : PowerSeries.coeff 2 R = 0 := by
  rw [coeff_R, sixth_eq, PowerSeries.coeff_expand_of_not_dvd _ _ _ (by norm_num)]
  norm_num

private theorem R_trunc_three : PowerSeries.trunc 3 R = 1+Polynomial.X := by
  ext n
  rw [PowerSeries.coeff_trunc]
  by_cases hn : n<3
  · interval_cases n <;> norm_num [R_zero, R_one, R_two, Polynomial.coeff_one, Polynomial.coeff_X]
  · simp [hn, Polynomial.coeff_one, Polynomial.coeff_X,
      show n≠0 by omega, show 1≠n by omega]

private theorem R_source (n : ℕ) (hn : 1<n) :
    (n+1:F3)*PowerSeries.coeff n (R^(n+1)) =
      (n:F3)*PowerSeries.coeff n (R^(n+2)) := by
  by_cases hbig : 4<n
  · rw [coeff_R_pow_zero (n+1) n (by omega) (by omega),
      coeff_R_pow_zero (n+2) n (by omega) (by omega)]
    simp
  · have hsmall : n=2 ∨ n=3 ∨ n=4 := by omega
    rcases hsmall with rfl | rfl | rfl
    · have hc : PowerSeries.coeff 2 (R^4)=0 := by
        rw [coeff_pow_eq_coeff_trunc_pow, R_trunc_three]
        have hpoly : (1+Polynomial.X : F3[X])^4 =
            1+4*Polynomial.X+6*Polynomial.X^2+4*Polynomial.X^3+Polynomial.X^4 := by ring
        rw [hpoly]
        norm_num [Polynomial.coeff_add, Polynomial.coeff_mul, Polynomial.coeff_one, Polynomial.coeff_X]
        change (6:ZMod 3)=0
        decide
      norm_num [hc]
      left
      change (3:ZMod 3)=0
      decide
    · rw [coeff_R_pow_zero 4 3 (by omega) (by omega)]
      norm_num
      left
      change (3:ZMod 3)=0
      decide
    · have hc : PowerSeries.coeff 4 (R^6)=0 := by
        rw [show R^6 = (R^2)^3 by ring, cube_eq_expand,
          PowerSeries.coeff_expand_of_not_dvd _ _ _ (by norm_num)]
      rw [coeff_R_pow_zero 5 4 (by omega) (by omega), hc]
      simp

private theorem reduced_eq_R : reducedSeries = R :=
  source_unique reducedSeries R reduced_zero R_zero reduced_one R_one
    reduced_source_equation R_source


private theorem supports_disjoint (n : ℕ) (_hn : 1<n)
    (hp : ∃ r : ℕ, n=3^r) :
    ¬∃ i j : ℕ, i<j ∧ 2*n=3*(3^i+3^j) := by
  obtain ⟨r,hr⟩ := hp
  rintro ⟨i,j,hij,heq⟩
  cases r with
  | zero => simp at hr; omega
  | succ r =>
    rw [pow_succ] at hr
    have hs : (3:ℕ)^r+3^r = 3^i+3^j := by omega
    obtain ⟨hi,hj⟩ := power_pair_unique r r i j (by omega) (by omega) hs
    omega

private theorem coeff_R_high (n : ℕ) (hn : 1<n) :
    PowerSeries.coeff n R = -PowerSeries.coeff (2*n) (t^6) := by
  rw [coeff_R]
  simp [show n≠0 by omega, show n≠1 by omega]

private theorem R_power (n : ℕ) (hn : 1<n) (hp : ∃ r : ℕ, n=3^r) :
    PowerSeries.coeff n R = 2 := by
  rw [coeff_R_high n hn, sixth_eq]
  obtain ⟨r,hr⟩ := hp
  cases r with
  | zero => simp at hr; omega
  | succ r =>
    have he : 2*n = 3*(2*3^r) := by rw [pow_succ] at hr; omega
    rw [he, PowerSeries.coeff_expand_mul, coeff_square_diagonal]
    decide

private theorem R_pair (n : ℕ) (hn : 1<n)
    (hp : ∃ i j : ℕ, i<j ∧ 2*n=3*(3^i+3^j)) :
    PowerSeries.coeff n R = 1 := by
  rw [coeff_R_high n hn, sixth_eq]
  obtain ⟨i,j,hij,heq⟩ := hp
  rw [heq, PowerSeries.coeff_expand_mul, coeff_square_off_diagonal i j hij]
  decide

private theorem R_else (n : ℕ) (hn : 1<n)
    (hp : ¬∃ r : ℕ, n=3^r)
    (hq : ¬∃ i j : ℕ, i<j ∧ 2*n=3*(3^i+3^j)) :
    PowerSeries.coeff n R = 0 := by
  rw [coeff_R_high n hn, sixth_eq]
  suffices hz : PowerSeries.coeff (2*n) (PowerSeries.expand 3 (by decide) (t^2)) = 0 by
    rw [hz, neg_zero]
  by_cases hd : 3 ∣ 2*n
  · obtain ⟨k,hk⟩ := hd
    rw [hk, PowerSeries.coeff_expand_mul]
    apply coeff_square_else
    rintro ⟨i,j,hij⟩
    rcases lt_trichotomy i j with h | h | h
    · exact hq ⟨i,j,h,by omega⟩
    · subst j
      apply hp
      refine ⟨i+1,?_⟩
      rw [pow_succ]
      omega
    · exact hq ⟨j,i,h,by omega⟩
  · exact PowerSeries.coeff_expand_of_not_dvd _ _ _ hd

attribute [local instance] Classical.propDecidable

/-- The complete mod-three support of A396808 at every index greater than one. -/
theorem a396808_mod_three (n : ℕ) (hn : 1<n) :
    (a n : ZMod 3) =
      if ∃ r : ℕ, n=3^r then 2
      else if ∃ i j : ℕ, i<j ∧ 2*n=3*(3^i+3^j) then 1
      else 0 := by
  classical
  have hc : (a n : F3) = PowerSeries.coeff n R := by
    rw [← coeff_reducedSeries, reduced_eq_R]
  rw [hc]
  by_cases hq : ∃ i j : ℕ, i<j ∧ 2*n=3*(3^i+3^j)
  · have hp : ¬∃ r : ℕ, n=3^r := fun hp => supports_disjoint n hn hp hq
    rw [if_neg hp, if_pos hq]
    exact R_pair n hn hq
  · by_cases hp : ∃ r : ℕ, n=3^r
    · rw [if_pos hp]
      exact R_power n hn hp
    · rw [if_neg hp, if_neg hq]
      exact R_else n hn hp hq

#print axioms R_source
#print axioms a396808_mod_three
end
end D5.S3.Arith.TernaryTraceSupport
